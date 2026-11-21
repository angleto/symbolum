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
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

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
   * `|- !e t. NUM_TERM t ==> NUM_CLOSED t ==> NUM_PROV (t = numeral (NUM_VALUE t e))`
   *
   * PA computes every closed term: it proves the term equal to the numeral of its value. This is
   * the first place truth and provability meet, and it is the term half of completeness for
   * bounded formulas: `NUM_PROV_NUMERAL_ADD` and `NUM_PROV_NUMERAL_MUL` settle a sum and a product
   * of two NUMERALS, and this carries them to any closed term by course-of-values induction on its
   * code, replacing each operand by its numeral with the congruences `Deduction` publishes.
   *
   * A variable is the case that does not arise, and the induction says so rather than assuming
   * it: a code of a variable is not closed, since the variable is free in it.
   */
  val ProvesValue: String = "NUM_PROV_VALUE"

  /**
   * `|- !e a b. ... ==> NUM_TRUE (a = b) e ==> NUM_PROV (a = b)`, for closed terms `a` and `b`.
   *
   * A true closed equation is provable, which is completeness for the atomic formulas that hold.
   * Both sides are proved equal to the numeral of one value and the two proofs are joined.
   * [[ProvesFalseEquation]] is the other half of the atomic case.
   */
  val ProvesTrueEquation: String = "NUM_PROV_TRUE_EQ"

  /**
   * `|- !e a b. ... ==> NUM_TRUE ~(a = b) e ==> NUM_PROV ~(a = b)`, for closed terms `a` and `b`.
   *
   * A false closed equation has a provable negation, the half of the atomic case that needs PA to
   * tell numbers apart. Each side is proved equal to the numeral of its value, as for a true
   * equation; the two values differ, so `NUM_PROV_NUMERAL_DISTINCT` denies the equation between
   * the numerals, and `NUM_PROV_NOT_EQ_CONG` carries the denial back onto `a` and `b`. With
   * [[ProvesTrueEquation]] it says that PA decides every closed equation, which is completeness for
   * the atomic formulas and their negations. The connectives are [[ProvesGround]], and the bounded
   * quantifiers are the next step.
   */
  val ProvesFalseEquation: String = "NUM_PROV_FALSE_EQ"

  /**
   * `NUM_GROUND p` says `p` codes a formula with no quantifier whose terms are all closed: the
   * formulas completeness is proved for first, and the ones whose truth does not depend on the
   * environment.
   */
  val GroundName: String = "NUM_GROUND"

  /** `|- !a b. NUM_GROUND (a = b) = (NUM_CLOSED a /\ NUM_CLOSED b)`, coded. */
  val GroundEquality: String = "NUM_GROUND_EQ"

  /** `|- !p. NUM_GROUND ~p = NUM_GROUND p`, coded. */
  val GroundNegation: String = "NUM_GROUND_NOT"

  /** `|- !p q. NUM_GROUND (p ==> q) = (NUM_GROUND p /\ NUM_GROUND q)`, coded. */
  val GroundImplication: String = "NUM_GROUND_IMP"

  /** `|- !j p. NUM_GROUND (!v_j. p) = F`, coded: a quantifier is what this class leaves out. */
  val GroundUniversal: String = "NUM_GROUND_ALL"

  /**
   * `|- !e p. NUM_FORM p ==> NUM_GROUND p ==>
   *        (NUM_TRUE p e ==> NUM_PROV p) /\ (~NUM_TRUE p e ==> NUM_PROV ~p)`
   *
   * PA decides every closed formula without a quantifier: it proves the true ones and refutes the
   * false ones. By strong induction on the code, with one case per connective. An equation is
   * [[ProvesTrueEquation]] or [[ProvesFalseEquation]]. A negation is the hypothesis at its body,
   * with `Deduction`'s double negation for the false one. An implication is `NUM_PROV_WEAKEN`
   * when its consequent holds, `NUM_PROV_IMP_DENIED` when its antecedent fails, and
   * `NUM_PROV_NOT_IMP` when it is false. The quantifier is the case `NUM_GROUND` rules out, and the
   * bounded ones are the next step.
   */
  val ProvesGround: String = "NUM_PROV_GROUND"

  /**
   * `|- !x k t. NUM_TERM t ==> !e. NUM_VALUE (t[numeral k/x]) e = NUM_VALUE t e[x := k]`
   *
   * Putting the numeral of `k` for `v_x` in a term changes its value exactly as sending `x` to
   * `k` in the environment does, where `e[x := k]` is `\j. COND (j = x) k (e j)`. By strong
   * induction on the code: a variable is the one case that reads the update, by whether it is
   * `v_x`, and the rest are the clauses of the substitution and of the value pushed through.
   */
  val ValueAtNumeral: String = "NUM_VALUE_SUBST_NUMERAL"

  /**
   * `|- !x k p. NUM_FORM p ==> !e. NUM_TRUE (p[numeral k/x]) e = NUM_TRUE p e[x := k]`
   *
   * The same for a formula, which is what lets a fact about every instance `p[numeral k/x]` be
   * read as a fact about `p` at every value of `x`: bounded completeness needs it at each bounded
   * quantifier. By strong induction on the code, with the induction hypothesis at every
   * environment. An equation is [[ValueAtNumeral]] at both sides. At a universal over `v_j` the
   * environment moves under the quantifier: when `j` is `x` the substitution stops and the update
   * at `x` is overwritten by the quantifier's own, and otherwise the hypothesis is taken at the
   * quantifier's environment and the two updates commute, since they are at different indices.
   * Both are equalities between environments that are abstractions, by a case split on the
   * argument under the abstraction, so `ETA` is not spent. No condition on `x` is needed: a numeral is closed, so nothing it is put under can
   * capture it.
   */
  val TrueAtNumeral: String = "NUM_TRUE_SUBST_NUMERAL"

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
    TriangleGraphTrue -> "!e:num -> num. NUM_TRUE NUM_TRI_GRAPH e = (e 0 = NUM_TRI (e 1))",
    ProvesValue ->
      ("!e:num -> num. !t:num. NUM_TERM t ==> NUM_CLOSED t ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR t (NUM_NUMERAL (NUM_VALUE t e))))"),
    ProvesTrueEquation ->
      ("!e:num -> num. !a:num. !b:num. NUM_TERM a ==> NUM_CLOSED a ==> " +
        "NUM_TERM b ==> NUM_CLOSED b ==> NUM_TRUE (NUM_CODE 5 (NUM_PAIR a b)) e ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR a b))"),
    ProvesFalseEquation ->
      ("!e:num -> num. !a:num. !b:num. NUM_TERM a ==> NUM_CLOSED a ==> " +
        "NUM_TERM b ==> NUM_CLOSED b ==> NUM_TRUE (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR a b))) e ==> " +
        "NUM_PROV (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR a b)))"),
    GroundEquality -> "!a:num. !b:num. NUM_GROUND (NUM_CODE 5 (NUM_PAIR a b)) = (NUM_CLOSED a /\\ NUM_CLOSED b)",
    GroundNegation -> "!p:num. NUM_GROUND (NUM_CODE 6 p) = NUM_GROUND p",
    GroundImplication -> "!p:num. !q:num. NUM_GROUND (NUM_CODE 7 (NUM_PAIR p q)) = (NUM_GROUND p /\\ NUM_GROUND q)",
    GroundUniversal -> "!j:num. !p:num. NUM_GROUND (NUM_CODE 8 (NUM_PAIR j p)) = F",
    ProvesGround ->
      ("!e:num -> num. !p:num. NUM_FORM p ==> NUM_GROUND p ==> " +
        "(NUM_TRUE p e ==> NUM_PROV p) /\\ (~(NUM_TRUE p e) ==> NUM_PROV (NUM_CODE 6 p))"),
    ValueAtNumeral ->
      ("!x:num k:num t:num. NUM_TERM t ==> !e:num -> num. " +
        "NUM_VALUE (NUM_SUBST_TERM x (NUM_NUMERAL k) t) e = NUM_VALUE t (\\j:num. COND (j = x) k (e j))"),
    TrueAtNumeral ->
      ("!x:num k:num p:num. NUM_FORM p ==> !e:num -> num. " +
        "NUM_TRUE (NUM_SUBST_FORM x (NUM_NUMERAL k) p) e = NUM_TRUE p (\\j:num. COND (j = x) k (e j))")
  )

  /** The step of the ground predicate, as text, with the guards the truth's step has. */
  val GroundStepText: String =
    "\\f:num -> bool. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "     (NUM_CLOSED (NUM_FST (NUM_PAYLOAD s)) /\\ NUM_CLOSED (NUM_SND (NUM_PAYLOAD s))) " +
      "     (COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) " +
      "           (f (NUM_PAYLOAD s)) " +
      "           (COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (f (NUM_FST (NUM_PAYLOAD s)) /\\ f (NUM_SND (NUM_PAYLOAD s))) " +
      "                 F))"

  /** The one the standard chain builds. */
  lazy val standard: Truth = Chain.standard.truth

  /**
   * Over what the embedded theory can prove, extending its theory.
   *
   * A link of the chain, above `provability`, so that completeness can state that a true formula
   * is a provable one in one signature, and so that `Find` and the library reach what is here.
   */
  def construct(
    language: Language,
    numbering: Numbering,
    provability: Provability,
    deduction: Deduction,
    induct: Induct,
    successor: Successor,
    naturals: Natural
  ): Either[LogicError, Truth] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val environments = Type.fun(numbers, numbers)

    for {
      descent <- Descent.construct(numbering.peano, induct)
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

      withGround <- Language.defineShaped(
        numbering, recursion, truthTheory, provability.notation, truthLogic,
        GroundName, GroundStepText, Type.Bool, Nil)
      (groundTheory, groundDefinition, groundNamed) = withGround

      graphBody <- Parser.term(groundTheory, provability.notation, TriangleGraphText, numbers)
      withGraph <- LogicError.lift(Kernel.defineConstant(groundTheory, TriangleGraphName, graphBody))
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
      clauses = new Clauses(numbering, logic, successor, projections, statements)

      valueVariable <- clauses.at(valueNamed, ValueVariable, Type.fun(environments, numbers))
      valueZero <- clauses.at(valueNamed, ValueZero, Type.fun(environments, numbers))
      valueSuccessor <- clauses.at(valueNamed, ValueSuccessor, Type.fun(environments, numbers))
      valueSum <- clauses.at(valueNamed, ValueSum, Type.fun(environments, numbers))
      valueProduct <- clauses.at(valueNamed, ValueProduct, Type.fun(environments, numbers))
      numeralAtZero <- language.fact(Language.NumeralAtZero)
      numeralAtSuccessor <- language.fact(Language.NumeralAtSuccessor)
      valueNumeral <- numeralValue(
        logic, statements, naturals, numeralAtZero, numeralAtSuccessor, valueZero,
        valueSuccessor)

      trueEquality <- clauses.at(truthNamed, TrueEquality, Type.fun(environments, Type.Bool))
      trueNegation <- clauses.at(truthNamed, TrueNegation, Type.fun(environments, Type.Bool))
      trueImplication <- clauses.at(truthNamed, TrueImplication, Type.fun(environments, Type.Bool))
      trueUniversal <- clauses.at(truthNamed, TrueUniversal, Type.fun(environments, Type.Bool))
      groundEquality <- clauses.plain(groundNamed, GroundEquality)
      groundNegation <- clauses.plain(groundNamed, GroundNegation)
      groundImplication <- clauses.plain(groundNamed, GroundImplication)
      groundUniversal <- clauses.plain(groundNamed, GroundUniversal)
      modusPonens <- provability.fact(Provability.ModusPonens)
      doubleNegation <- naturals.classical.fact(Classical.DoubleNegation)

      semiring <- Semiring.construct(numbering.peano)
      doubled <- triangleDoubled(logic, statements, naturals, numbering, semiring)
      graph <- triangleGraph(
        logic, statements, numbering, graphDefinition, doubled,
        Vector(valueVariable, valueSuccessor, valueSum, valueProduct, trueEquality))

      evaluation <- Evaluation.of(
        logic, theory, provability.notation, language, numbering, deduction, statements,
        valueZero, valueSuccessor, valueSum, valueProduct, trueEquality, trueNegation,
        Grounding(trueImplication, groundEquality, groundNegation, groundImplication, groundUniversal,
          modusPonens, doubleNegation, naturals.classical, valueVariable, valueNumeral, trueUniversal))
    } yield new Truth(
      language,
      theory,
      provability.notation,
      logic,
      Map(
        ValueName -> valueDefinition,
        TrueName -> truthDefinition,
        GroundName -> groundDefinition,
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
        TriangleGraphTrue -> graph,
        ProvesValue -> evaluation._1,
        ProvesTrueEquation -> evaluation._2,
        ProvesFalseEquation -> evaluation._3,
        GroundEquality -> groundEquality,
        GroundNegation -> groundNegation,
        GroundImplication -> groundImplication,
        GroundUniversal -> groundUniversal,
        ProvesGround -> evaluation._4,
        ValueAtNumeral -> evaluation._5,
        TrueAtNumeral -> evaluation._6
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

    /** A clause of a recursion that answers with a truth value and reads no environment. */
    def plain(named: Kernel.Thm, name: String): Either[LogicError, Kernel.Thm] =
      for {
        statement <- statements.statement(name)
        stripped <- Logic.stripForall(statement)
        (variables, body) = stripped
        sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
        code <- sides._1 match {
          case App(_, coded) => Right(coded)
          case other => Left(NotOfForm("a predicate read at a code", other))
        }
        instance <- rules.spec(code, named)
        cleaned <- Rewrite.inTheorem(projections, instance)
        settled <- Language.settleGuards(numbering, logic, successor, Type.Bool, cleaned)
        reduced <- Conv
          .betaNormalise(settled.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, settled)))
        general <- rules.genAll(reduced, variables.toList)
        result <- statements.checked(name, general)
      } yield result

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

  /** Carry a refusal out of a derivation written in direct style. */
  private final class RefusedHere(val error: LogicError) extends RuntimeException

  /**
   * [[ProvesValue]] and [[ProvesTrueEquation]], written in direct style the way `Deduction`'s
   * derivations are, because the induction below is five cases deep and each is a dozen steps.
   */
  /** What the ground completeness reads beyond the evaluation's own facts. */
  private final case class Grounding(
    trueImplication: Kernel.Thm,
    groundEquality: Kernel.Thm,
    groundNegation: Kernel.Thm,
    groundImplication: Kernel.Thm,
    groundUniversal: Kernel.Thm,
    modusPonens: Kernel.Thm,
    doubleNegation: Kernel.Thm,
    classical: Classical,
    valueVariable: Kernel.Thm,
    valueNumeral: Kernel.Thm,
    trueUniversal: Kernel.Thm
  )

  private object Evaluation {

    def of(
      logic: Logic,
      theory: Theory,
      notation: Notation,
      language: Language,
      numbering: Numbering,
      deduction: Deduction,
      statements: Statements,
      valueZero: Kernel.Thm,
      valueSuccessor: Kernel.Thm,
      valueSum: Kernel.Thm,
      valueProduct: Kernel.Thm,
      trueEquality: Kernel.Thm,
      trueNegation: Kernel.Thm,
      grounding: Grounding
    ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm)] =
      try {
        val built = new Evaluation(
          logic, theory, notation, language, numbering, deduction,
          valueZero, valueSuccessor, valueSum, valueProduct, trueEquality, trueNegation)
        for {
          value <- statements.checked(ProvesValue, built.provesValue)
          equation <- statements.checked(ProvesTrueEquation, built.provesTrueEquation(value))
          denial <- statements.checked(ProvesFalseEquation, built.provesFalseEquation(value))
          ground <- statements.checked(ProvesGround, built.provesGround(equation, denial, grounding))
          valueAt <- statements.checked(ValueAtNumeral, built.valueAtNumeral(grounding))
          truthAt <- statements.checked(TrueAtNumeral, built.trueAtNumeral(grounding, valueAt))
        } yield (value, equation, denial, ground, valueAt, truthAt)
      } catch { case refused: RefusedHere => Left(refused.error) }
  }

  private final class Evaluation(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    language: Language,
    numbering: Numbering,
    deduction: Deduction,
    valueZero: Kernel.Thm,
    valueSuccessor: Kernel.Thm,
    valueSum: Kernel.Thm,
    valueProduct: Kernel.Thm,
    trueEquality: Kernel.Thm,
    trueNegation: Kernel.Thm
  ) {
    private val rules = logic.rules
    private val numbers = TyApp(Natural.TypeName, Nil)
    private val environments = Type.fun(numbers, numbers)
    private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
    private val property = Type.fun(numbers, Type.Bool)

    private def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)
    private def constant(name: String, ty: Type): Term =
      force(LogicError.lift(theory.constant(name, ty)))
    private def applied(head: Term, arguments: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, arguments)))
    private def assumed(claim: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(claim)))
    private def languageFact(name: String): Kernel.Thm = force(language.fact(name))
    private def deductionFact(name: String): Kernel.Thm = force(deduction.fact(name))
    private def imp(left: Term, right: Term): Term = force(logic.mkImp(left, right))

    /** Specialise, then detach each premise in order. */
    private def apply(theorem: Kernel.Thm, arguments: List[Term], premises: Kernel.Thm*)
      : Kernel.Thm =
      premises.foldLeft(force(rules.specAll(theorem, arguments)))((carried, premise) =>
        force(rules.mp(carried, premise)))

    private val coding = constant(Numbering.CodeName, arithmetic)
    private val pairing = constant(Numbering.PairName, arithmetic)
    private val numeralOf = constant(Language.NumeralName, Type.fun(numbers, numbers))
    private val value = constant(ValueName, Type.fun(numbers, Type.fun(environments, numbers)))
    private val truth = constant(TrueName, Type.fun(numbers, Type.fun(environments, Type.Bool)))
    private val termPredicate = constant(Language.TermName, property)
    private val closedPredicate = constant(Language.ClosedName, property)
    private val provablePredicate = constant(Provability.ProvableName, property)
    private val free = constant(Language.FreeName, Type.fun(numbers, property))
    private val below = constant(Peano.StrictOrder, Type.fun(numbers, property))
    private val tags: Vector[Term] =
      (0 to 8).toVector.map(k => force(Parser.term(theory, notation, k.toString, numbers)))

    private def code(tag: Int, payload: Term): Term = applied(coding, List(tags(tag), payload))
    private def pair(left: Term, right: Term): Term = applied(pairing, List(left, right))
    private def equation(left: Term, right: Term): Term = code(5, pair(left, right))
    private def numeral(of: Term): Term = applied(numeralOf, List(of))
    private def isTerm(subject: Term): Term = applied(termPredicate, List(subject))
    private def isClosed(subject: Term): Term = applied(closedPredicate, List(subject))
    private def provable(subject: Term): Term = applied(provablePredicate, List(subject))

    private val environment = Term.variable("e", environments)
    private def valueOf(subject: Term): Term = applied(value, List(subject, environment))

    /** What the induction proves at `t`: PA equates it with the numeral of its value. */
    private def goal(subject: Term): Term = provable(equation(subject, numeral(valueOf(subject))))
    private def claim(subject: Term): Term =
      imp(isTerm(subject), imp(isClosed(subject), goal(subject)))

    private def sides(theorem: Kernel.Thm): (Term, Term) =
      Term.destEq(theorem.conclusion).getOrElse(
        throw new RefusedHere(NotOfForm("an equation", theorem.conclusion)))

    /** `template(a)` to `template(b)` along `a = b`, by one abstraction and its congruence. */
    private def moved(template: Term => Term, along: Kernel.Thm, theorem: Kernel.Thm)
      : Kernel.Thm = {
      val (from, to) = sides(along)
      val taken = Term.freeVariables(template(from)) ++ Term.freeVariables(template(to)) ++
        Term.freeVariables(along.conclusion)
      val hole = Conv.freshVariable("x", Term.typeOf(from), taken)
      val context = force(LogicError.lift(Term.abs(hole, template(hole))))
      val congruence = force(Conv.apTerm(context, along).flatMap(Conv.betaSides))
      force(LogicError.lift(Kernel.eqMp(congruence, theorem)))
    }

    /** An existential opened at a fresh witness, the case proved, and the witness discharged. */
    private def opened(existential: Kernel.Thm, name: String, avoid: Set[FVar])(
      proceed: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic
        .destExistsPredicate(existential.conclusion)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential.conclusion)))
      val witness = Conv.freshVariable(
        name, numbers, avoid ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .betaReduce(applied(predicate, List(witness)))
        .getOrElse(throw new RefusedHere(NotOfForm("an abstraction", predicate)))
      force(rules.existsElim(existential, witness, proceed(witness, assumed(body))))
    }

    /** `NUM_CODE k a = NUM_CODE k' a'` from `k = k'` and `a = a'`. */
    private def codeCongruence(tagEquation: Kernel.Thm, payloadEquation: Kernel.Thm): Kernel.Thm =
      force(Conv.apTerm(coding, tagEquation).flatMap(half =>
        LogicError.lift(Kernel.mkComb(half, payloadEquation))))

    /** `NUM_PAIR u v = NUM_PAIR u v`, spelled so a caller can pass it where an equation goes. */
    private def refl(term: Term): Kernel.Thm = Conv.refl(term)

    private val closedCases = languageFact(Language.ClosedCases)

    /**
     * `NUM_CLOSED part` from `NUM_CLOSED whole`, through the freeness clause of `whole`.
     *
     * `clause` is that clause at an index `k`, `NUM_FREE_TERM k whole = <something>`, and
     * `inject` turns `NUM_FREE_TERM k part` into its right side: the identity for a successor and
     * a disjunction introduced for a sum or a product.
     */
    private def closedPart(
      wholeIsClosed: Kernel.Thm, whole: Term, part: Term,
      clause: Term => Kernel.Thm, inject: (Term, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val index = Conv.freshVariable(
        "k", numbers,
        Term.freeVariables(whole) ++ wholeIsClosed.hypotheses.flatMap(Term.freeVariables))
      val nowhere = force(
        rules
          .spec(whole, closedCases)
          .flatMap(unfolded => LogicError.lift(Kernel.eqMp(unfolded, wholeIsClosed)))
          .flatMap(rules.spec(index, _)))
      val freeInPart = applied(free, List(index, part))
      val inWhole = force(
        Conv.sym(clause(index)).flatMap(reversed =>
          LogicError.lift(Kernel.eqMp(reversed, inject(index, assumed(freeInPart))))))
      val denied = force(
        rules
          .notElim(nowhere, inWhole)
          .flatMap(rules.notIntro(freeInPart, _))
          .flatMap(rules.gen(index, _)))
      force(
        rules
          .spec(part, closedCases)
          .flatMap(Conv.sym)
          .flatMap(folded => LogicError.lift(Kernel.eqMp(folded, denied))))
    }

    /** `part < whole` for a component of a code, as the constructor's bound gives it. */
    private def belowCode(tag: Int, payload: Term): Kernel.Thm =
      apply(force(numbering.fact(Numbering.CodeRight)), List(tags(tag), payload))

    private def belowPair(tag: Int, left: Term, right: Term, first: Boolean): Kernel.Thm = {
      val component = if (first) left else right
      val atMost = apply(
        force(numbering.fact(if (first) Numbering.PairLeft else Numbering.PairRight)),
        List(left, right))
      val inCode = belowCode(tag, pair(left, right))
      apply(
        force(numbering.peano.fact(Peano.AtMostThenBelow)),
        List(component, pair(left, right), code(tag, pair(left, right))),
        force(rules.conjIntro(atMost, inCode)))
    }

    private val numeralIsTerm = languageFact(Language.NumeralIsTerm)
    private val numeralIsClosed = languageFact(Language.NumeralIsClosed)
    private def numeralTerm(of: Term): Kernel.Thm = force(rules.spec(of, numeralIsTerm))
    private def numeralClosed(of: Term): Kernel.Thm = force(rules.spec(of, numeralIsClosed))

    /** From `PROV (s = r')` and `r = r'`, `PROV (s = r)`. */
    private def answered(subject: Term, rewritten: Kernel.Thm, proved: Kernel.Thm): Kernel.Thm =
      moved(x => provable(equation(subject, x)), force(Conv.sym(rewritten)), proved)

    lazy val provesValue: Kernel.Thm = {
      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claim(y))))
      val instance = force(
        rules
          .spec(predicate, strong)
          .flatMap(theorem =>
            Conv.betaNormalise(theorem.conclusion)
              .flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))

      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claim(z))))
      val earlier = assumed(hypothesis)
      val yIsTerm = assumed(isTerm(y))
      val yIsClosed = assumed(isClosed(y))

      /** The claim at a component, given that it is below `y`, a term and closed. */
      def atComponent(
        part: Term, isBelow: Kernel.Thm, partIsTerm: Kernel.Thm, partIsClosed: Kernel.Thm
      ): Kernel.Thm =
        force(
          rules
            .spec(part, earlier)
            .flatMap(rules.mp(_, isBelow))
            .flatMap(rules.mp(_, partIsTerm))
            .flatMap(rules.mp(_, partIsClosed)))

      val cases = force(
        rules.spec(y, languageFact(Language.TermCases)).flatMap(unfolded =>
          LogicError.lift(Kernel.eqMp(unfolded, yIsTerm))))
      val taken = Set(y, z, environment)

      val reached = opened(cases, "a", taken) { (a, withTag) =>
        opened(withTag, "b", taken + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          val split = logic.destDisj(alternatives.conclusion)
            .getOrElse(throw new RefusedHere(
              NotOfForm("the four shapes of a term", alternatives.conclusion)))

          /** The claim at the shape a case has pinned, carried back from it to `y`. */
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(goal, force(Conv.sym(yIsShape)), atShape)
          def closedAt(yIsShape: Kernel.Thm): Kernel.Thm = moved(isClosed, yIsShape, yIsClosed)
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(x => applied(below, List(part, x)), force(Conv.sym(yIsShape)), isBelowShape)

          // A variable: not closed, since the variable is free in it.
          val asVariable = {
            val tagIsZero = assumed(split._1)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIsZero, refl(b))))
            val shapeIsClosed = closedAt(yIsShape)
            val nowhere = force(
              rules
                .spec(code(0, b), closedCases)
                .flatMap(unfolded => LogicError.lift(Kernel.eqMp(unfolded, shapeIsClosed)))
                .flatMap(rules.spec(b, _)))
            val clause = apply(languageFact(Language.FreeVariable), List(b, b))
            val there = force(
              Conv.sym(clause).flatMap(reversed =>
                LogicError.lift(Kernel.eqMp(reversed, Kernel.refl(b)))))
            force(rules.notElim(nowhere, there).flatMap(rules.falsityElim(goal(y), _)))
          }

          val rest = logic.destDisj(split._2)
            .getOrElse(throw new RefusedHere(NotOfForm("three shapes", split._2)))

          // Zero: the numeral of zero is the code of zero, so the claim is reflexivity.
          val asZero = {
            val held = assumed(rest._1)
            val tagIsOne = force(rules.conjElim1(held))
            val payloadIsZero = force(rules.conjElim2(held))
            val shape = code(1, tags(0))
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIsOne, payloadIsZero)))
            val reflexive = apply(
              deductionFact(Deduction.Reflexivity), List(shape),
              languageFact(Language.TermZero))
            val computed = force(
              rules.spec(environment, valueZero)
                .flatMap(Conv.apTerm(numeralOf, _))
                .flatMap(Conv.trans(_, languageFact(Language.NumeralAtZero))))
            back(answered(shape, computed, reflexive), yIsShape)
          }

          val last = logic.destDisj(rest._2)
            .getOrElse(throw new RefusedHere(NotOfForm("two shapes", rest._2)))

          // A successor: the claim at the argument, carried under the successor's congruence.
          val asSuccessor = {
            val held = assumed(last._1)
            val tagIsTwo = force(rules.conjElim1(held))
            val bIsTerm = force(rules.conjElim2(held))
            val shape = code(2, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIsTwo, refl(b))))
            val bIsClosed = closedPart(
              closedAt(yIsShape), shape, b,
              k => apply(languageFact(Language.FreeSuccessor), List(k, b)),
              (_, freeInB) => freeInB)
            val atB = atComponent(b, belowY(belowCode(2, b), b, yIsShape), bIsTerm, bIsClosed)
            val numeralOfB = numeral(valueOf(b))
            val carried = apply(
              deductionFact(Deduction.SuccessorCongruence), List(b, numeralOfB),
              bIsTerm, numeralTerm(valueOf(b)), bIsClosed, numeralClosed(valueOf(b)), atB)
            val computed = force(
              rules.specAll(valueSuccessor, List(environment, b))
                .flatMap(Conv.apTerm(numeralOf, _))
                .flatMap(Conv.trans(_, force(
                  rules.spec(valueOf(b), languageFact(Language.NumeralAtSuccessor))))))
            back(answered(shape, computed, carried), yIsShape)
          }

          // A sum or a product: each operand by its numeral, one congruence at a time, and the
          // two numerals by the object theory's own arithmetic.
          val asBinary = {
            val held = assumed(last._2)
            val whichTag = force(rules.conjElim1(held))
            val decomposed = force(rules.conjElim2(held))
            opened(decomposed, "u", taken + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken + a + b + u) { (v, parts) =>
                val payloadIsPair = force(rules.conjElim1(parts))
                val components = force(rules.conjElim2(parts))
                val uIsTerm = force(rules.conjElim1(components))
                val vIsTerm = force(rules.conjElim2(components))
                val tagCases = logic.destDisj(whichTag.conclusion)
                  .getOrElse(throw new RefusedHere(
                    NotOfForm("a sum or a product", whichTag.conclusion)))

                def binary(tag: Int, tagEquation: Kernel.Thm): Kernel.Thm = {
                  val isSum = tag == 3
                  val shape = code(tag, pair(u, v))
                  val yIsShape =
                    force(Conv.trans(yIsCode, codeCongruence(tagEquation, payloadIsPair)))
                  val shapeIsClosed = closedAt(yIsShape)
                  val freeClause =
                    languageFact(if (isSum) Language.FreeSum else Language.FreeProduct)
                  val uIsClosed = closedPart(
                    shapeIsClosed, shape, u, k => apply(freeClause, List(k, u, v)),
                    (k, freeInU) => force(rules.disjIntro1(applied(free, List(k, v)), freeInU)))
                  val vIsClosed = closedPart(
                    shapeIsClosed, shape, v, k => apply(freeClause, List(k, u, v)),
                    (k, freeInV) => force(rules.disjIntro2(applied(free, List(k, u)), freeInV)))
                  val atU = atComponent(
                    u, belowY(belowPair(tag, u, v, first = true), u, yIsShape), uIsTerm, uIsClosed)
                  val atV = atComponent(
                    v, belowY(belowPair(tag, u, v, first = false), v, yIsShape), vIsTerm, vIsClosed)

                  val nu = numeral(valueOf(u))
                  val nv = numeral(valueOf(v))
                  val nuTerm = numeralTerm(valueOf(u))
                  val nuClosed = numeralClosed(valueOf(u))
                  val nvTerm = numeralTerm(valueOf(v))
                  val nvClosed = numeralClosed(valueOf(v))
                  def op(left: Term, right: Term): Term = code(tag, pair(left, right))
                  val opIsTerm = languageFact(if (isSum) Language.TermSum else Language.TermProduct)
                  val opIsClosed =
                    languageFact(if (isSum) Language.ClosedSum else Language.ClosedProduct)
                  def opTerm(l: Term, r: Term, lt: Kernel.Thm, rt: Kernel.Thm): Kernel.Thm =
                    apply(opIsTerm, List(l, r), lt, rt)
                  def opClosed(l: Term, r: Term, lc: Kernel.Thm, rc: Kernel.Thm): Kernel.Thm =
                    apply(opIsClosed, List(l, r), lc, rc)

                  val leftReplaced = apply(
                    deductionFact(
                      if (isSum) Deduction.SumCongruence else Deduction.ProductCongruence),
                    List(u, nu, v), uIsTerm, uIsClosed, nuTerm, nuClosed, vIsTerm, vIsClosed, atU)
                  val rightReplaced = apply(
                    deductionFact(
                      if (isSum) Deduction.SumCongruenceRight
                      else Deduction.ProductCongruenceRight),
                    List(v, nv, nu), vIsTerm, vIsClosed, nvTerm, nvClosed, nuTerm, nuClosed, atV)
                  val onNumerals = apply(
                    deductionFact(
                      if (isSum) Deduction.NumeralAddition else Deduction.NumeralMultiplication),
                    List(valueOf(u), valueOf(v)))
                  val total = sides(apply(
                    if (isSum) valueSum else valueProduct, List(environment, u, v)))._2
                  val nt = numeral(total)

                  val transitivity = deductionFact(Deduction.Transitivity)
                  val first = op(u, v)
                  val second = op(nu, v)
                  val third = op(nu, nv)
                  val firstTerm = opTerm(u, v, uIsTerm, vIsTerm)
                  val secondTerm = opTerm(nu, v, nuTerm, vIsTerm)
                  val thirdTerm = opTerm(nu, nv, nuTerm, nvTerm)
                  val firstClosed = opClosed(u, v, uIsClosed, vIsClosed)
                  val secondClosed = opClosed(nu, v, nuClosed, vIsClosed)
                  val thirdClosed = opClosed(nu, nv, nuClosed, nvClosed)
                  val twoSteps = apply(
                    transitivity, List(first, second, third),
                    firstTerm, secondTerm, thirdTerm, firstClosed, secondClosed, thirdClosed,
                    leftReplaced, rightReplaced)
                  val allThree = apply(
                    transitivity, List(first, third, nt),
                    firstTerm, thirdTerm, numeralTerm(total), firstClosed, thirdClosed,
                    numeralClosed(total), twoSteps, onNumerals)

                  val computed = force(
                    rules.specAll(if (isSum) valueSum else valueProduct, List(environment, u, v))
                      .flatMap(Conv.apTerm(numeralOf, _)))
                  back(answered(shape, computed, allThree), yIsShape)
                }

                force(rules.disjElim(
                  whichTag,
                  binary(3, assumed(tagCases._1)),
                  binary(4, assumed(tagCases._2))))
              }
            }
          }

          force(rules.disjElim(
            alternatives, asVariable,
            force(rules.disjElim(assumed(split._2), asZero,
              force(rules.disjElim(assumed(rest._2), asSuccessor, asBinary))))))
        }
      }

      val step = force(
        rules
          .disch(isClosed(y), reached)
          .flatMap(rules.disch(isTerm(y), _))
          .flatMap(rules.disch(hypothesis, _))
          .flatMap(rules.gen(y, _)))
      force(rules.mp(instance, step).flatMap(rules.gen(environment, _)))
    }

    /** [[ProvesTrueEquation]], from [[ProvesValue]] at both sides. */
    /** [[ProvesGround]], by strong induction on the code and one case per connective. */
    def provesGround(trueEq: Kernel.Thm, falseEq: Kernel.Thm, g: Grounding): Kernel.Thm = {
      val groundPredicate = constant(GroundName, property)
      val formPredicate = constant(Language.FormulaName, property)
      def ground(subject: Term): Term = applied(groundPredicate, List(subject))
      def isForm(subject: Term): Term = applied(formPredicate, List(subject))
      def truthAt(subject: Term): Term = applied(truth, List(subject, environment))
      def neg(subject: Term): Term = code(6, subject)
      def not(t: Term): Term = force(logic.mkNot(t))
      def both(l: Term, r: Term): Term = force(logic.mkConj(l, r))
      def decided(subject: Term): Term =
        both(imp(truthAt(subject), provable(subject)), imp(not(truthAt(subject)), provable(neg(subject))))
      def claimG(subject: Term): Term = imp(isForm(subject), imp(ground(subject), decided(subject)))

      /** `PROV q` from `PROV (p ==> q)` and `PROV p`. */
      def detach(p: Term, q: Term, implication: Kernel.Thm, antecedent: Kernel.Thm): Kernel.Thm =
        apply(g.modusPonens, List(p, q), implication, antecedent)
      /** `NUM_TRUE x e = <clause>` read forwards or backwards. */
      def through(clause: Kernel.Thm, held: Kernel.Thm): Kernel.Thm = force(LogicError.lift(Kernel.eqMp(clause, held)))
      def backwards(clause: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
        force(Conv.sym(clause).flatMap(c => LogicError.lift(Kernel.eqMp(c, held))))
      def cases(p: Term)(yes: Kernel.Thm => Kernel.Thm, no: Kernel.Thm => Kernel.Thm): Kernel.Thm =
        force(g.classical.cases(p, yes(assumed(p)), no(assumed(not(p)))))
      def absurd(goal: Term, contradiction: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(goal, contradiction))
      def decidedFrom(subject: Term, whenTrue: Kernel.Thm => Kernel.Thm, whenFalse: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
        val t = truthAt(subject)
        val a = force(rules.disch(t, whenTrue(assumed(t))))
        val b = force(rules.disch(not(t), whenFalse(assumed(not(t)))))
        force(rules.conjIntro(a, b))
      }

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimG(y))))
      val instance = force(
        rules.spec(predicate, strong).flatMap(theorem =>
          Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimG(z))))
      val earlier = assumed(hypothesis)
      val yIsForm = assumed(isForm(y))
      val yIsGround = assumed(ground(y))

      def atComponent(part: Term, isBelow: Kernel.Thm, partIsForm: Kernel.Thm, partIsGround: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsForm))
          .flatMap(rules.mp(_, partIsGround)))

      val shapes = force(rules.spec(y, languageFact(Language.FormulaCases)).flatMap(unfolded =>
        LogicError.lift(Kernel.eqMp(unfolded, yIsForm))))
      val taken = Set(y, z, environment)

      val reached = opened(shapes, "a", taken) { (a, withTag) =>
        opened(withTag, "b", taken + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(template: Term => Term, atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(template, force(Conv.sym(yIsShape)), atShape)
          def forth(template: Term => Term, atY: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(template, yIsShape, atY)
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(x => applied(below, List(part, x)), force(Conv.sym(yIsShape)), isBelowShape)

          val (equality, rest1) = logic.destDisj(alternatives.conclusion).getOrElse(
            throw new RefusedHere(NotOfForm("the four shapes of a formula", alternatives.conclusion)))
          val (negation, rest2) = logic.destDisj(rest1).getOrElse(throw new RefusedHere(NotOfForm("three shapes", rest1)))
          val (implication, universal) = logic.destDisj(rest2).getOrElse(throw new RefusedHere(NotOfForm("two shapes", rest2)))

          // an equation between closed terms: the atomic case, already proved both ways
          val asEquality = {
            val held = assumed(equality)
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken + a + b + u) { (v, parts) =>
                val payloadIs = force(rules.conjElim1(parts))
                val terms = force(rules.conjElim2(parts))
                val uIsTerm = force(rules.conjElim1(terms))
                val vIsTerm = force(rules.conjElim2(terms))
                val shape = code(5, pair(u, v))
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, payloadIs)))
                val closedBoth = through(apply(g.groundEquality, List(u, v)), forth(ground, yIsGround, yIsShape))
                val uIsClosed = force(rules.conjElim1(closedBoth))
                val vIsClosed = force(rules.conjElim2(closedBoth))
                val atShape = decidedFrom(shape,
                  holds => apply(trueEq, List(environment, u, v), uIsTerm, uIsClosed, vIsTerm, vIsClosed, holds),
                  fails => {
                    val negated = backwards(apply(trueNegation, List(environment, shape)), fails)
                    apply(falseEq, List(environment, u, v), uIsTerm, uIsClosed, vIsTerm, vIsClosed, negated)
                  })
                back(decided, atShape, yIsShape)
              }
            }
          }

          // a negation: the hypothesis at the body, and the double negation for the false one
          val asNegation = {
            val held = assumed(negation)
            val tagIs = force(rules.conjElim1(held))
            val bodyIsForm = force(rules.conjElim2(held))
            val shape = neg(b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, refl(b))))
            val bodyIsGround = through(apply(g.groundNegation, List(b)), forth(ground, yIsGround, yIsShape))
            val atBody = atComponent(b, belowY(belowCode(6, b), b, yIsShape), bodyIsForm, bodyIsGround)
            val bodyTrue = force(rules.conjElim1(atBody))
            val bodyFalse = force(rules.conjElim2(atBody))
            val atShape = decidedFrom(shape,
              holds => force(rules.mp(bodyFalse, through(apply(trueNegation, List(environment, b)), holds))),
              fails => {
                val notNot = through(force(Conv.apTerm(constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)),
                  apply(trueNegation, List(environment, b)))), fails)
                val bodyHolds = force(rules.spec(truthAt(b), g.doubleNegation).flatMap(rules.mp(_, notNot)))
                val provedBody = force(rules.mp(bodyTrue, bodyHolds))
                val introduce = apply(deductionFact(Deduction.DoubleNegationIntroduction), List(b), bodyIsForm)
                detach(b, neg(neg(b)), introduce, provedBody)
              })
            back(decided, atShape, yIsShape)
          }

          // an implication: weakening, ex falso, or its refutation, by the truth of the two sides
          val asImplication = {
            val held = assumed(implication)
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken + a + b + u) { (v, parts) =>
                val payloadIs = force(rules.conjElim1(parts))
                val forms = force(rules.conjElim2(parts))
                val uIsForm = force(rules.conjElim1(forms))
                val vIsForm = force(rules.conjElim2(forms))
                val shape = code(7, pair(u, v))
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, payloadIs)))
                val grounds = through(apply(g.groundImplication, List(u, v)), forth(ground, yIsGround, yIsShape))
                val atU = atComponent(u, belowY(belowPair(7, u, v, first = true), u, yIsShape), uIsForm, force(rules.conjElim1(grounds)))
                val atV = atComponent(v, belowY(belowPair(7, u, v, first = false), v, yIsShape), vIsForm, force(rules.conjElim2(grounds)))
                val clause = apply(g.trueImplication, List(environment, u, v))
                val tu = truthAt(u)
                val tv = truthAt(v)
                val atShape = decidedFrom(shape,
                  holds => {
                    val arrow = through(clause, holds)
                    cases(tv)(
                      vHolds => apply(deductionFact(Deduction.Weaken), List(u, v), uIsForm, vIsForm,
                        force(rules.mp(force(rules.conjElim1(atV)), vHolds))),
                      vFails => cases(tu)(
                        uHolds => absurd(provable(shape), force(rules.notElim(vFails, force(rules.mp(arrow, uHolds))))),
                        uFails => apply(deductionFact(Deduction.ImplicationOfDenial), List(u, v), uIsForm, vIsForm,
                          force(rules.mp(force(rules.conjElim2(atU)), uFails)))
                      )
                    )
                  },
                  fails => {
                    val notArrow = through(force(Conv.apTerm(constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)), clause)), fails)
                    // ~(tu ==> tv) gives tu and ~tv
                    val uHolds = cases(tu)(
                      yes => yes,
                      no => absurd(tu, force(rules.notElim(notArrow,
                        force(rules.disch(tu, absurd(tv, force(rules.notElim(no, assumed(tu))))))))))
                    val vFails = cases(tv)(
                      yes => absurd(not(tv), force(rules.notElim(notArrow, force(rules.disch(tu, yes))))),
                      no => no)
                    apply(deductionFact(Deduction.DeniedImplication), List(u, v), uIsForm, vIsForm,
                      force(rules.mp(force(rules.conjElim1(atU)), uHolds)),
                      force(rules.mp(force(rules.conjElim2(atV)), vFails)))
                  })
                back(decided, atShape, yIsShape)
              }
            }
          }

          // a quantifier: not ground, so nothing to prove
          val asUniversal = {
            val held = assumed(universal)
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken + a + b + u) { (v, parts) =>
                val payloadIs = force(rules.conjElim1(parts))
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, payloadIs)))
                val nothing = through(apply(g.groundUniversal, List(u, v)), forth(ground, yIsGround, yIsShape))
                absurd(decided(y), nothing)
              }
            }
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(
        rules.disch(ground(y), reached).flatMap(rules.disch(isForm(y), _))
          .flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val everywhere = force(rules.mp(instance, step))
      val p = Term.variable("p", numbers)
      force(rules.spec(p, everywhere).flatMap(rules.gen(p, _)).flatMap(rules.gen(environment, _)))
    }

    def provesTrueEquation(provesValue: Kernel.Thm): Kernel.Thm = {
      val a = Term.variable("a", numbers)
      val b = Term.variable("b", numbers)
      val aIsTerm = assumed(isTerm(a))
      val aIsClosed = assumed(isClosed(a))
      val bIsTerm = assumed(isTerm(b))
      val bIsClosed = assumed(isClosed(b))
      val holds = applied(truth, List(equation(a, b), environment))
      val sameValue = force(
        rules.specAll(trueEquality, List(environment, a, b)).flatMap(unfolded =>
          LogicError.lift(Kernel.eqMp(unfolded, assumed(holds)))))

      val atA = apply(provesValue, List(environment, a), aIsTerm, aIsClosed)
      val atB = apply(provesValue, List(environment, b), bIsTerm, bIsClosed)
      // `b` equals the numeral of ITS value, which is `a`'s value: the same numeral.
      val atBByA = moved(x => provable(equation(b, numeral(x))), force(Conv.sym(sameValue)), atB)
      val shared = numeral(valueOf(a))
      val sharedTerm = numeralTerm(valueOf(a))
      val sharedClosed = numeralClosed(valueOf(a))
      val reversed = apply(
        deductionFact(Deduction.Symmetry), List(b, shared),
        bIsTerm, sharedTerm, bIsClosed, sharedClosed, atBByA)
      val joined = apply(
        deductionFact(Deduction.Transitivity), List(a, shared, b),
        aIsTerm, sharedTerm, bIsTerm, aIsClosed, sharedClosed, bIsClosed, atA, reversed)

      force(
        rules
          .disch(holds, joined)
          .flatMap(rules.disch(isClosed(b), _))
          .flatMap(rules.disch(isTerm(b), _))
          .flatMap(rules.disch(isClosed(a), _))
          .flatMap(rules.disch(isTerm(a), _))
          .flatMap(rules.genAll(_, List(environment, a, b))))
    }

    /** [[ProvesFalseEquation]]: both sides to their numerals, the numerals apart, carried back. */
    def provesFalseEquation(provesValue: Kernel.Thm): Kernel.Thm = {
      val a = Term.variable("a", numbers)
      val b = Term.variable("b", numbers)
      val aIsTerm = assumed(isTerm(a))
      val aIsClosed = assumed(isClosed(a))
      val bIsTerm = assumed(isTerm(b))
      val bIsClosed = assumed(isClosed(b))
      val denied = code(6, equation(a, b))
      val fails = applied(truth, List(denied, environment))
      val apart = force(
        for {
          negation <- rules.specAll(trueNegation, List(environment, equation(a, b)))
          unfolded <- LogicError.lift(Kernel.eqMp(negation, assumed(fails)))
          equality <- rules.specAll(trueEquality, List(environment, a, b))
          moved <- Conv.apTerm(constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)), equality)
          result <- LogicError.lift(Kernel.eqMp(moved, unfolded))
        } yield result)

      val atA = apply(provesValue, List(environment, a), aIsTerm, aIsClosed)
      val atB = apply(provesValue, List(environment, b), bIsTerm, bIsClosed)
      val (va, vb) = (valueOf(a), valueOf(b))
      val numerals = apply(deductionFact(Deduction.NumeralsDistinct), List(va, vb), apart)
      val carried = apply(
        deductionFact(Deduction.DeniedCongruence), List(a, b, numeral(va), numeral(vb)),
        aIsTerm, bIsTerm, numeralTerm(va), numeralTerm(vb),
        aIsClosed, bIsClosed, numeralClosed(va), numeralClosed(vb),
        atA, atB, numerals)

      force(
        rules
          .disch(fails, carried)
          .flatMap(rules.disch(isClosed(b), _))
          .flatMap(rules.disch(isTerm(b), _))
          .flatMap(rules.disch(isClosed(a), _))
          .flatMap(rules.disch(isTerm(a), _))
          .flatMap(rules.genAll(_, List(environment, a, b))))
    }

    /* ------------------------------------------- a numeral put for a variable, read by the truth */

    private def equal(left: Term, right: Term): Term = force(LogicError.lift(Term.eq(left, right)))
    private def denial(t: Term): Term = force(logic.mkNot(t))
    private val conditional =
      constant(Classical.Conditional, Type.fun(Type.Bool, Type.fun(numbers, Type.fun(numbers, numbers))))
    private def cond(guard: Term, yes: Term, no: Term): Term = applied(conditional, List(guard, yes, no))

    /** `\j. COND (j = index) to (env j)`: `env` with `index` sent to `to`. */
    private def updated(env: Term, index: Term, to: Term): Term = {
      val j = Conv.freshVariable(
        "j", numbers, Term.freeVariables(env) ++ Term.freeVariables(index) ++ Term.freeVariables(to))
      force(LogicError.lift(Term.abs(j, cond(equal(j, index), to, applied(env, List(j))))))
    }

    /** `l = r` from `l = c` and `r = c`. */
    private def same(left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
      force(Conv.sym(right).flatMap(Conv.trans(left, _)))
    private def chained(steps: Kernel.Thm*): Kernel.Thm =
      steps.reduceLeft((carried, next) => force(Conv.trans(carried, next)))

    /**
     * `term = normal`, by the equations given and beta, which every one of them strictly unfolds:
     * a clause of the substitution, of the value or of the truth, or an induction hypothesis at a
     * smaller code, none of whose right sides holds its own left side.
     */
    private def unfolded(equations: Vector[Kernel.Thm], term: Term): Kernel.Thm =
      force(Rewrite.Rule.all(logic, equations).flatMap(Rewrite.rewrite(_, term)))

    /** Both sides of `goal` unfolded by the same equations, and required to meet. */
    private def met(equations: Vector[Kernel.Thm], goal: Term): Kernel.Thm = {
      val (left, right) = Term.destEq(goal).getOrElse(throw new RefusedHere(NotOfForm("an equation", goal)))
      val joined = same(unfolded(equations, left), unfolded(equations, right))
      if (joined.conclusion == goal) joined else throw new RefusedHere(NotOfForm("the goal", joined.conclusion))
    }

    private final class Conditions(g: Grounding) {
      private val atNumbers = Map(Classical.TypeVariable -> numbers)
      private val condTrue = Kernel.instType(atNumbers, force(g.classical.fact(Classical.CondTrue)))
      private val condFalse = Kernel.instType(atNumbers, force(g.classical.fact(Classical.CondFalse)))

      /** `COND p a b = a` from `p`. */
      def taken(guard: Kernel.Thm, a: Term, b: Term): Kernel.Thm =
        apply(condTrue, List(guard.conclusion, a, b), guard)

      /** `COND p a b = b` from `~p`. */
      def passed(denied: Kernel.Thm, a: Term, b: Term): Kernel.Thm = {
        val guard = logic.destNot(denied.conclusion)
          .getOrElse(throw new RefusedHere(NotOfForm("a negation", denied.conclusion)))
        apply(condFalse, List(guard, a, b), denied)
      }

      def split(p: Term)(yes: Kernel.Thm => Kernel.Thm, no: Kernel.Thm => Kernel.Thm): Kernel.Thm =
        force(g.classical.cases(p, yes(assumed(p)), no(assumed(denial(p)))))

      /**
       * `f = h` between two environments that are both abstractions, from their bodies at a fresh
       * `m`. `pointwise` is handed `m` and proves the two bodies' beta-normal forms equal, and the
       * kernel's abstraction rule closes it. Extensionality is not used, and with it `ETA` is not
       * spent: an abstraction on both sides is what makes the bodies enough.
       */
      def extensional(f: Term, h: Term, avoid: Set[FVar])(pointwise: FVar => Kernel.Thm): Kernel.Thm = {
        val m = Conv.freshVariable("m", numbers, avoid ++ Term.freeVariables(f) ++ Term.freeVariables(h))
        def body(function: Term): Term = sides(force(Conv.betaRoot(applied(function, List(m)))))._2
        val (atF, atH) = (body(f), body(h))
        val point = chained(force(Conv.betaNormalise(atF)), pointwise(m), force(Conv.sym(force(Conv.betaNormalise(atH)))))
        val joined = force(LogicError.lift(Kernel.abs(m, point)))
        if (joined.conclusion == equal(f, h)) joined
        else throw new RefusedHere(NotOfForm("the two environments equal", joined.conclusion))
      }
    }

    private val substituting = constant(Language.SubstituteName, Type.fun(numbers, arithmetic))
    private val formulaSubstituting = constant(Language.FormulaSubstituteName, Type.fun(numbers, arithmetic))
    private val formPredicate = constant(Language.FormulaName, property)

    /** [[ValueAtNumeral]], by strong induction on the code, one case per shape of a term. */
    def valueAtNumeral(g: Grounding): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val nk = numeral(k)
      def substituted(s: Term): Term = applied(substituting, List(x, nk, s))
      def claimed(s: Term): Term =
        equal(applied(value, List(substituted(s), environment)), applied(value, List(s, updated(environment, x, k))))
      def everywhere(s: Term): Term = force(logic.mkForall(environment, claimed(s)))
      def claimAt(s: Term): Term = imp(isTerm(s), everywhere(s))

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimAt(y))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimAt(z))))
      val earlier = assumed(hypothesis)
      val yIsTerm = assumed(isTerm(y))
      def atComponent(part: Term, isBelow: Kernel.Thm, partIsTerm: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsTerm))
          .flatMap(rules.spec(environment, _)))

      val shapes = force(rules.spec(y, languageFact(Language.TermCases)).flatMap(unfolding =>
        LogicError.lift(Kernel.eqMp(unfolding, yIsTerm))))
      val taken0 = Set(y, z, environment, x, k)
      val substituteVariable = languageFact(Language.SubstituteVariable)
      val substituteZero = languageFact(Language.SubstituteZero)
      val substituteSuccessor = languageFact(Language.SubstituteSuccessor)
      val substituteSum = languageFact(Language.SubstituteSum)
      val substituteProduct = languageFact(Language.SubstituteProduct)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(everywhere, force(Conv.sym(yIsShape)), force(rules.gen(environment, atShape)))
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          val (variableCase, rest1) = logic.destDisj(alternatives.conclusion)
            .getOrElse(throw new RefusedHere(NotOfForm("the four shapes of a term", alternatives.conclusion)))
          val (zeroCase, rest2) = logic.destDisj(rest1).getOrElse(throw new RefusedHere(NotOfForm("three shapes", rest1)))
          val (successorCase, binaryCase) =
            logic.destDisj(rest2).getOrElse(throw new RefusedHere(NotOfForm("two shapes", rest2)))

          // A variable: the one case that reads the update, by whether it is v_x.
          val asVariable = {
            val tagIsZero = assumed(variableCase)
            val shape = code(0, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIsZero, refl(b))))
            val substitution = apply(substituteVariable, List(x, nk, b)) // = COND (b = x) nk (v_b)
            val update = updated(environment, x, k)
            val read = chained(
              apply(g.valueVariable, List(update, b)),
              force(Conv.betaNormalise(applied(update, List(b))))) // VALUE v_b e' = COND (b = x) k (e b)
            def valueThrough(equation: Kernel.Thm): Kernel.Thm =
              force(Conv.apTerm(value, equation).flatMap(Conv.apThm(_, environment)))
            val atShape = split(equal(b, x))(
              isX => same(
                chained(valueThrough(chained(substitution, taken(isX, nk, shape))),
                  apply(g.valueNumeral, List(environment, k))),
                chained(read, taken(isX, k, applied(environment, List(b))))),
              notX => same(
                chained(valueThrough(chained(substitution, passed(notX, nk, shape))),
                  apply(g.valueVariable, List(environment, b))),
                chained(read, passed(notX, k, applied(environment, List(b))))))
            back(atShape, yIsShape)
          }

          // Zero: the substitution leaves it and both values are zero.
          val asZero = {
            val held = assumed(zeroCase)
            val shape = code(1, tags(0))
            val yIsShape = force(Conv.trans(yIsCode,
              codeCongruence(force(rules.conjElim1(held)), force(rules.conjElim2(held)))))
            back(met(Vector(substituteZero, valueZero), claimed(shape)), yIsShape)
          }

          // A successor: the hypothesis at the argument, under the two clauses.
          val asSuccessor = {
            val held = assumed(successorCase)
            val bIsTerm = force(rules.conjElim2(held))
            val shape = code(2, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held)), refl(b))))
            val atB = atComponent(b, belowY(belowCode(2, b), b, yIsShape), bIsTerm)
            back(met(Vector(substituteSuccessor, valueSuccessor, atB), claimed(shape)), yIsShape)
          }

          // A sum or a product: the hypothesis at both operands.
          val asBinary = {
            val held = assumed(binaryCase)
            val whichTag = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, parts) =>
                val payloadIsPair = force(rules.conjElim1(parts))
                val components = force(rules.conjElim2(parts))
                val (sumTag, productTag) = logic.destDisj(whichTag.conclusion)
                  .getOrElse(throw new RefusedHere(NotOfForm("a sum or a product", whichTag.conclusion)))
                def binary(tag: Int, tagEquation: Kernel.Thm): Kernel.Thm = {
                  val shape = code(tag, pair(u, v))
                  val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagEquation, payloadIsPair)))
                  val atU = atComponent(u, belowY(belowPair(tag, u, v, first = true), u, yIsShape),
                    force(rules.conjElim1(components)))
                  val atV = atComponent(v, belowY(belowPair(tag, u, v, first = false), v, yIsShape),
                    force(rules.conjElim2(components)))
                  val clauses =
                    if (tag == 3) Vector(substituteSum, valueSum) else Vector(substituteProduct, valueProduct)
                  back(met(clauses ++ Vector(atU, atV), claimed(shape)), yIsShape)
                }
                force(rules.disjElim(whichTag, binary(3, assumed(sumTag)), binary(4, assumed(productTag))))
              }
            }
          }

          force(rules.disjElim(alternatives, asVariable,
            force(rules.disjElim(assumed(rest1), asZero,
              force(rules.disjElim(assumed(rest2), asSuccessor, asBinary))))))
        }
      }

      val step = force(rules.disch(isTerm(y), reached).flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val t = Term.variable("t", numbers)
      force(rules.mp(instance, step).flatMap(rules.spec(t, _)).flatMap(rules.genAll(_, List(x, k, t))))
    }

    /** [[TrueAtNumeral]], by strong induction on the code, one case per shape of a formula. */
    def trueAtNumeral(g: Grounding, valueAt: Kernel.Thm): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val nk = numeral(k)
      def isForm(s: Term): Term = applied(formPredicate, List(s))
      def substituted(s: Term): Term = applied(formulaSubstituting, List(x, nk, s))
      def truthAt(s: Term, env: Term): Term = applied(truth, List(s, env))
      def equationAt(s: Term, env: Term): Term = equal(truthAt(substituted(s), env), truthAt(s, updated(env, x, k)))
      def everywhere(s: Term): Term = force(logic.mkForall(environment, equationAt(s, environment)))
      def claimAt(s: Term): Term = imp(isForm(s), everywhere(s))
      def termAt(s: Term, sIsTerm: Kernel.Thm): Kernel.Thm =
        force(rules.specAll(valueAt, List(x, k, s)).flatMap(rules.mp(_, sIsTerm)).flatMap(rules.spec(environment, _)))

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimAt(y))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimAt(z))))
      val earlier = assumed(hypothesis)
      val yIsForm = assumed(isForm(y))
      def atComponent(part: Term, isBelow: Kernel.Thm, partIsForm: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsForm)))

      val shapes = force(rules.spec(y, languageFact(Language.FormulaCases)).flatMap(unfolding =>
        LogicError.lift(Kernel.eqMp(unfolding, yIsForm))))
      val taken0 = Set(y, z, environment, x, k)
      val universals = force(logic.universalAt(numbers))

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(everywhere, force(Conv.sym(yIsShape)), force(rules.gen(environment, atShape)))
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          val (equalityCase, rest1) = logic.destDisj(alternatives.conclusion)
            .getOrElse(throw new RefusedHere(NotOfForm("the four shapes of a formula", alternatives.conclusion)))
          val (negationCase, rest2) = logic.destDisj(rest1).getOrElse(throw new RefusedHere(NotOfForm("three shapes", rest1)))
          val (implicationCase, universalCase) =
            logic.destDisj(rest2).getOrElse(throw new RefusedHere(NotOfForm("two shapes", rest2)))
          def pairCase(held: Kernel.Thm)(proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, parts) =>
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, force(rules.conjElim1(parts)))))
                proceed(u, v, yIsShape, force(rules.conjElim2(parts)))
              }
            }
          }

          // An equation: the value lemma at both sides.
          val asEquality = pairCase(assumed(equalityCase)) { (u, v, yIsShape, terms) =>
            val shape = code(5, pair(u, v))
            val atU = termAt(u, force(rules.conjElim1(terms)))
            val atV = termAt(v, force(rules.conjElim2(terms)))
            back(met(Vector(languageFact(Language.FormulaSubstituteEquality), trueEquality, atU, atV),
              equationAt(shape, environment)), yIsShape)
          }

          // A negation: the hypothesis at its body.
          val asNegation = {
            val held = assumed(negationCase)
            val shape = code(6, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held)), refl(b))))
            val atB = force(rules.spec(environment,
              atComponent(b, belowY(belowCode(6, b), b, yIsShape), force(rules.conjElim2(held)))))
            back(met(Vector(languageFact(Language.FormulaSubstituteNegation), trueNegation, atB),
              equationAt(shape, environment)), yIsShape)
          }

          // An implication: the hypothesis at both sides.
          val asImplication = pairCase(assumed(implicationCase)) { (u, v, yIsShape, forms) =>
            val shape = code(7, pair(u, v))
            val atU = force(rules.spec(environment,
              atComponent(u, belowY(belowPair(7, u, v, first = true), u, yIsShape), force(rules.conjElim1(forms)))))
            val atV = force(rules.spec(environment,
              atComponent(v, belowY(belowPair(7, u, v, first = false), v, yIsShape), force(rules.conjElim2(forms)))))
            back(met(Vector(languageFact(Language.FormulaSubstituteImplication), g.trueImplication, atU, atV),
              equationAt(shape, environment)), yIsShape)
          }

          // A universal over v_u: the environment moves under the quantifier.
          val asUniversal = pairCase(assumed(universalCase)) { (u, v, yIsShape, vIsForm) =>
            val shape = code(8, pair(u, v))
            val n = Conv.freshVariable("n", numbers, taken0 + a + b + u + v)
            val update = updated(environment, x, k) // e'
            def bound(env: Term): Term = updated(env, u, n) // env[u := n]
            def underQuantifier(bodyEquation: Kernel.Thm): Kernel.Thm =
              force(LogicError.lift(Kernel.abs(n, bodyEquation)).flatMap(Conv.apTerm(universals, _)))
            def truthThrough(s: Term, envEquation: Kernel.Thm): Kernel.Thm =
              force(Conv.apTerm(applied(truth, List(s)), envEquation))
            val atUpdate = apply(g.trueUniversal, List(update, u, v)) // TRUE (!v_u. v) e' = !n. TRUE v e'[u := n]
            val substitution = apply(languageFact(Language.FormulaSubstituteUniversal), List(x, nk, u, v))
            def truthOfSubstituted(equation: Kernel.Thm): Kernel.Thm =
              force(Conv.apTerm(truth, equation).flatMap(Conv.apThm(_, environment)))
            val atShape = split(equal(u, x))(
              isX => {
                // The substitution stops, and e'[u := n] is e[u := n], since u is x.
                val stopped = chained(substitution, taken(isX, shape, code(8, pair(u, substituted(v)))))
                val sameEnvironment = extensional(bound(environment), bound(update), taken0 + a + b + u + v + n) { m =>
                  val em = applied(environment, List(m))
                  split(equal(m, u))(
                    isU => same(taken(isU, n, em), taken(isU, n, cond(equal(m, x), k, em))),
                    notU => {
                      val notXm = force(rules.notIntro(equal(m, x), force(rules.notElim(notU,
                        force(Conv.sym(isX).flatMap(Conv.trans(assumed(equal(m, x)), _)))))))
                      same(passed(notU, n, em),
                        chained(passed(notU, n, cond(equal(m, x), k, em)), passed(notXm, k, em)))
                    })
                }
                val left = chained(truthOfSubstituted(stopped), apply(g.trueUniversal, List(environment, u, v)),
                  underQuantifier(truthThrough(v, sameEnvironment)))
                same(left, atUpdate)
              },
              notX => {
                // The substitution goes under, and the two updates commute, being at u and at x.
                val under = chained(substitution, passed(notX, shape, code(8, pair(u, substituted(v)))))
                val hypothesisAt = force(rules.spec(bound(environment),
                  atComponent(v, belowY(belowPair(8, u, v, first = false), v, yIsShape), vIsForm)))
                val commuted = extensional(updated(bound(environment), x, k), bound(update),
                  taken0 + a + b + u + v + n) { m =>
                  val em = applied(environment, List(m))
                  split(equal(m, x))(
                    isX => {
                      val notU = force(rules.notIntro(equal(m, u), force(rules.notElim(notX,
                        force(Conv.sym(assumed(equal(m, u))).flatMap(Conv.trans(_, isX)))))))
                      same(taken(isX, k, cond(equal(m, u), n, em)),
                        chained(passed(notU, n, cond(equal(m, x), k, em)), taken(isX, k, em)))
                    },
                    notXm => {
                      val inner = passed(notXm, k, em) // COND (m = x) k (e m) = e m
                      val rightSide = force(Conv.apTerm(applied(conditional, List(equal(m, u), n)), inner))
                      same(passed(notXm, k, cond(equal(m, u), n, em)), rightSide)
                    })
                }
                val body = chained(hypothesisAt, truthThrough(v, commuted))
                val left = chained(truthOfSubstituted(under), apply(g.trueUniversal, List(environment, u, substituted(v))),
                  underQuantifier(body))
                same(left, atUpdate)
              })
            back(atShape, yIsShape)
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(rules.disch(isForm(y), reached).flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val p = Term.variable("p", numbers)
      force(rules.mp(instance, step).flatMap(rules.spec(p, _)).flatMap(rules.genAll(_, List(x, k, p))))
    }
  }
}
