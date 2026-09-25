package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The terms of Peano arithmetic as a **type**, their substitution by structural recursion, and the
 * first lemma proved about it.
 *
 * `Language` has the same five constructors as numbers: `NUM_TERM` holds of a code, tags `0` to
 * `4` are a variable, zero, the successor, addition and multiplication, and every function over a
 * code pays for a proof that the recursion is admissible, which that file says is most of it. This
 * development is the same syntax built by [[Datatype]]: `pterm` is a type with five constructors,
 * `PSUBST` is defined by the recursion theorem that builder derives, and its equations come out of
 * the definition rather than out of an admissibility argument. It exists to be what
 * `Datatype` is measured by: a builder that no consumer spends is machinery, not a type former.
 *
 * == It sits beside the chain ==
 *
 * The chain is the vocabulary every question about the reals and the naturals is typed in, and a
 * second syntax of arithmetic in that vocabulary would put a `PVAR` beside every `NUM_CODE` a
 * reader meets in `Find`. So `Ask`, `Find` and the library do not reach it, `docs/lemmas.md` does
 * not list it, and what builds it is [[Syntax.construct]] over the chain's widest signature, which
 * is `Fraction`'s arrangement.
 *
 * == What it does not do ==
 *
 * It does not relate itself to the coded syntax. That `NUM_SUBST_TERM` of the code of a term is
 * the code of `PSUBST` of it is a theorem this development makes statable and does not prove, and
 * it is the one that would let the object theory's arithmetic be read off a datatype rather than
 * off a number.
 */
final class Syntax private (
  val datatype: Datatype,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The equation defining `name`. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact, by name: the type's own, the equations of `PSUBST`, and the lemma. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).orElse(datatype.facts.get(name)).toRight(MissingDefinition(name))
}

object Syntax {

  /** The type of terms. */
  val TypeName: String = "pterm"

  val Variable: String = "PVAR"
  val Zero: String = "PZERO"
  val Successor: String = "PSUC"
  val Addition: String = "PADD"
  val Multiplication: String = "PMUL"

  /** `PSUBST i s t`: `s` put for the variable `i` everywhere in `t`. */
  val Substitution: String = "PSUBST"

  /** `|- !t i. PSUBST i (PVAR i) t = t`: putting a variable for itself changes nothing. */
  val SubstitutionOfItself: String = "PSUBST_SELF"

  private val Num: Type = TyApp(Natural.TypeName, Nil)

  /** The type, constructor by constructor, in the order `Language` numbers its tags. */
  val Specification: Datatype.Specification = Datatype.Specification(
    TypeName,
    List(
      Datatype.Constructor(Variable, List(Datatype.Argument.Of(Num))),
      Datatype.Constructor(Zero, Nil),
      Datatype.Constructor(Successor, List(Datatype.Argument.Recursive)),
      Datatype.Constructor(Addition, List(Datatype.Argument.Recursive, Datatype.Argument.Recursive)),
      Datatype.Constructor(Multiplication, List(Datatype.Argument.Recursive, Datatype.Argument.Recursive))
    )
  )

  /** The equations of `PSUBST`, one per constructor, with the names they are published under. */
  val SubstitutionEquations: Vector[(String, String)] = Vector(
    "PSUBST_PVAR" -> "!i:num. !s:pterm. !j:num. PSUBST i s (PVAR j) = COND (j = i) s (PVAR j)",
    "PSUBST_PZERO" -> "!i:num. !s:pterm. PSUBST i s PZERO = PZERO",
    "PSUBST_PSUC" -> "!i:num. !s:pterm. !t:pterm. PSUBST i s (PSUC t) = PSUC (PSUBST i s t)",
    "PSUBST_PADD" -> "!i:num. !s:pterm. !t:pterm. !u:pterm. PSUBST i s (PADD t u) = PADD (PSUBST i s t) (PSUBST i s u)",
    "PSUBST_PMUL" -> "!i:num. !s:pterm. !t:pterm. !u:pterm. PSUBST i s (PMUL t u) = PMUL (PSUBST i s t) (PSUBST i s u)"
  )

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] =
    SubstitutionEquations :+ (SubstitutionOfItself -> "!t:pterm. !i:num. PSUBST i (PVAR i) t = t")

  /** The development over the chain it is handed. */
  def construct(chain: Chain): Either[LogicError, Syntax] = {
    val ground = Datatype.Ground.of(chain)
    val base = chain.widest
    for {
      datatype <- Datatype.define(ground, base.theory, base.notation, Specification)
      substituted <- substitution(ground, datatype)
      (theory, equations) = substituted
      logic <- chain.classical.logic.over(theory)
      itself <- substitutionOfItself(chain, logic, theory, base.notation, datatype, equations)
      facts = SubstitutionEquations.map(_._1).zip(equations).toMap + (SubstitutionOfItself -> itself)
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(theory, base.notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Syntax(datatype, theory, base.notation, logic, datatype.definitions, facts)
  }

  /** The development over the standard chain. */
  lazy val standard: Syntax =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /** `PSUBST`, by the recursion theorem, with one clause per constructor over `i` and `s`. */
  private def substitution(ground: Datatype.Ground, datatype: Datatype): Either[LogicError, (Theory, List[Kernel.Thm])] = {
    val theory = datatype.theory
    val notation = datatype.notation
    def term(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
    for {
      clauses <- List(
        "\\j:num. COND (j = i:num) (s:pterm) (PVAR j)",
        "PZERO",
        "\\t:pterm. \\r:pterm. PSUC r",
        "\\t:pterm. \\u:pterm. \\r:pterm. \\q:pterm. PADD r q",
        "\\t:pterm. \\u:pterm. \\r:pterm. \\q:pterm. PMUL r q"
      ).foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, text) => acc.flatMap(list => term(text).map(list :+ _)))
      defined <- Datatype.defineRecursive(
        datatype,
        ground,
        theory,
        Substitution,
        List(Term.variable("i", Num), Term.variable("s", datatype.carrier)),
        clauses
      )
      (extended, _, equations) = defined
    } yield (extended, equations)
  }

  /**
   * [[SubstitutionOfItself]], by induction on the term. The one case with anything in it is a
   * variable, which is `j = i` or not, and the two branches of the conditional agree when it is.
   */
  private def substitutionOfItself(
    chain: Chain,
    logic: Logic,
    theory: Theory,
    notation: Notation,
    datatype: Datatype,
    equations: List[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    def term(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    val i = Term.variable("i", Num)
    val j = Term.variable("j", Num)
    val t = Term.variable("t", datatype.carrier)
    val u = Term.variable("u", datatype.carrier)
    val carrier = datatype.carrier

    /** `P x` folded back from its reduced form, where `P` is the induction predicate. */
    def folded(predicate: Term, argument: Term, proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        applied <- LogicError.lift(Term.app(predicate, argument))
        opened <- Conv.betaRoot(applied)
        back <- Conv.sym(opened)
        result <- LogicError.lift(Kernel.eqMp(back, proof))
      } yield result

    /** `P x` opened into its reduced form. */
    def unfolded(proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.betaRoot(proof.conclusion).flatMap(opened => LogicError.lift(Kernel.eqMp(opened, proof)))

    for {
      induction <- datatype.fact(Datatype.induction(TypeName))
      predicate <- term("\\t:pterm. PSUBST i (PVAR i) t = t")
      atPredicate <- rules.spec(predicate, induction)
      pvarI <- term("PVAR i")

      // PVAR j: COND (j = i) (PVAR i) (PVAR j) = PVAR j, by cases on j = i
      variableCase <- {
        for {
          atJ <- rules.specAll(equations(0), List(i, pvarI, j))
          same <- proposition("j:num = i:num")
          condTrue <- chain.classical.fact(Classical.CondTrue).map(Kernel.instType(Map(Classical.TypeVariable -> carrier), _))
          condFalse <- chain.classical.fact(Classical.CondFalse).map(Kernel.instType(Map(Classical.TypeVariable -> carrier), _))
          pvarJ <- term("PVAR j")
          equal <- LogicError.lift(Kernel.assume(same))
          whenEqual <- for {
            chosen <- rules.specAll(condTrue, List(same, pvarI, pvarJ)).flatMap(rules.mp(_, equal))
            // PVAR i = PVAR j, from j = i
            back <- Conv.sym(equal)
            pvar <- datatype.constructor(Variable)
            carried <- Conv.apTerm(pvar, back)
            result <- Conv.trans(atJ, chosen).flatMap(Conv.trans(_, carried))
          } yield result
          different <- logic.mkNot(same)
          apart <- LogicError.lift(Kernel.assume(different))
          whenDifferent <- rules
            .specAll(condFalse, List(same, pvarI, pvarJ))
            .flatMap(rules.mp(_, apart))
            .flatMap(Conv.trans(atJ, _))
          both <- chain.classical.cases(same, whenEqual, whenDifferent)
          result <- folded(predicate, pvarJ, both).flatMap(rules.gen(j, _))
        } yield result
      }

      zeroCase <- {
        for {
          atZero <- rules.specAll(equations(1), List(i, pvarI))
          pzero <- term("PZERO")
          result <- folded(predicate, pzero, atZero)
        } yield result
      }

      successorCase <- {
        for {
          hypothesis <- LogicError.lift(Term.app(predicate, t)).flatMap(held => LogicError.lift(Kernel.assume(held)))
          induced <- unfolded(hypothesis)
          atT <- rules.specAll(equations(2), List(i, pvarI, t))
          psuc <- datatype.constructor(Successor)
          carried <- Conv.apTerm(psuc, induced)
          joined <- Conv.trans(atT, carried)
          applied <- term("PSUC t")
          result <- folded(predicate, applied, joined)
            .flatMap(rules.disch(hypothesis.conclusion, _))
            .flatMap(rules.gen(t, _))
        } yield result
      }

      binary = (index: Int, name: String) =>
        for {
          left <- LogicError.lift(Term.app(predicate, t)).flatMap(held => LogicError.lift(Kernel.assume(held)))
          right <- LogicError.lift(Term.app(predicate, u)).flatMap(held => LogicError.lift(Kernel.assume(held)))
          leftInduced <- unfolded(left)
          rightInduced <- unfolded(right)
          atTU <- rules.specAll(equations(index), List(i, pvarI, t, u))
          constructor <- datatype.constructor(name)
          carried <- Conv.apTerm(constructor, leftInduced)
            .flatMap(partial => LogicError.lift(Kernel.mkComb(partial, rightInduced)))
          joined <- Conv.trans(atTU, carried)
          applied <- LogicError.lift(Term.appAll(constructor, List(t, u)))
          result <- folded(predicate, applied, joined)
            .flatMap(rules.disch(right.conclusion, _))
            .flatMap(rules.disch(left.conclusion, _))
            .flatMap(rules.genAll(_, List(t, u)))
        } yield result

      additionCase <- binary(3, Addition)
      multiplicationCase <- binary(4, Multiplication)

      together <- List(variableCase, zeroCase, successorCase, additionCase)
        .foldRight[Either[LogicError, Kernel.Thm]](Right(multiplicationCase))((part, acc) =>
          acc.flatMap(rules.conjIntro(part, _)))
      everywhere <- rules.mp(atPredicate, together)
      atT <- rules.spec(t, everywhere)
      opened <- unfolded(atT)
      result <- rules.genAll(opened, List(t, i))
    } yield result
  }
}
