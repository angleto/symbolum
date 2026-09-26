package garden.xeno.symbolum.theories

import org.scalatest.Assertions
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The moves a test uses to meet the hypotheses of a theorem about resolution at a concrete
 * refutation, and the refutation written as data.
 *
 * Shared by `PigeonholeSpec` and `ExpanderPigeonholeSpec`, whose non-vacuity guards both detach a
 * lower bound at a refutation nobody assumed. The refutation's three functions are free variables
 * `k`, `v`, `s` while the hypotheses are derived, with one equation per value the argument reads;
 * [[ResolutionFixture.Refutation.close]] then puts the functions in, written as conditionals, and
 * proves every one of those equations by deciding its conditional, so nothing is left assumed.
 */
final class ResolutionFixture(val moves: Pigeonhole.Builder, chain: Chain, show: Term => String) extends Assertions {

  private val Num = TyApp(Natural.TypeName, Nil)

  def ok[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  def numeral(value: Int): String = if (value == 0) "ZERO" else s"(SUC ${numeral(value - 1)})"

  def implication(term: Term): (Term, Term) =
    moves.logic.destImp(term).getOrElse(fail(s"an implication: ${show(term)}"))

  /** The antecedents and the conclusion of `a1 ==> ... ==> an ==> c`, `count` of them. */
  def antecedents(term: Term, count: Int): (List[Term], Term) =
    if (count == 0) (Nil, term)
    else {
      val (first, rest) = implication(term)
      val (more, conclusion) = antecedents(rest, count - 1)
      (first :: more, conclusion)
    }

  /** The body of `?x1 ... xn. body` or `!x. body` at the given witnesses, root-contracted. */
  def opened(quantified: Term, witnesses: String*): Term =
    witnesses.foldLeft(quantified) { (current, text) =>
      val predicate = moves.logic.destExistsPredicate(current)
        .orElse(moves.logic.destForallPredicate(current)).getOrElse(fail("a quantification"))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(fail("a predicate"))
      val applied = ok(LogicError.lift(Term.app(predicate, moves.term(text, domain))))
      Term.destEq(ok(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(fail("an equation"))
    }

  def conjuncts(term: Term): List[Term] = moves.logic.destConj(term) match {
    case Some((a, b)) => a :: conjuncts(b)
    case None => List(term)
  }

  def split(term: Term): (Term, Term) = moves.logic.destConj(term).getOrElse(fail("a conjunction"))

  def rightOf(equation: Kernel.Thm): Term = Term.destEq(equation.conclusion).map(_._2).getOrElse(fail("an equation"))

  def argumentsOf(term: Term, taken: List[Term] = Nil): List[Term] = term match {
    case App(fn, argument) => argumentsOf(fn, argument :: taken)
    case _ => taken
  }

  /** `|- C a1 ... an = <its body>`, reduced, for a definition of `Resolving`. */
  def unfold(name: String, arguments: List[Term]): Kernel.Thm = {
    val equation = ok(Conv.unfold(ok(chain.resolving.definition(name)), arguments))
    moves.trans(equation, ok(Conv.betaNormalise(rightOf(equation))))
  }

  /** `|- goal[x]` from `|- c = x` and `|- goal[c]`. */
  def carried(equation: Kernel.Thm, variable: FVar, goal: Term, atValue: Kernel.Thm): Kernel.Thm = {
    val zz = Term.variable("zz", variable.ty)
    val lambda = ok(LogicError.lift(Term.abs(zz, ok(LogicError.lift(Term.substitute(Map(variable -> zz), goal))))))
    val across = ok(Conv.apTerm(lambda, equation))
    val (from, to) = Term.destEq(across.conclusion).getOrElse(fail("an equation"))
    val joined = moves.trans(moves.trans(moves.sym(ok(Conv.betaRoot(from))), across), ok(Conv.betaRoot(to)))
    ok(LogicError.lift(Kernel.eqMp(joined, atValue)))
  }

  /**
   * `|- !x. NUM_LT x c ==> body[x]`, the goal given as a term, by proving the body at each numeral
   * below `c` and carrying it back to `x`. `name` is the variable opened, which differs between a
   * case analysis and one nested inside it, since the outer one's guard is still a hypothesis.
   */
  def belowBound(goal: Term, bound: Int, name: String = "w")(atValue: (Int, Term) => Kernel.Thm): Kernel.Thm = {
    val x = Term.variable(name, Num)
    val (guard, body) = implication(opened(goal, name))
    def cases(upTo: Int, below: Kernel.Thm): Kernel.Thm =
      if (upTo == 0) moves.exFalso(body, moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), name), below))
      else {
        val split = moves.mp(moves.spec(moves.pf(Peano.BelowSuccessorCases), numeral(upTo - 1), name), below)
        moves.byDisjunction(split)(
          earlier => cases(upTo - 1, earlier),
          same => {
            val (_, bodyAtValue) = implication(opened(goal, numeral(upTo - 1)))
            carried(moves.sym(same), x, body, atValue(upTo - 1, bodyAtValue))
          }
        )
      }
    ok(moves.rules.gen(x, ok(moves.rules.disch(guard, cases(bound, moves.assumeT(guard))))))
  }

  /** `|- NUM_LT a b` for numerals `a < b`. */
  def below(a: Int, b: Int): Kernel.Thm =
    if (b == a + 1) moves.spec(moves.pf(Peano.BelowSuccessor), numeral(a))
    else moves.mp(moves.spec(moves.pf(Peano.StrictTransitive), numeral(a), numeral(b - 1), numeral(b)),
      moves.conj(below(a, b - 1), moves.spec(moves.pf(Peano.BelowSuccessor), numeral(b - 1))))

  /** `|- NUM_LE a b` for numerals `a <= b`. */
  def noMoreThan(a: Int, b: Int): Kernel.Thm =
    if (a == b) moves.spec(moves.pf(Peano.Reflexive), numeral(a))
    else moves.mp(moves.spec(moves.pf(Peano.AtMostFromBelow), numeral(a), numeral(b)), below(a, b))

  /** `|- ~(a = b)` for two different numerals in successor form. */
  def distinct(a: Term, b: Term): Kernel.Thm = {
    def inner(term: Term): Option[Term] = term match {
      case App(Const("SUC", _), x) => Some(x)
      case _ => None
    }
    val equal = ok(LogicError.lift(Term.eq(a, b)))
    (inner(a), inner(b)) match {
      case (Some(x), Some(y)) =>
        val injective = moves.mp(moves.spec(moves.nf(Natural.SuccessorInjective), show(x), show(y)), moves.assumeT(equal))
        ok(moves.rules.notIntro(equal, moves.absurd(distinct(x, y), injective)))
      case (Some(x), None) => moves.spec(moves.nf(Natural.SuccessorNotZero), show(x))
      case (None, Some(y)) =>
        val reversed = moves.spec(moves.nf(Natural.SuccessorNotZero), show(y))
        ok(moves.rules.notIntro(equal, moves.absurd(reversed, moves.sym(moves.assumeT(equal)))))
      case _ => fail(s"two different numerals: ${show(a)}, ${show(b)}")
    }
  }

  /** `|- t = t'`, every `COND` at the root whose guard compares two numerals decided. */
  def decided(term: Term): Kernel.Thm = term match {
    case App(App(App(Const("COND", ty), guard), yes), no) =>
      val (a, b) = Term.destEq(guard).getOrElse(fail("a guard that is an equation"))
      val at = Type.destFun(ty).flatMap(t => Type.destFun(t._2)).map(_._1).getOrElse(fail("a conditional's type"))
      def schema(name: String) = Kernel.instType(Map(Classical.TypeVariable -> at), ok(moves.classical.fact(name)))
      val step =
        if (a == b) moves.mp(ok(moves.rules.specAll(schema(Classical.CondTrue), List(guard, yes, no))), Conv.refl(a))
        else moves.mp(ok(moves.rules.specAll(schema(Classical.CondFalse), List(guard, yes, no))), distinct(a, b))
      moves.trans(step, decided(rightOf(step)))
    case other => Conv.refl(other)
  }

  /** A value hypothesis `lhs = rhs` after instantiation, proved by deciding `lhs`. */
  def valueHolds(statement: Term): Kernel.Thm = {
    val (lhs, rhs) = Term.destEq(statement).getOrElse(fail("an equation"))
    val proof = decided(lhs)
    if (rightOf(proof) != rhs) fail(s"a value that decides to ${show(rhs)}: ${show(rightOf(proof))}")
    proof
  }

  /* ------------------------------------------------------- a refutation as data */

  /** Pigeon `pigeon` in hole `hole`, positively or negatively. */
  final case class Literal(pigeon: Int, hole: Int, positive: Boolean)

  /**
   * A refutation over the variables `p * holes + h`: the clauses in order, the first `inputs` of
   * them the inputs, and each later one the resolvent of a parent holding the pivot positively and
   * one holding it negatively. The last clause is the empty one.
   */
  final class Refutation(holes: Int, val clauses: Vector[Vector[Literal]], val inputs: Int, steps: Map[Int, (Int, Int, (Int, Int))]) {
    require(clauses.last.isEmpty, "a refutation ends at the empty clause")
    require(clauses.indices.drop(inputs).forall(steps.contains), "every derived clause names its parents")

    val size: Int = clauses.size

    def variable(pigeon: Int, hole: Int): String = s"(NUM_ADD (NUM_MUL ${numeral(pigeon)} ${numeral(holes)}) ${numeral(hole)})"
    private def polarity(literal: Literal): String = if (literal.positive) "T" else "F"

    private def lengthText(j: Int): String = s"k ${numeral(j)} = ${numeral(clauses(j).size)}"
    private def variableText(j: Int, i: Int): String =
      s"v ${numeral(j)} ${numeral(i)} = ${variable(clauses(j)(i).pigeon, clauses(j)(i).hole)}"
    private def polarityText(j: Int, i: Int): String = s"s ${numeral(j)} ${numeral(i)} = ${polarity(clauses(j)(i))}"

    /** Every value the derivation reads, as an equation over the free `k`, `v`, `s`. */
    val values: List[String] = clauses.indices.toList.flatMap { j =>
      lengthText(j) :: clauses(j).indices.toList.flatMap(i => List(variableText(j, i), polarityText(j, i)))
    }
    private val known: Map[String, Kernel.Thm] = values.map(text => text -> moves.assume(text)).toMap

    def lengthOf(j: Int): Kernel.Thm = known(lengthText(j))
    def variableOf(j: Int, i: Int): Kernel.Thm = known(variableText(j, i))
    def polarityOf(j: Int, i: Int): Kernel.Thm = known(polarityText(j, i))

    /** `|- NUM_LT i (k j)` for a literal index of clause `j`. */
    def indexBelow(j: Int, i: Int): Kernel.Thm =
      moves.transport(moves.sym(lengthOf(j)), s"NUM_LT ${numeral(i)} zz", below(i, clauses(j).size))

    /** `|- !i. NUM_LT i (k j) ==> body[i]`, from the body at each literal index of clause `j`. */
    def forEachLiteral(goal: Term, j: Int)(atIndex: (Int, Term) => Kernel.Thm): Kernel.Thm = {
      val (guard, body) = implication(opened(goal, "i"))
      val underLength = moves.transport(lengthOf(j), "NUM_LT i zz", moves.assumeT(guard))
      val lifted = ok(moves.logic.mkForall(Term.variable("i", Num),
        ok(moves.logic.mkImp(moves.prop(s"NUM_LT i ${numeral(clauses(j).size)}"), body))))
      val byIndex = belowBound(lifted, clauses(j).size, "t")(atIndex)
      moves.generalised(ok(moves.rules.disch(guard, moves.mp(moves.spec(byIndex, "i"), underLength))), "i")
    }

    /** A parent's literals are carried into step `j`, all but the pivot at the parent's polarity. */
    private def carries(goal: Term, parent: Int, j: Int, pivot: Literal): Kernel.Thm =
      forEachLiteral(goal, parent) { (c, atC) =>
        val (denial, conclusion) = implication(atC)
        val literal = clauses(parent)(c)
        val proof =
          if (literal == pivot)
            moves.exFalso(conclusion, moves.absurd(moves.assumeT(denial), moves.conj(variableOf(parent, c), polarityOf(parent, c))))
          else {
            val at = clauses(j).indexOf(literal)
            if (at < 0) fail(s"clause $j lacks a literal of its parent $parent")
            moves.witnessed(conclusion, List(numeral(at)), moves.conj(indexBelow(j, at), moves.conj(
              moves.trans(variableOf(j, at), moves.sym(variableOf(parent, c))),
              moves.trans(polarityOf(j, at), moves.sym(polarityOf(parent, c))))))
          }
        ok(moves.rules.disch(denial, proof))
      }

    private def justified(body: Term, j: Int): Kernel.Thm =
      if (j < inputs) moves.disjoined(body, below(j, inputs))
      else {
        val (_, resolventPart) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
        val (first, second, (pigeon, hole)) = steps(j)
        val pivot = variable(pigeon, hole)
        val parts = conjuncts(opened(resolventPart, numeral(first), numeral(second), pivot))
        val proof = moves.conj(below(first, j), moves.conj(below(second, j), moves.conj(
          carries(parts(2), first, j, Literal(pigeon, hole, positive = true)),
          carries(parts(3), second, j, Literal(pigeon, hole, positive = false)))))
        moves.disjoined(body, moves.witnessed(resolventPart, List(numeral(first), numeral(second), pivot), proof))
      }

    /** `|- RES_REFUTATION k v s inputs m`, given as the goal, under the values. */
    def refutes(goal: Term): Kernel.Thm = {
      val opening = unfold(Resolving.Refutation, argumentsOf(goal))
      val (everyStep, reachesEmpty) = split(rightOf(opening))
      val stepsHold = belowBound(everyStep, size) { (j, justifiedAt) =>
        val justifying = unfold(Resolving.JustifiedName, argumentsOf(justifiedAt))
        ok(LogicError.lift(Kernel.eqMp(moves.sym(justifying), justified(rightOf(justifying), j))))
      }
      val last = size - 1
      val empty = moves.witnessed(reachesEmpty, List(numeral(last)), moves.conj(below(last, size), lengthOf(last)))
      ok(LogicError.lift(Kernel.eqMp(moves.sym(opening), moves.conj(stepsHold, empty))))
    }

    private def table(rows: IndexedSeq[String], index: String, default: String): String =
      rows.zipWithIndex.foldRight(default) { case ((row, at), rest) => s"(COND ($index = ${numeral(at)}) $row $rest)" }

    val lengths: String = s"\\j:num. ${table(clauses.map(c => numeral(c.size)), "j", "ZERO")}"
    val variables: String =
      s"\\j:num. \\i:num. ${table(clauses.map(c => table(c.map(l => variable(l.pigeon, l.hole)), "i", "ZERO")), "j", "ZERO")}"
    val polarities: String = s"\\j:num. \\i:num. ${table(clauses.map(c => table(c.map(polarity), "i", "F")), "j", "F")}"

    /**
     * The theorem with every value hypothesis discharged, the three functions put in as tables, and
     * each value then proved by deciding its conditional: what is left rests on nothing assumed.
     */
    def close(theorem: Kernel.Thm): Kernel.Thm = {
      val discharged = values.reverse.foldLeft(theorem)((current, text) => ok(moves.rules.disch(moves.prop(text), current)))
      val concrete = moves.inst(discharged, "k" -> lengths, "v" -> variables, "s" -> polarities)
      val (valueTerms, _) = antecedents(concrete.conclusion, values.size)
      valueTerms.foldLeft(concrete)((current, value) => moves.mp(current, valueHolds(value)))
    }
  }

  /**
   * A refutation of the pigeonhole principle for three pigeons and two holes, nineteen steps, found
   * by eliminating the third pigeon's variables first. Its inputs are the three pigeon clauses and
   * the six hole clauses, pigeons `c < d` at hole `h` in the order `(h, c, d)`.
   */
  lazy val threeIntoTwo: Refutation = {
    def pos(p: Int, h: Int) = Literal(p, h, positive = true)
    def neg(p: Int, h: Int) = Literal(p, h, positive = false)
    val inputs = Vector(
      Vector(pos(0, 0), pos(0, 1)), Vector(pos(1, 0), pos(1, 1)), Vector(pos(2, 0), pos(2, 1)),
      Vector(neg(0, 0), neg(1, 0)), Vector(neg(0, 0), neg(2, 0)), Vector(neg(1, 0), neg(2, 0)),
      Vector(neg(0, 1), neg(1, 1)), Vector(neg(0, 1), neg(2, 1)), Vector(neg(1, 1), neg(2, 1))
    )
    val derived = Vector(
      9 -> (Vector(pos(2, 1), neg(0, 0)), (2, 4, (2, 0))),
      10 -> (Vector(pos(2, 1), neg(1, 0)), (2, 5, (2, 0))),
      11 -> (Vector(neg(0, 0), neg(1, 1)), (9, 8, (2, 1))),
      12 -> (Vector(neg(1, 0), neg(0, 1)), (10, 7, (2, 1))),
      13 -> (Vector(pos(0, 1), neg(1, 0)), (0, 3, (0, 0))),
      14 -> (Vector(pos(0, 1), neg(1, 1)), (0, 11, (0, 0))),
      15 -> (Vector(neg(1, 0)), (13, 12, (0, 1))),
      16 -> (Vector(neg(1, 1)), (14, 6, (0, 1))),
      17 -> (Vector(pos(1, 1)), (1, 15, (1, 0))),
      18 -> (Vector(), (17, 16, (1, 1)))
    )
    new Refutation(2, inputs ++ derived.map(_._2._1), inputs.size, derived.map { case (j, (_, step)) => j -> step }.toMap)
  }
}
