package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The width of a resolution refutation of the pigeonhole principle, and what keeps the theorem from
 * being about nothing.
 *
 * **That its hypotheses are met, at the smallest instance with a derived step.** A lower bound whose
 * hypotheses nothing satisfies is true and empty, and it would pass every other test here. At
 * `n = 1` there are two pigeons and one hole, and the refutation has five steps: the two pigeon
 * clauses `x0` and `x1`, the hole clause `~x0 \/ ~x1`, the resolvent `~x1` of the first with the
 * third, and the empty clause, resolving the second with the fourth. Every hypothesis is derived for
 * it with nothing assumed and the theorem is detached there.
 *
 * **That `0 < n` is load-bearing.** At `n = 0` the one pigeon's clause is empty, so the refutation of
 * one step meets the other two hypotheses and has no derived step at all: the conclusion is refuted
 * at it. The theorem with that hypothesis dropped is false, and that is derived rather than argued.
 *
 * **That the injection bound needs its injectivity.** A constant function from two numbers into one
 * meets the range hypothesis, and `2 <= 1` is refuted.
 *
 * The goals are read off the published theorem, specialised, rather than written out a second time
 * here: what is shown to be met is exactly what the theorem asks.
 */
class PigeonholeSpec extends AnyFlatSpec with Matchers {

  private def ok[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val chain = Chain.standard
  private lazy val pigeonhole = ok(Pigeonhole.construct(chain))
  private lazy val moves = new Pigeonhole.Builder(chain)
  private val Num = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = ok(pigeonhole.fact(name))

  "Every fact of the development" should "prove the statement it is published as" in {
    Pigeonhole.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe ok(pigeonhole.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
    pigeonhole.facts.keySet shouldBe Pigeonhole.Statements.map(_._1).toSet
  }

  it should "cost choice and infinity and none of the reals' sixteen" in {
    // Built over the chain's end, where the reals live; nothing about a field is reached.
    val expected = Set(
      ok(chain.classical.axiom(Classical.Choice)).conclusion,
      ok(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    Pigeonhole.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)) shouldBe expected)
    }
  }

  it should "read the bad pigeons through the soundness of a resolution step" in {
    // Step 3 of the argument: a resolvent's bad pigeons are its parents'. A proof that reached the
    // conclusion some other way would state the same thing and would not be this argument.
    val wanted = Set(ok(chain.resolving.fact(Resolving.StepSound)).conclusion)
    Derivation.restingOn(fact(Pigeonhole.DerivedWidth), wanted) shouldBe wanted
  }

  /* ------------------------------------------------------------------ the moves */

  private def numeral(value: Int): String = if (value == 0) "ZERO" else s"(SUC ${numeral(value - 1)})"
  private val One = numeral(1)
  private val Two = numeral(2)
  private val Three = numeral(3)
  private val Four = numeral(4)
  private val Five = numeral(5)

  private def implication(term: Term): (Term, Term) =
    moves.logic.destImp(term).getOrElse(fail(s"an implication: ${pigeonhole.show(term)}"))

  /** The antecedents and the conclusion of `a1 ==> ... ==> an ==> c`, `count` of them. */
  private def antecedents(term: Term, count: Int): (List[Term], Term) =
    if (count == 0) (Nil, term)
    else {
      val (first, rest) = implication(term)
      val (more, conclusion) = antecedents(rest, count - 1)
      (first :: more, conclusion)
    }

  /** The body of `?x1 ... xn. body` or `!x. body` at the given witnesses, root-contracted. */
  private def opened(quantified: Term, witnesses: String*): Term =
    witnesses.foldLeft(quantified) { (current, text) =>
      val predicate = moves.logic.destExistsPredicate(current)
        .orElse(moves.logic.destForallPredicate(current)).getOrElse(fail("a quantification"))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(fail("a predicate"))
      val applied = ok(LogicError.lift(Term.app(predicate, moves.term(text, domain))))
      Term.destEq(ok(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(fail("an equation"))
    }

  private def conjuncts(term: Term): List[Term] = moves.logic.destConj(term) match {
    case Some((a, b)) => a :: conjuncts(b)
    case None => List(term)
  }

  /** `|- goal[x]` from `|- x = c`... read backwards: from `|- c = x` and `|- goal[c]`. */
  private def carried(equation: Kernel.Thm, variable: FVar, goal: Term, atValue: Kernel.Thm): Kernel.Thm = {
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
  private def belowBound(goal: Term, bound: Int, name: String = "w")(atValue: (Int, Term) => Kernel.Thm): Kernel.Thm = {
    val x = Term.variable(name, Num)
    val (guard, body) = implication(opened(goal, name))
    def split(upTo: Int, below: Kernel.Thm): Kernel.Thm =
      if (upTo == 0) moves.exFalso(body, moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), name), below))
      else {
        val cases = moves.mp(moves.spec(moves.pf(Peano.BelowSuccessorCases), numeral(upTo - 1), name), below)
        moves.byDisjunction(cases)(
          earlier => split(upTo - 1, earlier),
          same => {
            val (_, bodyAtValue) = implication(opened(goal, numeral(upTo - 1)))
            carried(moves.sym(same), x, body, atValue(upTo - 1, bodyAtValue))
          }
        )
      }
    ok(moves.rules.gen(x, ok(moves.rules.disch(guard, split(bound, moves.assumeT(guard))))))
  }

  /** `|- C a1 ... an = <its body>`, reduced, for a definition of `Resolving`. */
  private def unfold(name: String, arguments: List[Term]): Kernel.Thm = {
    val equation = ok(Conv.unfold(ok(chain.resolving.definition(name)), arguments))
    val right = Term.destEq(equation.conclusion).map(_._2).getOrElse(fail("an equation"))
    moves.trans(equation, ok(Conv.betaNormalise(right)))
  }

  private def rightOf(equation: Kernel.Thm): Term = Term.destEq(equation.conclusion).map(_._2).getOrElse(fail("an equation"))
  private def split(term: Term): (Term, Term) = moves.logic.destConj(term).getOrElse(fail("a conjunction"))

  /** `|- NUM_LT a b` for numerals `a < b`. */
  private def below(a: Int, b: Int): Kernel.Thm =
    if (b == a + 1) moves.spec(moves.pf(Peano.BelowSuccessor), numeral(a))
    else moves.mp(moves.spec(moves.pf(Peano.StrictTransitive), numeral(a), numeral(b - 1), numeral(b)),
      moves.conj(below(a, b - 1), moves.spec(moves.pf(Peano.BelowSuccessor), numeral(b - 1))))

  /** `|- ~(a = b)` for two different numerals in successor form. */
  private def distinct(a: Term, b: Term): Kernel.Thm = {
    def inner(term: Term): Option[Term] = term match {
      case App(Const("SUC", _), x) => Some(x)
      case _ => None
    }
    val equal = ok(LogicError.lift(Term.eq(a, b)))
    (inner(a), inner(b)) match {
      case (Some(x), Some(y)) =>
        val injective = moves.mp(moves.spec(moves.nf(Natural.SuccessorInjective), pigeonhole.show(x), pigeonhole.show(y)), moves.assumeT(equal))
        ok(moves.rules.notIntro(equal, moves.absurd(distinct(x, y), injective)))
      case (Some(x), None) => moves.spec(moves.nf(Natural.SuccessorNotZero), pigeonhole.show(x))
      case (None, Some(y)) =>
        val reversed = moves.spec(moves.nf(Natural.SuccessorNotZero), pigeonhole.show(y))
        ok(moves.rules.notIntro(equal, moves.absurd(reversed, moves.sym(moves.assumeT(equal)))))
      case _ => fail(s"two different numerals: ${pigeonhole.show(a)}, ${pigeonhole.show(b)}")
    }
  }

  /** `|- t = t'`, every `COND` at the root whose guard compares two numerals decided. */
  private def decided(term: Term): Kernel.Thm = term match {
    case App(App(App(Const("COND", ty), guard), yes), no) =>
      val (a, b) = Term.destEq(guard).getOrElse(fail("a guard that is an equation"))
      val at = Type.destFun(ty).flatMap(t => Type.destFun(t._2)).map(_._1).getOrElse(fail("a conditional's type"))
      def schema(name: String) = Kernel.instType(Map(Classical.TypeVariable -> at), ok(chain.classical.fact(name)))
      val step =
        if (a == b) moves.mp(ok(moves.rules.specAll(schema(Classical.CondTrue), List(guard, yes, no))), Conv.refl(a))
        else moves.mp(ok(moves.rules.specAll(schema(Classical.CondFalse), List(guard, yes, no))), distinct(a, b))
      moves.trans(step, decided(Term.destEq(step.conclusion).map(_._2).getOrElse(fail("an equation"))))
    case other => Conv.refl(other)
  }

  /** A value hypothesis `lhs = rhs` or `!i. lhs = rhs` after instantiation, proved by deciding `lhs`. */
  private def valueHolds(statement: Term): Kernel.Thm =
    moves.logic.destForallPredicate(statement) match {
      case Some(_) =>
        val body = opened(statement, "i")
        ok(moves.rules.gen(Term.variable("i", Num), valueHolds(body)))
      case None =>
        val (lhs, rhs) = Term.destEq(statement).getOrElse(fail("an equation"))
        val proof = decided(lhs)
        Term.destEq(proof.conclusion).map(_._2) shouldBe Some(rhs)
        proof
    }

  /* ----------------------------------------------------- the refutation at n = 1 */

  private def variableOf(pigeon: String): String = s"NUM_ADD (NUM_MUL $pigeon $One) ZERO"
  private val X0 = variableOf("ZERO")
  private val X1 = variableOf(One)

  /** What the three functions are where the argument reads them, of free `k`, `v`, `s`. */
  private val Values: List[String] = List(
    s"k ZERO = $One", s"k $One = $One", s"k $Two = $Two", s"k $Three = $One", s"k $Four = ZERO",
    s"!i:num. v ZERO i = $X0", s"!i:num. v $One i = $X1", s"v $Two ZERO = $X0", s"v $Two $One = $X1",
    s"!i:num. v $Three i = $X1",
    s"!i:num. s ZERO i = T", s"!i:num. s $One i = T", s"!i:num. s $Two i = F", s"!i:num. s $Three i = F"
  )

  private val Lengths = s"\\j:num. COND (j = $Four) ZERO (COND (j = $Two) $Two $One)"
  private val Variables = s"\\j:num. \\i:num. COND (j = ZERO) ($X0) (COND (j = $Two) (COND (i = ZERO) ($X0) ($X1)) ($X1))"
  private val Polarities = s"\\j:num. \\i:num. COND (j = $Two) F (COND (j = $Three) F T)"

  private final case class Known(values: Map[String, Kernel.Thm]) {
    def apply(text: String): Kernel.Thm = values.getOrElse(text, fail(s"no value $text"))
    def at(text: String, index: String): Kernel.Thm = moves.spec(apply(text), index)
  }

  /** Every input is a clause of the principle, from the values alone. */
  private def inputsAreClauses(goal: Term, known: Known): Kernel.Thm =
    belowBound(goal, 3) { (c, body) =>
      val (pigeonPart, holePart) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
      val j = numeral(c)
      if (c < 2) {
        val x = if (c == 0) X0 else X1
        val parts = conjuncts(opened(pigeonPart, j))
        val atMost =
          if (c == 0) moves.spec(moves.pf(Peano.ZeroIsLeast), One) else moves.spec(moves.pf(Peano.Reflexive), One)
        val length = known(s"k $j = $One")
        val literal = s"!i:num. v $j i = $x"
        val positive = s"!i:num. s $j i = T"
        // Every literal is `j` in some hole: the only hole, zero.
        val everyLiteral = {
          val (guard, inner) = implication(opened(parts(1), "i"))
          val found = moves.witnessed(inner, List("ZERO"), moves.conj(below(0, 1), moves.conj(known.at(literal, "i"), known.at(positive, "i"))))
          moves.generalised(ok(moves.rules.disch(guard, found)), "i")
        }
        // Every hole has a literal: the hole is zero and the literal is the first.
        val everyHole = belowBound(parts(2), 1, "t") { (_, atZero) =>
          moves.witnessed(atZero, List("ZERO"), moves.conj(moves.transport(moves.sym(length), "NUM_LT ZERO zz", below(0, 1)),
            moves.conj(known.at(literal, "ZERO"), known.at(positive, "ZERO"))))
        }
        moves.disjoined(body, moves.witnessed(pigeonPart, List(j), moves.conj(atMost, moves.conj(everyLiteral, everyHole))))
      } else {
        val parts = conjuncts(opened(holePart, "ZERO", One, "ZERO"))
        val length = known(s"k $Two = $Two")
        val negative = s"!i:num. s $Two i = F"
        val literals = Map(0 -> known(s"v $Two ZERO = $X0"), 1 -> known(s"v $Two $One = $X1"))
        val every = {
          val (guard, _) = implication(opened(parts(3), "i"))
          val underTwo = moves.transport(length, "NUM_LT i zz", moves.assumeT(guard))
          val lifted = moves.logic.mkForall(Term.variable("i", Num), ok(moves.logic.mkImp(
            moves.prop(s"NUM_LT i $Two"), implication(opened(parts(3), "i"))._2)))
          val byIndex = belowBound(ok(lifted), 2, "t") { (index, atIndex) =>
            val (either, polarity) = moves.logic.destConj(atIndex).getOrElse(fail("a conjunction"))
            moves.conj(moves.disjoined(either, literals(index)), known.at(negative, numeral(index)))
          }
          moves.generalised(ok(moves.rules.disch(guard, moves.mp(moves.spec(byIndex, "i"), underTwo))), "i")
        }
        def present(index: Int, part: Term): Kernel.Thm =
          moves.witnessed(part, List(numeral(index)), moves.conj(
            moves.transport(moves.sym(length), s"NUM_LT ${numeral(index)} zz", below(index, 2)),
            moves.conj(literals(index), known.at(negative, numeral(index)))))
        val proof = moves.conj(below(0, 1), moves.conj(moves.spec(moves.pf(Peano.Reflexive), One), moves.conj(below(0, 1),
          moves.conj(every, moves.conj(present(0, parts(4)), present(1, parts(5)))))))
        moves.disjoined(body, moves.witnessed(holePart, List("ZERO", One, "ZERO"), proof))
      }
    }

  /** `|- RES_JUSTIFIED k v s 3 j` opened, at `j` = 3 or 4, from the values. */
  private def resolved(body: Term, step: Int, known: Known): Kernel.Thm = {
    val (_, resolventPart) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
    val (first, second, pivot, pivotText) =
      if (step == 3) (0, 2, X0, "ZERO") else (1, 3, X1, One)
    val _ = pivotText
    val parts = conjuncts(opened(resolventPart, numeral(first), numeral(second), s"($pivot)"))
    // A parent whose every literal is the pivot at the pivot's own polarity carries nothing.
    def carriesNothing(goal: Term, parent: Int): Kernel.Thm = {
      val (guard, rest) = implication(opened(goal, "i"))
      val (denial, conclusion) = implication(rest)
      val literal = parent match {
        case 0 => known.at(s"!i:num. v ZERO i = $X0", "i")
        case 1 => known.at(s"!i:num. v $One i = $X1", "i")
        case 3 => known.at(s"!i:num. v $Three i = $X1", "i")
        case _ => fail("a parent of one literal")
      }
      val polarity = parent match {
        case 0 => known.at("!i:num. s ZERO i = T", "i")
        case 1 => known.at(s"!i:num. s $One i = T", "i")
        case _ => known.at(s"!i:num. s $Three i = F", "i")
      }
      val contradicted = moves.absurd(moves.assumeT(denial), moves.conj(literal, polarity))
      moves.generalised(ok(moves.rules.disch(guard, ok(moves.rules.disch(denial, moves.exFalso(conclusion, contradicted))))), "i")
    }
    // The hole clause resolved on `x0` leaves `~x1`, which step three is.
    def carriesTheOther(goal: Term): Kernel.Thm = {
      val (guard, _) = implication(opened(goal, "i"))
      val underTwo = moves.transport(known(s"k $Two = $Two"), "NUM_LT i zz", moves.assumeT(guard))
      val lifted = ok(moves.logic.mkForall(Term.variable("i", Num), ok(moves.logic.mkImp(
        moves.prop(s"NUM_LT i $Two"), implication(opened(goal, "i"))._2))))
      val byIndex = belowBound(lifted, 2, "t") { (index, atIndex) =>
        val (denial, conclusion) = implication(atIndex)
        if (index == 0) {
          val pair = moves.conj(known(s"v $Two ZERO = $X0"), known.at(s"!i:num. s $Two i = F", "ZERO"))
          ok(moves.rules.disch(denial, moves.exFalso(conclusion, moves.absurd(moves.assumeT(denial), pair))))
        } else {
          val sameVariable = moves.trans(known.at(s"!i:num. v $Three i = $X1", "ZERO"), moves.sym(known(s"v $Two $One = $X1")))
          val samePolarity = moves.trans(known.at(s"!i:num. s $Three i = F", "ZERO"), moves.sym(known.at(s"!i:num. s $Two i = F", One)))
          val witness = moves.transport(moves.sym(known(s"k $Three = $One")), "NUM_LT ZERO zz", below(0, 1))
          ok(moves.rules.disch(denial, moves.witnessed(conclusion, List("ZERO"), moves.conj(witness, moves.conj(sameVariable, samePolarity)))))
        }
      }
      moves.generalised(ok(moves.rules.disch(guard, moves.mp(moves.spec(byIndex, "i"), underTwo))), "i")
    }
    val carriesFirst = carriesNothing(parts(2), first)
    val carriesSecond = if (step == 3) carriesTheOther(parts(3)) else carriesNothing(parts(3), second)
    val proof = moves.conj(below(first, step), moves.conj(below(second, step), moves.conj(carriesFirst, carriesSecond)))
    moves.disjoined(body, moves.witnessed(resolventPart, List(numeral(first), numeral(second), s"($pivot)"), proof))
  }

  /** `|- RES_REFUTATION k v s 3 5`, from the values. */
  private def refutes(goal: Term, known: Known): Kernel.Thm = {
    val opening = unfold(Resolving.Refutation, argumentsOf(goal))
    val (everyStep, reachesEmpty) = split(rightOf(opening))
    val steps = belowBound(everyStep, 5) { (j, justifiedAt) =>
      val justifying = unfold(Resolving.JustifiedName, argumentsOf(justifiedAt))
      val body = rightOf(justifying)
      val proof =
        if (j < 3) moves.disjoined(body, below(j, 3))
        else resolved(body, j, known)
      ok(LogicError.lift(Kernel.eqMp(moves.sym(justifying), proof)))
    }
    val empty = moves.witnessed(reachesEmpty, List(Four), moves.conj(below(4, 5), known(s"k $Four = ZERO")))
    ok(LogicError.lift(Kernel.eqMp(moves.sym(opening), moves.conj(steps, empty))))
  }

  "The theorem" should "have hypotheses a refutation meets, and detach at it" in {
    val general = moves.spec(fact(Pigeonhole.DerivedWidth), One, "k", "v", "s", Three, Five)
    val (hypotheses, _) = antecedents(general.conclusion, 3)
    val inputs = hypotheses(1)
    val refutation = hypotheses(2)
    val known = Known(Values.map(text => text -> moves.assume(text)).toMap)

    val detached = moves.mp(general, below(0, 1), inputsAreClauses(inputs, known), refutes(refutation, known))
    val closed = Values.reverse.foldLeft(detached)((current, text) => ok(moves.rules.disch(moves.prop(text), current)))

    // Now the functions themselves: every value hypothesis is a conditional that decides.
    val concrete = moves.inst(closed, "k" -> Lengths, "v" -> Variables, "s" -> Polarities)
    val (valueTerms, conclusion) = antecedents(concrete.conclusion, Values.size)
    val result = valueTerms.foldLeft(concrete)((current, value) => moves.mp(current, valueHolds(value)))

    result.hypotheses shouldBe empty
    result.conclusion shouldBe conclusion
    // What it says there: some step from the fourth on is at least `n - 1 = 0` long, the length
    // being the conditional the refutation's lengths are written with.
    result.conclusion shouldBe moves.prop(
      s"?j:num. NUM_LE $Three j /\\ NUM_LT j $Five /\\ NUM_LE $One (SUC (COND (j = $Four) ZERO (COND (j = $Two) $Two $One)))")
  }

  it should "be false without 0 < n, at the one-step refutation of the empty pigeon clause" in {
    // At `n = 0` the pigeon clause is empty, so a refutation can stop at its input.
    val general = moves.spec(fact(Pigeonhole.DerivedWidth), "ZERO", "k", "v", "s", One, One)
    val (hypotheses, conclusion) = antecedents(general.conclusion, 3)
    val positive = hypotheses(0)
    val inputs = hypotheses(1)
    val refutation = hypotheses(2)
    val emptyLength = moves.assume("k ZERO = ZERO")

    val clause = belowBound(inputs, 1) { (_, body) =>
      val (pigeonPart, _) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
      val parts = conjuncts(opened(pigeonPart, "ZERO"))
      def vacuous(goal: Term, bound: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
        val (guard, rest) = implication(opened(goal, "i"))
        val underZero = bound(moves.assumeT(guard))
        val absurd = moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), "i"), underZero)
        moves.generalised(ok(moves.rules.disch(guard, moves.exFalso(rest, absurd))), "i")
      }
      val literals = vacuous(parts(1), below => moves.transport(emptyLength, "NUM_LT i zz", below))
      val holes = vacuous(parts(2), identity)
      moves.disjoined(body, moves.witnessed(pigeonPart, List("ZERO"),
        moves.conj(moves.spec(moves.pf(Peano.ZeroIsLeast), "ZERO"), moves.conj(literals, holes))))
    }
    val refuting = {
      val opening = unfold(Resolving.Refutation, argumentsOf(refutation))
      val (everyStep, reachesEmpty) = split(rightOf(opening))
      val steps = belowBound(everyStep, 1) { (_, justifiedAt) =>
        val justifying = unfold(Resolving.JustifiedName, argumentsOf(justifiedAt))
        ok(LogicError.lift(Kernel.eqMp(moves.sym(justifying), moves.disjoined(rightOf(justifying), below(0, 1)))))
      }
      val empty = moves.witnessed(reachesEmpty, List("ZERO"), moves.conj(below(0, 1), emptyLength))
      ok(LogicError.lift(Kernel.eqMp(moves.sym(opening), moves.conj(steps, empty))))
    }
    refuting.conclusion shouldBe refutation
    clause.conclusion shouldBe inputs

    // And nothing it asks for exists: a derived step is at least one and below one.
    val refuted = ok(moves.rules.notIntro(conclusion, {
      val assumed = moves.assumeT(conclusion)
      val predicate = moves.logic.destExistsPredicate(conclusion).get
      val j = Term.variable("j", Num)
      val body = Term.destEq(ok(Conv.betaRoot(ok(LogicError.lift(Term.app(predicate, j))))).conclusion).map(_._2).get
      val parts = moves.assumeT(body)
      val atLeast = moves.left(parts)
      val underOne = moves.left(moves.right(parts))
      val excluded = moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), "j", One), underOne)
      ok(moves.rules.existsElim(assumed, j, moves.absurd(excluded, atLeast)))
    }))
    // The two hypotheses rest on the one-step refutation's length alone, the conclusion's denial on
    // nothing; what stands between them and a falsity is `0 < 0`, which is itself refuted.
    refuted.hypotheses shouldBe empty
    clause.hypotheses.toSet shouldBe Set(moves.prop("k ZERO = ZERO"))
    refuting.hypotheses.toSet shouldBe Set(moves.prop("k ZERO = ZERO"))
    positive shouldBe moves.prop("NUM_LT ZERO ZERO")
    moves.spec(moves.pf(Peano.StrictIrreflexive), "ZERO").conclusion shouldBe ok(moves.logic.mkNot(positive))
  }

  private def argumentsOf(term: Term, taken: List[Term] = Nil): List[Term] = term match {
    case App(fn, argument) => argumentsOf(fn, argument :: taken)
    case _ => taken
  }

  "The injection bound" should "need its injectivity: a constant function puts two into one" in {
    val general = moves.spec(fact(Pigeonhole.Injection), Two, One, "\\x:num. ZERO")
    val (hypotheses, conclusion) = antecedents(general.conclusion, 2)
    val range = hypotheses(0)
    val rangeHolds = {
      val (guard, body) = implication(opened(range, "x"))
      moves.generalised(ok(moves.rules.disch(guard, below(0, 1).ensuring(_.conclusion == body))), "x")
    }
    rangeHolds.conclusion shouldBe range
    val notInjective = moves.spec(moves.nf(Natural.SuccessorNotZero), "ZERO")
    notInjective.conclusion shouldBe moves.prop(s"~($One = ZERO)")
    moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), One, Two), below(1, 2)).conclusion shouldBe
      ok(moves.logic.mkNot(conclusion))
  }
}
