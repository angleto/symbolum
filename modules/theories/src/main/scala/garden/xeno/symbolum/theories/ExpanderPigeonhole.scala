package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A width lower bound for resolution refutations of the pigeonhole principle on a graph that
 * expands: the argument of Ben-Sasson and Wigderson, proved.
 *
 * {{{
 *   !np n adj r w k v s inputs m.
 *     NUM_LT 0 r ==> <MATCHABLE> ==> <EXPANDING> ==>
 *     (!j. NUM_LT j inputs ==> <clause j is a clause of the principle on adj>) ==>
 *     RES_REFUTATION k v s inputs m ==>
 *     ?j. NUM_LT j m /\ NUM_LE w (k j)
 * }}}
 *
 * == Why this and not the complete principle ==
 *
 * `Pigeonhole.RES_PHP_DERIVED_WIDTH` bounds the width of refutations of the principle in which
 * every pigeon may go to every hole, and on that formula a width bound is cheap: a pigeon clause
 * already has `n` literals, so a resolvent with one as a parent has `n - 1` of them. A width bound
 * says something about proof complexity only on a formula whose inputs are **short**, and that is
 * the principle restricted to a bipartite graph `adj` of small degree: pigeon `p` may go only to a
 * hole `h` with `adj p h`, so a pigeon clause is as long as the pigeon's degree. Ben-Sasson and
 * Wigderson, "Short proofs are narrow: resolution made simple", J. ACM 48 (2001), show that when
 * the graph expands every refutation holds a clause as wide as the expansion guarantees, which for
 * a bounded-degree expander is linear in the number of holes.
 *
 * == The two hypotheses on the graph, which the statement carries ==
 *
 * **`MATCHABLE`**: every set of at most `r` pigeons has an injective matching into the holes along
 * `adj`. The source derives it from the expansion by Hall's theorem, which is not in this
 * repository; so it is a hypothesis, which is the honest form of using a theorem without proving
 * it. It is a property of the graph and says nothing about any refutation.
 *
 * **`EXPANDING`**: every set of exactly `t` pigeons with `t <= r < 2t` has at least `w` holes that
 * have exactly one neighbour in the set, its unique-neighbour boundary.
 *
 * There are no finite sets and no cardinality here, the first limit `Pigeonhole` met, so a set of
 * pigeons is a predicate `sx : num -> bool` read below `np`; "at most `t` elements" is an injection
 * into `[0, t)`, "exactly `t`" is that and not "at most `PRE t`", and "at least `w` boundary holes"
 * is an injection from `[0, w)` into the boundary.
 *
 * == The argument ==
 *
 * `mu(C)` is the least number of pigeons whose clauses, together with every hole clause, imply `C`.
 * "Implied" is written out: every assignment satisfying those clauses satisfies `C`.
 *
 *   1. An input is implied by at most one pigeon: its own if it is a pigeon clause, none if it is a
 *      hole clause.
 *   2. No set of at most `r` pigeons implies the empty clause: the matching is an assignment
 *      satisfying all of them and every hole clause.
 *   3. A resolvent is implied by the union of what implies its parents, which is `RES_STEP_SOUND`,
 *      and the union of a set of `a` and one of `b` injects into `[0, a + b)`.
 *   4. So the first step no set of `r` implies is a resolvent whose parents are each implied by at
 *      most `r`, and the larger of the parents' measures is more than half of `r`. That parent is
 *      the clause the argument is about: `r < 2 mu <= 2 r`.
 *   5. Take a set `S` of `mu` pigeons implying it. For a boundary hole `h` with its one neighbour
 *      `p` in `S`: `S` without `p` is smaller, so if the clause had no literal at hole `h`, an
 *      assignment satisfying the smaller set could be changed at hole `h` alone, putting `p` there
 *      and taking every other pigeon out, into one satisfying `S`; the clause would read the two
 *      alike, so the smaller set would imply it. Hence a literal at every boundary hole, and holes
 *      differ, so `w` boundary holes give `w` distinct literals: `Pigeonhole.NUM_INJECTION_LE`.
 *
 * Step 4 takes the least such step with `NUM_LEAST`, as `Pigeonhole` takes its first clause with
 * two bad pigeons, rather than descending by strong induction.
 *
 * == What it found ==
 *
 *   - **Hall's theorem is missing**, so `MATCHABLE` is a hypothesis where the source derives it.
 *   - The absence of finite sets, again: every size here is an injection into an interval.
 *
 * It sits outside the chain with `Pigeonhole`'s standing and declares nothing.
 */
final class ExpanderPigeonhole private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object ExpanderPigeonhole {

  /** The theorem. See the class comment for the statement. */
  val ExpanderWidth: String = "RES_GPHP_WIDTH"

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Fun: Type = Type.fun(Num, Num)
  private val Pred: Type = Type.fun(Num, Type.Bool)
  private val Rel: Type = Type.fun(Num, Pred)

  /** `Pigeonhole`'s variables, and the ones this argument adds. */
  private val Types: Map[String, Type] =
    Pigeonhole.Types ++
      List("np", "ta", "tb", "z", "l", "i0", "h0", "p0", "q0", "h2", "q1", "i1", "i2", "j1").map(_ -> Num).toMap ++
      Map("adj" -> Rel, "sx" -> Pred, "sa" -> Pred, "sb" -> Pred, "al" -> Pred) ++
      Map("ga" -> Fun, "gc" -> Fun, "g1" -> Fun, "g2" -> Fun, "gb" -> Fun)

  /* ------------------------------------------------------------------------- the texts */

  /** The variable of pigeon `p` in hole `h`, as in `Pigeonhole`: injective for `h < n`. */
  private def xv(p: String, h: String): String = s"(NUM_ADD (NUM_MUL $p n) $h)"

  /** The assignment `al` satisfies clause `j`, the way `RES_SAT` opens. */
  private def clauseSat(al: String, j: String): String =
    s"(?i0:num. NUM_LT i0 (k $j) /\\ ($al (v $j i0) = s $j i0))"

  /** The pigeon clause of `p` on the graph, satisfied by `al`. */
  private def pigeonAx(al: String, p: String): String =
    s"(?h0:num. NUM_LT h0 n /\\ adj $p h0 /\\ $al ${xv(p, "h0")} = T)"

  /** Every hole clause on the graph, satisfied by `al`. */
  private def holeAx(al: String): String =
    "(!h0:num. !p0:num. !q0:num. NUM_LT h0 n ==> NUM_LT p0 q0 ==> NUM_LT q0 np ==> adj p0 h0 ==> adj q0 h0 ==> " +
      s"~($al ${xv("p0", "h0")} = T /\\ $al ${xv("q0", "h0")} = T))"

  /** `al` satisfies the pigeon clauses of the set and every hole clause. */
  private def satS(al: String, set: String): String =
    s"((!p0:num. NUM_LT p0 np ==> $set p0 ==> ${pigeonAx(al, "p0")}) /\\ ${holeAx(al)})"

  /** The axioms of the set imply clause `j`. */
  private def implies(set: String, j: String): String =
    s"(!al:num->bool. ${satS("al", set)} ==> ${clauseSat("al", j)})"

  /** The set, read below `np`, has at most `t` elements: it injects into `[0, t)`. */
  private def atMost(set: String, t: String): String =
    s"(?g1:num->num. (!p0:num. NUM_LT p0 np ==> $set p0 ==> NUM_LT (g1 p0) $t) /\\ " +
      s"(!p0:num. !q0:num. NUM_LT p0 np ==> NUM_LT q0 np ==> $set p0 ==> $set q0 ==> g1 p0 = g1 q0 ==> p0 = q0))"

  /** `mu(j) <= t`: some set of at most `t` pigeons implies clause `j`. */
  private def measured(j: String, t: String): String =
    s"(?sx:num->bool. ${atMost("sx", t)} /\\ ${implies("sx", j)})"

  /** Clause `j`'s least measure `t` has `t <= r < 2t`. */
  private def midRest(j: String): String =
    s"(?t:num. ${measured(j, "t")} /\\ (!z:num. NUM_LT z t ==> ~${measured(j, "z")}) /\\ " +
      "NUM_LE t r /\\ NUM_LT r (NUM_ADD t t))"

  private def mid(j: String): String = s"(NUM_LT $j m /\\ ${midRest(j)})"

  /** Hole `h` has exactly one neighbour in the set. */
  private def boundary(set: String, h: String): String =
    s"(NUM_LT $h n /\\ (?p0:num. NUM_LT p0 np /\\ $set p0 /\\ adj p0 $h /\\ " +
      s"(!q0:num. NUM_LT q0 np ==> $set q0 ==> adj q0 $h ==> q0 = p0)))"

  /** The set without `p`. */
  private def without(set: String, p: String): String = s"(\\y:num. $set y /\\ ~(y = $p))"

  val Matchable: String =
    s"(!sx:num->bool. ${atMost("sx", "r")} ==> (?g2:num->num. " +
      "(!p0:num. NUM_LT p0 np ==> sx p0 ==> NUM_LT (g2 p0) n /\\ adj p0 (g2 p0)) /\\ " +
      "(!p0:num. !q0:num. NUM_LT p0 np ==> NUM_LT q0 np ==> sx p0 ==> sx q0 ==> g2 p0 = g2 q0 ==> p0 = q0)))"

  val Expanding: String =
    s"(!sx:num->bool. !t:num. NUM_LE t r ==> NUM_LT r (NUM_ADD t t) ==> ${atMost("sx", "t")} ==> " +
      s"~${atMost("sx", "(PRE t)")} ==> (?gb:num->num. " +
      s"(!i1:num. NUM_LT i1 w ==> ${boundary("sx", "(gb i1)")}) /\\ " +
      "(!i1:num. !i2:num. NUM_LT i1 w ==> NUM_LT i2 w ==> gb i1 = gb i2 ==> i1 = i2)))"

  /** Clause `j` is the pigeon clause of `c`: every literal `c` in a neighbouring hole, positively, and every one present. */
  private def pigeonClause(j: String, c: String): String =
    s"(NUM_LT $c np /\\ " +
      s"(!i:num. NUM_LT i (k $j) ==> ?h:num. NUM_LT h n /\\ adj $c h /\\ v $j i = ${xv(c, "h")} /\\ s $j i = T) /\\ " +
      s"(!h:num. NUM_LT h n ==> adj $c h ==> ?i:num. NUM_LT i (k $j) /\\ v $j i = ${xv(c, "h")} /\\ s $j i = T))"

  /** Clause `j` is the hole clause of `c < d` at a hole `h` both are adjacent to. */
  private def holeClause(j: String, c: String, d: String, h: String): String =
    s"(NUM_LT $c $d /\\ NUM_LT $d np /\\ NUM_LT $h n /\\ adj $c $h /\\ adj $d $h /\\ " +
      s"(!i:num. NUM_LT i (k $j) ==> (v $j i = ${xv(c, h)} \\/ v $j i = ${xv(d, h)}) /\\ s $j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k $j) /\\ v $j i = ${xv(c, h)} /\\ s $j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k $j) /\\ v $j i = ${xv(d, h)} /\\ s $j i = F))"

  /** Clause `j` is a clause of the pigeonhole principle on `adj`, `np` pigeons and `n` holes. */
  val Clause: String =
    s"((?c:num. ${pigeonClause("j", "c")}) \\/ (?c:num. ?d:num. ?h:num. ${holeClause("j", "c", "d", "h")}))"

  /** How a resolvent's literals carry a parent's, as `RES_JUSTIFIED` opens. */
  private def carries(parent: String, j: String, polarity: String): String =
    s"(!i:num. NUM_LT i (k $parent) ==> ~(v $parent i = x /\\ s $parent i = $polarity) ==> " +
      s"(?w3:num. NUM_LT w3 (k $j) /\\ v $j w3 = v $parent i /\\ s $j w3 = s $parent i))"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    ExpanderWidth ->
      ("!np:num. !n:num. !adj:num->num->bool. !r:num. !w:num. " +
        "!k:num->num. !v:num->num->num. !s:num->num->bool. !inputs:num. !m:num. " +
        s"NUM_LT 0 r ==> $Matchable ==> $Expanding ==> " +
        s"(!j:num. NUM_LT j inputs ==> $Clause) ==> " +
        "RES_REFUTATION k v s inputs m ==> " +
        "(?j:num. NUM_LT j m /\\ NUM_LE w (k j))")
  )

  /** The development over the chain it is handed. It extends nothing. */
  def construct(chain: Chain): Either[LogicError, ExpanderPigeonhole] = {
    val signature = chain.widest
    try {
      val proof = new Proof(chain)
      val facts = Map(ExpanderWidth -> proof.checked(ExpanderWidth, proof.width))
      Right(new ExpanderPigeonhole(signature.theory, signature.notation, chain.logic, facts))
    } catch { case refused: Moves.RefusedHere => Left(refused.error) }
  }

  /** The development over the standard chain. */
  lazy val standard: ExpanderPigeonhole =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /* ------------------------------------------------------------------------- the proof */

  /** The derivation, over `Pigeonhole`'s moves and this file's variables. */
  private[theories] final class Proof(chain: Chain) {
    val b = new Pigeonhole.Builder(chain, Types, Moves.Written)
    import b.*

    def mf(name: String): Kernel.Thm = force(chain.modular.fact(name))

    def checked(name: String, theorem: Kernel.Thm): Kernel.Thm = {
      val text = Statements.collectFirst { case (`name`, statement) => statement }.getOrElse(refuse(name, logic.falsity))
      val expected = force(Parser.proposition(theory, notation, text))
      if (theorem.conclusion == expected && theorem.hypotheses.isEmpty) theorem
      else refuse(s"$name as it is written", theorem.conclusion)
    }

    /* ------------------------------------------------ moves over beta-normal forms */

    /**
     * Every text here that applies a set, a map or an assignment written as a lambda produces a
     * redex, and `spec` contracts it where `assume` does not. These put both sides of a step into
     * normal form first, so that which of the two produced a theorem stops mattering.
     */
    def mpn(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
      premises.foldLeft(reduced(implication))((current, premise) => force(rules.mp(current, reduced(premise))))

    def absurdN(negation: Kernel.Thm, positive: Kernel.Thm): Kernel.Thm = absurd(reduced(negation), reduced(positive))

    def wit(target: Term, witnesses: List[String], proof: Kernel.Thm): Kernel.Thm =
      witnessed(target, witnesses, reduced(proof))

    /** The normal form of a term. */
    def normal(term: Term): Term =
      Term.destEq(force(Conv.betaNormalise(term)).conclusion).map(_._2).getOrElse(refuse("an equation", term))

    def refl(text: String): Kernel.Thm = Conv.refl(term(text, Num))

    /** The `i`th of `count` conjuncts, associated to the right. */
    def part(theorem: Kernel.Thm, i: Int, count: Int): Kernel.Thm = {
      val tail = (0 until i).foldLeft(theorem)((current, _) => right(current))
      if (i == count - 1) tail else left(tail)
    }

    /* --------------------------------------------------------- COND at any type */

    def destCond(term: Term): (Term, Term, Term) = term match {
      case App(App(App(_, guard), yes), no) => (guard, yes, no)
      case other => refuse("a conditional", other)
    }

    /** `|- COND c a b = a` from `|- c`, at the type of `a`. */
    def condHolds(conditional: Term, guard: Kernel.Thm): Kernel.Thm = {
      val (c, yes, no) = destCond(conditional)
      if (guard.conclusion != c) refuse("a proof of the conditional's guard", guard.conclusion)
      val at = Kernel.instType(Map(Classical.TypeVariable -> Term.typeOf(yes)), cf(Classical.CondTrue))
      mp(force(rules.specAll(at, List(c, yes, no))), guard)
    }

    /** `|- COND c a b = b` from `|- ~c`, at the type of `a`. */
    def condFails(conditional: Term, guard: Kernel.Thm): Kernel.Thm = {
      val (c, yes, no) = destCond(conditional)
      if (!logic.destNot(guard.conclusion).contains(c)) refuse("a proof that the conditional's guard fails", guard.conclusion)
      val at = Kernel.instType(Map(Classical.TypeVariable -> Term.typeOf(yes)), cf(Classical.CondFalse))
      mp(force(rules.specAll(at, List(c, yes, no))), guard)
    }

    /** `|- y = F` from `|- ~(y = T)`. */
    def notTrue(theorem: Kernel.Thm): Kernel.Thm = {
      val equation = logic.destNot(theorem.conclusion).getOrElse(refuse("a negation", theorem.conclusion))
      val (y, _) = Term.destEq(equation).getOrElse(refuse("an equation", equation))
      val goal = force(LogicError.lift(Term.eq(y, logic.falsity)))
      cases(y)(
        holds => exFalso(goal, absurd(theorem, truthEquation(holds))),
        fails => falseEquation(fails)
      )
    }

    /* ------------------------------------------------------------------ variables */

    /**
     * `|- NUM_LT h n ==> NUM_LT h2 n ==> x(p, h) = x(q, h2) ==> p = q /\ h = h2`: the uniqueness
     * of quotient and remainder at the divisor `n`, after `NUM_MUL_SYM` puts `n` first.
     */
    lazy val variableInjective: Kernel.Thm = {
      val first = assume("NUM_LT h n")
      val second = assume("NUM_LT h2 n")
      val same = assume(s"${xv("p", "h")} = ${xv("q", "h2")}")
      val moved = transport(spec(pf(Peano.MulCommutative), "p", "n"), s"NUM_ADD zz h = ${xv("q", "h2")}", same)
      val movedBoth = transport(spec(pf(Peano.MulCommutative), "q", "n"), "NUM_ADD (NUM_MUL n p) h = NUM_ADD zz h2", moved)
      val result = mpn(spec(mf(Modular.DivisionUnique), "n", "p", "h", "q", "h2"), conj(movedBoth, conj(first, second)))
      discharged(result, "NUM_LT h n", "NUM_LT h2 n", s"${xv("p", "h")} = ${xv("q", "h2")}")
    }

    def sameVariable(p: String, h: String, q: String, h2: String, hBelow: Kernel.Thm, h2Below: Kernel.Thm, equal: Kernel.Thm): Kernel.Thm =
      mpn(inst(variableInjective, "p" -> p, "h" -> h, "q" -> q, "h2" -> h2), hBelow, h2Below, equal)

    /* ------------------------------------------------------------- 1. the inputs */

    /** `|- NUM_LT 0 r ==> Clause ==> measured(j, r)`. */
    lazy val inputMeasured: Kernel.Thm = {
      val positive = assume("NUM_LT ZERO r")
      val isClause = assume(Clause)
      val goal = prop(measured("j", "r"))
      val constant = "(\\y:num. ZERO)"
      val result = byDisjunction(isClause)(
        pigeon => opened(pigeon, "c") { body =>
          // The set {c}, injected into [0, r) by the constant zero.
          val single = "(\\y:num. y = c)"
          val bounded = generalised(discharged(positive, "NUM_LT p0 np", s"$single p0"), "p0")
          val injective = {
            val p0Is = reduced(assume(s"$single p0"))
            val q0Is = reduced(assume(s"$single q0"))
            generalised(discharged(trans(p0Is, sym(q0Is)), "NUM_LT p0 np", "NUM_LT q0 np", s"$single p0", s"$single q0",
              s"$constant p0 = $constant q0"), "p0", "q0")
          }
          val sized = wit(prop(atMost(single, "r")), List(constant), conj(bounded, injective))
          val sat = reduced(assume(satS("al", single)))
          val axiom = mpn(spec(left(sat), "c"), part(body, 0, 3), refl("c"))
          val satisfied = opened(axiom, "h0") { at =>
            val literal = mpn(spec(part(body, 2, 3), "h0"), part(at, 0, 3), part(at, 1, 3))
            opened(literal, "i0") { found =>
              val atLiteral = transport(sym(part(found, 1, 3)), "al zz = T", part(at, 2, 3))
              wit(prop(clauseSat("al", "j")), List("i0"), conj(part(found, 0, 3), trans(atLiteral, sym(part(found, 2, 3)))))
            }
          }
          val implied = generalised(discharged(satisfied, satS("al", single)), "al")
          wit(goal, List(single), conj(sized, implied))
        },
        holes => opened(holes, "c") { h1 => opened(h1, "d") { h2 => opened(h2, "h") { body =>
          // The empty set: the hole clause follows from the hole clauses alone.
          val empty = "(\\y:num. F)"
          val bounded = generalised(discharged(exFalso(prop("NUM_LT ZERO r"), reduced(assume(s"$empty p0"))),
            "NUM_LT p0 np", s"$empty p0"), "p0")
          val injective = generalised(discharged(exFalso(prop("p0 = q0"), reduced(assume(s"$empty p0"))),
            "NUM_LT p0 np", "NUM_LT q0 np", s"$empty p0", s"$empty q0", s"$constant p0 = $constant q0"), "p0", "q0")
          val sized = wit(prop(atMost(empty, "r")), List(constant), conj(bounded, injective))
          val sat = reduced(assume(satS("al", empty)))
          val exclusive = mpn(spec(right(sat), "h", "c", "d"),
            part(body, 2, 8), part(body, 0, 8), part(body, 1, 8), part(body, 3, 8), part(body, 4, 8))
          def fromLiteral(literal: Kernel.Thm, isFalse: Kernel.Thm): Kernel.Thm =
            opened(literal, "i0") { found =>
              val atLiteral = transport(sym(part(found, 1, 3)), "al zz = F", isFalse)
              wit(prop(clauseSat("al", "j")), List("i0"), conj(part(found, 0, 3), trans(atLiteral, sym(part(found, 2, 3)))))
            }
          val satisfied = cases(prop(s"al ${xv("c", "h")} = T"))(
            cTrue => {
              val dNot = refuted(prop(s"al ${xv("d", "h")} = T"))(dTrue => absurdN(exclusive, conj(cTrue, dTrue)))
              fromLiteral(part(body, 7, 8), notTrue(dNot))
            },
            cNot => fromLiteral(part(body, 6, 8), notTrue(cNot))
          )
          val implied = generalised(discharged(satisfied, satS("al", empty)), "al")
          wit(goal, List(empty), conj(sized, implied))
        } } }
      )
      discharged(result, "NUM_LT ZERO r", Clause)
    }

    /* ----------------------------------------------------- 2. the empty clause */

    /** `|- k j = ZERO ==> Matchable ==> atMost(sx, r) ==> ~implies(sx, j)`. */
    lazy val emptyUnimplied: Kernel.Thm = {
      val empty = assume("k j = ZERO")
      val matchable = assume(Matchable)
      val sized = assume(atMost("sx", "r"))
      val result = opened(mpn(spec(matchable, "sx"), sized), "g2") { matched =>
        val bounded = left(matched)
        val injective = right(matched)
        val assignment = s"(\\y:num. ?p1:num. NUM_LT p1 np /\\ sx p1 /\\ y = ${xv("p1", "(g2 p1)")})"
        refuted(prop(implies("sx", "j"))) { implying =>
          // Every pigeon of the set sits in its matched hole.
          val pigeons = {
            val below = assume("NUM_LT p0 np")
            val member = assume("sx p0")
            val matchedAt = mpn(spec(bounded, "p0"), below, member)
            val inHole = wit(prop(s"?p1:num. NUM_LT p1 np /\\ sx p1 /\\ ${xv("p0", "(g2 p0)")} = ${xv("p1", "(g2 p1)")}"),
              List("p0"), conj(below, conj(member, refl(xv("p0", "(g2 p0)")))))
            val axiom = wit(prop(pigeonAx(assignment, "p0")), List("g2 p0"),
              conj(left(matchedAt), conj(right(matchedAt), truthEquation(inHole))))
            generalised(discharged(axiom, "NUM_LT p0 np", "sx p0"), "p0")
          }
          // No hole holds two, since the matching is injective.
          val holes = {
            val hBelow = assume("NUM_LT h0 n")
            val ordered = assume("NUM_LT p0 q0")
            val two = normal(prop(s"$assignment ${xv("p0", "h0")} = T /\\ $assignment ${xv("q0", "h0")} = T"))
            val neither = refuted(two) { both =>
              opened(force(rules.eqTruthElim(left(both))), "p1") { pp =>
                opened(force(rules.eqTruthElim(right(both))), "q1") { qq =>
                  val p1Hole = left(mpn(spec(bounded, "p1"), part(pp, 0, 3), part(pp, 1, 3)))
                  val q1Hole = left(mpn(spec(bounded, "q1"), part(qq, 0, 3), part(qq, 1, 3)))
                  val pEq = sameVariable("p0", "h0", "p1", "(g2 p1)", hBelow, p1Hole, part(pp, 2, 3))
                  val qEq = sameVariable("q0", "h0", "q1", "(g2 q1)", hBelow, q1Hole, part(qq, 2, 3))
                  val holesAgree = trans(sym(right(pEq)), right(qEq))
                  val p1q1 = mpn(spec(injective, "p1", "q1"), part(pp, 0, 3), part(qq, 0, 3), part(pp, 1, 3), part(qq, 1, 3), holesAgree)
                  val p0q0 = trans(trans(left(pEq), p1q1), sym(left(qEq)))
                  absurd(spec(pf(Peano.StrictIrreflexive), "q0"), transport(p0q0, "NUM_LT zz q0", ordered))
                }
              }
            }
            generalised(discharged(neither, "NUM_LT h0 n", "NUM_LT p0 q0", "NUM_LT q0 np", "adj p0 h0", "adj q0 h0"),
              "h0", "p0", "q0")
          }
          val satisfied = mpn(spec(implying, assignment), conj(pigeons, holes))
          opened(satisfied, "i0") { found =>
            absurd(spec(pf(Peano.NotBelowZero), "i0"), transport(empty, "NUM_LT i0 zz", left(found)))
          }
        }
      }
      discharged(result, "k j = ZERO", Matchable, atMost("sx", "r"))
    }

    /* ------------------------------------------------------- 3. a resolvent */

    /**
     * `|- carries(pa) ==> carries(pb) ==> measured(pa, ta) ==> measured(pb, tb) ==>
     *     measured(j, ta + tb)`.
     */
    lazy val resolventMeasured: Kernel.Thm = {
      val carriesA = assume(carries("pa", "j", "T"))
      val carriesB = assume(carries("pb", "j", "F"))
      val measuredA = assume(measured("pa", "ta"))
      val measuredB = assume(measured("pb", "tb"))
      val union = "(\\y:num. sa y \\/ sb y)"
      val map = "(\\y:num. COND (sa y) (ga y) (NUM_ADD ta (gc y)))"
      val result = opened(measuredA, "sa") { a =>
        opened(measuredB, "sb") { bb =>
          opened(left(a), "ga") { fa =>
            opened(left(bb), "gc") { fc =>
              def inSecond(y: String, member: Kernel.Thm, notFirst: Kernel.Thm): Kernel.Thm =
                taut(prop(s"sb $y"), member, notFirst)

              // The union injects into [0, ta + tb): the first set below ta, the second shifted past it.
              val bounded = {
                val below = assume("NUM_LT p0 np")
                val member = reduced(assume(s"$union p0"))
                val value = cases(prop("sa p0"))(
                  inFirst => {
                    val small = mpn(spec(left(fa), "p0"), below, inFirst)
                    val widened = mpn(spec(pf(Peano.BelowThenAtMost), "ga p0", "ta", "NUM_ADD ta tb"),
                      conj(small, spec(pf(Peano.AtMostSum), "ta", "tb")))
                    transport(sym(whenHolds(inFirst, "ga p0", "NUM_ADD ta (gc p0)")), "NUM_LT zz (NUM_ADD ta tb)", widened)
                  },
                  notFirst => {
                    val small = mpn(spec(left(fc), "p0"), below, inSecond("p0", member, notFirst))
                    val shifted = mpn(spec(pf(Peano.AddStrictlyMonotone), "ta", "gc p0", "tb"), small)
                    transport(sym(whenFails(notFirst, "ga p0", "NUM_ADD ta (gc p0)")), "NUM_LT zz (NUM_ADD ta tb)", shifted)
                  }
                )
                generalised(discharged(value, "NUM_LT p0 np", s"$union p0"), "p0")
              }

              val injective = {
                val pBelow = assume("NUM_LT p0 np")
                val qBelow = assume("NUM_LT q0 np")
                val pMember = reduced(assume(s"$union p0"))
                val qMember = reduced(assume(s"$union q0"))
                val same = reduced(assume(s"$map p0 = $map q0"))
                /** `ga y < ta` and `ga y = ta + gc z` cannot both hold. */
                def apart(gz: String, small: Kernel.Thm, equal: Kernel.Thm): Kernel.Thm = {
                  val over = transport(equal, "NUM_LT zz ta", small)
                  val loop = mpn(spec(pf(Peano.AtMostThenBelow), "ta", s"NUM_ADD ta ($gz)", "ta"),
                    conj(spec(pf(Peano.AtMostSum), "ta", gz), over))
                  exFalso(prop("p0 = q0"), absurd(spec(pf(Peano.StrictIrreflexive), "ta"), loop))
                }
                def split(y: String, member: Kernel.Thm)(first: (Kernel.Thm, Kernel.Thm) => Kernel.Thm,
                    second: (Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm =
                  cases(prop(s"sa $y"))(
                    inFirst => first(inFirst, whenHolds(inFirst, s"ga $y", s"NUM_ADD ta (gc $y)")),
                    notFirst => second(inSecond(y, member, notFirst), whenFails(notFirst, s"ga $y", s"NUM_ADD ta (gc $y)"))
                  )
                val result = split("p0", pMember)(
                  (pFirst, pAt) => split("q0", qMember)(
                    (qFirst, qAt) =>
                      mpn(spec(right(fa), "p0", "q0"), pBelow, qBelow, pFirst, qFirst, trans(trans(sym(pAt), same), qAt)),
                    (_, qAt) =>
                      apart("gc q0", mpn(spec(left(fa), "p0"), pBelow, pFirst), trans(trans(sym(pAt), same), qAt))
                  ),
                  (pSecond, pAt) => split("q0", qMember)(
                    (qFirst, qAt) =>
                      apart("gc p0", mpn(spec(left(fa), "q0"), qBelow, qFirst), trans(trans(sym(qAt), sym(same)), pAt)),
                    (qSecond, qAt) => {
                      val shifted = trans(trans(sym(pAt), same), qAt)
                      val gSame = mpn(spec(pf(Peano.AddCancelsLeft), "gc p0", "gc q0", "ta"), shifted)
                      mpn(spec(right(fc), "p0", "q0"), pBelow, qBelow, pSecond, qSecond, gSame)
                    }
                  )
                )
                generalised(discharged(result, "NUM_LT p0 np", "NUM_LT q0 np", s"$union p0", s"$union q0",
                  s"$map p0 = $map q0"), "p0", "q0")
              }
              val sized = wit(prop(atMost(union, "(NUM_ADD ta tb)")), List(map), conj(bounded, injective))

              // What satisfies the union's clauses satisfies each parent's, so the resolvent.
              val sat = reduced(assume(satS("al", union)))
              def restricted(set: String): Kernel.Thm = {
                val below = assume("NUM_LT p0 np")
                val member = assume(s"$set p0")
                val axiom = mpn(spec(left(sat), "p0"), below, disjoined(prop("sa p0 \\/ sb p0"), member))
                conj(generalised(discharged(axiom, "NUM_LT p0 np", s"$set p0"), "p0"), right(sat))
              }
              val parentA = mpn(spec(right(a), "al"), restricted("sa"))
              val parentB = mpn(spec(right(bb), "al"), restricted("sb"))
              val step = spec(rf(Resolving.StepSound), "al", "v pa", "s pa", "v pb", "s pb", "v j", "s j",
                "k pa", "k pb", "k j", "x")
              val satisfied = mpn(step, carriesA, carriesB, parentA, parentB)
              val implied = generalised(discharged(satisfied, satS("al", union)), "al")
              wit(prop(measured("j", "(NUM_ADD ta tb)")), List(union), conj(sized, implied))
            }
          }
        }
      }
      discharged(result, carries("pa", "j", "T"), carries("pb", "j", "F"), measured("pa", "ta"), measured("pb", "tb"))
    }

    /** `|- measured(j, t) ==> NUM_LE t z ==> measured(j, z)`. */
    lazy val measuredMonotone: Kernel.Thm = {
      val at = assume(measured("j", "t"))
      val atMostZ = assume("NUM_LE t z")
      val result = opened(at, "sx") { body =>
        opened(left(body), "g1") { g =>
          val below = assume("NUM_LT p0 np")
          val member = assume("sx p0")
          val widened = mpn(spec(pf(Peano.BelowThenAtMost), "g1 p0", "t", "z"), conj(mpn(spec(left(g), "p0"), below, member), atMostZ))
          val bounded = generalised(discharged(widened, "NUM_LT p0 np", "sx p0"), "p0")
          val sized = wit(prop(atMost("sx", "z")), List("g1"), conj(bounded, right(g)))
          wit(prop(measured("j", "z")), List("sx"), conj(sized, right(body)))
        }
      }
      discharged(result, measured("j", "t"), "NUM_LE t z")
    }

    /* ------------------------------------------------------- 5. the boundary */

    /**
     * `|- atMost(sx, t) ==> sx p ==> NUM_LT p np ==> SUC (PRE t) = t ==> atMost(sx - {p}, PRE t)`.
     *
     * Whatever the injection sent to `PRE t` goes where `p` went, which is below `PRE t` because
     * the injection is injective: the fold `Pigeonhole.NUM_INJECTION_LE` is proved with.
     */
    lazy val removeOne: Kernel.Thm = {
      val sized = assume(atMost("sx", "t"))
      val member = assume("sx p")
      val pBelow = assume("NUM_LT p np")
      val sucPre = assume("SUC (PRE t) = t")
      val smaller = without("sx", "p")
      val folded = "(\\y:num. COND (g1 y = PRE t) (g1 p) (g1 y))"
      val result = opened(sized, "g1") { g =>
        val range = left(g)
        val injective = right(g)
        def belowPre(value: String, below: Kernel.Thm, differs: Kernel.Thm): Kernel.Thm = {
          val underSuccessor = transport(sym(sucPre), s"NUM_LT ($value) zz", below)
          val split = mpn(spec(pf(Peano.BelowSuccessorCases), "PRE t", value), underSuccessor)
          byDisjunction(split)(identity, same => exFalso(prop(s"NUM_LT ($value) (PRE t)"), absurd(differs, same)))
        }
        val bounded = {
          val below = assume("NUM_LT p0 np")
          val inSmaller = reduced(assume(s"$smaller p0"))
          val value = cases(prop("g1 p0 = PRE t"))(
            hit => {
              val differs = refuted(prop("g1 p = PRE t")) { e =>
                absurd(right(inSmaller), mpn(spec(injective, "p0", "p"), below, pBelow, left(inSmaller), member, trans(hit, sym(e))))
              }
              transport(sym(whenHolds(hit, "g1 p", "g1 p0")), "NUM_LT zz (PRE t)",
                belowPre("g1 p", mpn(spec(range, "p"), pBelow, member), differs))
            },
            miss => transport(sym(whenFails(miss, "g1 p", "g1 p0")), "NUM_LT zz (PRE t)",
              belowPre("g1 p0", mpn(spec(range, "p0"), below, left(inSmaller)), miss))
          )
          generalised(discharged(value, "NUM_LT p0 np", s"$smaller p0"), "p0")
        }
        val injectiveFolded = {
          val p0Below = assume("NUM_LT p0 np")
          val q0Below = assume("NUM_LT q0 np")
          val inP = reduced(assume(s"$smaller p0"))
          val inQ = reduced(assume(s"$smaller q0"))
          val same = reduced(assume(s"$folded p0 = $folded q0"))
          val result = cases(prop("g1 p0 = PRE t"))(
            hitP => cases(prop("g1 q0 = PRE t"))(
              hitQ => mpn(spec(injective, "p0", "q0"), p0Below, q0Below, left(inP), left(inQ), trans(hitP, sym(hitQ))),
              missQ => {
                val e = trans(trans(sym(whenHolds(hitP, "g1 p", "g1 p0")), same), whenFails(missQ, "g1 p", "g1 q0"))
                val pq = mpn(spec(injective, "p", "q0"), pBelow, q0Below, member, left(inQ), e)
                exFalso(prop("p0 = q0"), absurd(right(inQ), sym(pq)))
              }
            ),
            missP => cases(prop("g1 q0 = PRE t"))(
              hitQ => {
                val e = trans(trans(sym(whenFails(missP, "g1 p", "g1 p0")), same), whenHolds(hitQ, "g1 p", "g1 q0"))
                val pp = mpn(spec(injective, "p0", "p"), p0Below, pBelow, left(inP), member, e)
                exFalso(prop("p0 = q0"), absurd(right(inP), pp))
              },
              missQ => {
                val e = trans(trans(sym(whenFails(missP, "g1 p", "g1 p0")), same), whenFails(missQ, "g1 p", "g1 q0"))
                mpn(spec(injective, "p0", "q0"), p0Below, q0Below, left(inP), left(inQ), e)
              }
            )
          )
          generalised(discharged(result, "NUM_LT p0 np", "NUM_LT q0 np", s"$smaller p0", s"$smaller q0",
            s"$folded p0 = $folded q0"), "p0", "q0")
        }
        wit(prop(atMost(smaller, "(PRE t)")), List(folded), conj(bounded, injectiveFolded))
      }
      discharged(result, atMost("sx", "t"), "sx p", "NUM_LT p np", "SUC (PRE t) = t")
    }

    /** The literal the argument is after: some literal of clause `j1` is on a variable of hole `h`. */
    private val atHole: String =
      s"?l:num. NUM_LT l (k j1) /\\ (?q0:num. NUM_LT q0 np /\\ v j1 l = ${xv("q0", "h")})"

    /**
     * `boundary(sx, h) ==> atHole`, under a set `sx` of the least size `t` implying clause `j1`.
     *
     * If the clause has no literal at hole `h`, an assignment satisfying the set without `p` is
     * moved at hole `h` alone, `p` in and everybody else out, and the moved one satisfies the whole
     * set; the clause reads the two alike, so the smaller set implies it, against minimality.
     */
    def hit(sized: Kernel.Thm, implying: Kernel.Thm, minimal: Kernel.Thm, sucPre: Kernel.Thm, preBelow: Kernel.Thm): Kernel.Thm = {
      val bound = assume(boundary("sx", "h"))
      val hBelow = left(bound)
      val goal = prop(atHole)
      val result = opened(right(bound), "p") { own =>
        val pBelow = part(own, 0, 4)
        val member = part(own, 1, 4)
        val adjacent = part(own, 2, 4)
        val unique = part(own, 3, 4)
        byContradiction(goal) { none =>
          /** `~(v j1 i = x(q, h))`, since the clause has no literal at hole `h`. */
          def notAt(i: String, q: String, iBelow: Kernel.Thm, qBelow: Kernel.Thm): Kernel.Thm =
            refuted(prop(s"v j1 $i = ${xv(q, "h")}")) { equal =>
              absurdN(none, wit(goal, List(i), conj(iBelow,
                wit(prop(s"?q0:num. NUM_LT q0 np /\\ v j1 $i = ${xv("q0", "h")}"), List(q), conj(qBelow, equal)))))
            }
          val smaller = without("sx", "p")
          val sat = reduced(assume(satS("al", smaller)))
          val moved = s"(\\y:num. COND (y = ${xv("p", "h")}) T (COND (?qq:num. NUM_LT qq np /\\ y = ${xv("qq", "h")}) F (al y)))"
          def movedAt(y: String): Term = normal(term(s"$moved ($y)", Type.Bool))
          def inner(y: String): Term = destCond(movedAt(y))._3
          /** `moved y = al y`, from the two guards failing. */
          def unmoved(y: String, first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm =
            trans(condFails(movedAt(y), first), condFails(inner(y), second))
          /** `moved y = F`, from the first guard failing and the second holding. */
          def emptied(y: String, first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm =
            trans(condFails(movedAt(y), first), condHolds(inner(y), second))
          // The bound name is `qq` and not `q0` because `q0` is also a pigeon the hole clauses below
          // are opened at: written into this text it would be captured by the binder, and the guard
          // proved would be a different statement from the one in the conditional.
          def elsewhere(y: String): String = s"?qq:num. NUM_LT qq np /\\ $y = ${xv("qq", "h")}"

          // Every pigeon clause of the set holds of the moved assignment.
          val pigeons = {
            val below = assume("NUM_LT p0 np")
            val inSet = assume("sx p0")
            val axiom = cases(prop("p0 = p"))(
              isP => {
                val guard = transport(sym(isP), s"${xv("zz", "h")} = ${xv("p", "h")}", refl(xv("p", "h")))
                wit(prop(pigeonAx(moved, "p0")), List("h"),
                  conj(hBelow, conj(transport(sym(isP), "adj zz h", adjacent), condHolds(movedAt(xv("p0", "h")), guard))))
              },
              notP => opened(mpn(spec(left(sat), "p0"), below, conj(inSet, notP)), "h0") { at =>
                val h0Below = part(at, 0, 3)
                val first = refuted(prop(s"${xv("p0", "h0")} = ${xv("p", "h")}")) { equal =>
                  absurd(notP, left(sameVariable("p0", "h0", "p", "h", h0Below, hBelow, equal)))
                }
                val second = refuted(prop(elsewhere(xv("p0", "h0")))) { found =>
                  opened(found, "q1") { there =>
                    val same = sameVariable("p0", "h0", "q1", "h", h0Below, hBelow, right(there))
                    val adjacentHere = transport(right(same), "adj p0 zz", part(at, 1, 3))
                    absurd(notP, mpn(spec(unique, "p0"), below, inSet, adjacentHere))
                  }
                }
                wit(prop(pigeonAx(moved, "p0")), List("h0"),
                  conj(h0Below, conj(part(at, 1, 3), trans(unmoved(xv("p0", "h0"), first, second), part(at, 2, 3)))))
              }
            )
            generalised(discharged(axiom, "NUM_LT p0 np", "sx p0"), "p0")
          }

          // Every hole clause holds of it: at hole `h` only `p` is in, elsewhere nothing moved.
          val holes = {
            val h0Below = assume("NUM_LT h0 n")
            val ordered = assume("NUM_LT p0 q0")
            val q0Below = assume("NUM_LT q0 np")
            val p0Below = mpn(spec(pf(Peano.StrictTransitive), "p0", "q0", "np"), conj(ordered, q0Below))
            val two = normal(prop(s"$moved ${xv("p0", "h0")} = T /\\ $moved ${xv("q0", "h0")} = T"))
            val refutedTwo = cases(prop("h0 = h"))(
              atH => {
                /** A pigeon other than `p` is out of hole `h` under the moved assignment. */
                def out(q: String, qBelow: Kernel.Thm, notP: Kernel.Thm): Kernel.Thm = {
                  val first = refuted(prop(s"${xv(q, "h0")} = ${xv("p", "h")}")) { equal =>
                    absurd(notP, left(sameVariable(q, "h0", "p", "h", h0Below, hBelow, equal)))
                  }
                  val second = wit(prop(elsewhere(xv(q, "h0"))), List(q),
                    conj(qBelow, transport(atH, s"${xv(q, "h0")} = ${xv(q, "zz")}", refl(xv(q, "h0")))))
                  emptied(xv(q, "h0"), first, second)
                }
                refuted(two) { both =>
                  val contradiction = cases(prop("p0 = p"))(
                    isP => {
                      val qNotP = refuted(prop("q0 = p")) { e =>
                        absurd(spec(pf(Peano.StrictIrreflexive), "q0"), transport(trans(isP, sym(e)), "NUM_LT zz q0", ordered))
                      }
                      trans(sym(out("q0", q0Below, qNotP)), right(both))
                    },
                    notP => trans(sym(out("p0", p0Below, notP)), left(both))
                  )
                  force(rules.eqTruthElim(contradiction))
                }
              },
              notH => {
                def untouched(q: String): Kernel.Thm = {
                  val first = refuted(prop(s"${xv(q, "h0")} = ${xv("p", "h")}")) { equal =>
                    absurd(notH, right(sameVariable(q, "h0", "p", "h", h0Below, hBelow, equal)))
                  }
                  val second = refuted(prop(elsewhere(xv(q, "h0")))) { found =>
                    opened(found, "q1") { there => absurd(notH, right(sameVariable(q, "h0", "q1", "h", h0Below, hBelow, right(there)))) }
                  }
                  unmoved(xv(q, "h0"), first, second)
                }
                val before = mpn(spec(right(sat), "h0", "p0", "q0"), h0Below, ordered, q0Below,
                  assume("adj p0 h0"), assume("adj q0 h0"))
                refuted(two) { both =>
                  absurdN(before, conj(trans(sym(untouched("p0")), left(both)), trans(sym(untouched("q0")), right(both))))
                }
              }
            )
            generalised(discharged(refutedTwo, "NUM_LT h0 n", "NUM_LT p0 q0", "NUM_LT q0 np", "adj p0 h0", "adj q0 h0"),
              "h0", "p0", "q0")
          }

          // So the clause holds of the moved assignment, at a literal it did not move.
          val satisfied = opened(mpn(spec(implying, moved), conj(pigeons, holes)), "i0") { found =>
            val i0Below = left(found)
            val first = notAt("i0", "p", i0Below, pBelow)
            val second = refuted(prop(elsewhere("v j1 i0"))) { there =>
              opened(there, "q1") { at => absurd(notAt("i0", "q1", i0Below, left(at)), right(at)) }
            }
            wit(prop(clauseSat("al", "j1")), List("i0"), conj(i0Below, trans(sym(unmoved("v j1 i0", first, second)), right(found))))
          }
          val impliedSmaller = generalised(discharged(satisfied, satS("al", smaller)), "al")
          val shrunk = mpn(removeOne, sized, member, pBelow, sucPre)
          absurdN(mpn(spec(minimal, "PRE t"), preBelow),
            wit(prop(measured("j1", "(PRE t)")), List(smaller), conj(shrunk, impliedSmaller)))
        }
      }
      discharged(result, boundary("sx", "h"))
    }

    /** `NUM_LE w (k j1)` at a clause whose least measure `t` has `t <= r < 2t`. */
    def wide(midBody: Kernel.Thm): Kernel.Thm =
      opened(right(midBody), "t") { body =>
        val measuredT = part(body, 0, 4)
        val minimal = part(body, 1, 4)
        val tAtMostR = part(body, 2, 4)
        val rTwice = part(body, 3, 4)
        val expanding = assume(Expanding)
        // `t` is a successor, since `r < 0 + 0` is impossible.
        val preText = "SUC (PRE t) = t /\\ NUM_LT (PRE t) t"
        val pre = byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "t"))(
          zero => exFalso(prop(preText), absurd(spec(pf(Peano.NotBelowZero), "r"),
            transport(spec(pf(Peano.AddAtZero), "ZERO"), "NUM_LT r zz", substituted(zero, rTwice)))),
          successor => opened(successor, "y") { equation =>
            val preEq = trans(congruent("PRE", equation), spec(pf(Peano.PreAtSuccessor), "y"))
            val below = transport(sym(equation), "NUM_LT (PRE t) zz",
              transport(sym(preEq), "NUM_LT zz (SUC y)", spec(pf(Peano.BelowSuccessor), "y")))
            conj(trans(congruent("SUC", preEq), sym(equation)), below)
          }
        )
        val sucPre = left(pre)
        val preBelow = right(pre)
        opened(measuredT, "sx") { chosen =>
          val sized = left(chosen)
          val implying = right(chosen)
          val notSmaller = refuted(prop(atMost("sx", "(PRE t)"))) { small =>
            absurdN(mpn(spec(minimal, "PRE t"), preBelow), wit(prop(measured("j1", "(PRE t)")), List("sx"), conj(small, implying)))
          }
          val expansion = mpn(spec(expanding, "sx", "t"), tAtMostR, rTwice, sized, notSmaller)
          opened(expansion, "gb") { holes =>
            val onBoundary = left(holes)
            val holesDiffer = right(holes)
            val literal = hit(sized, implying, minimal, sucPre, preBelow)
            val pick = s"(\\i1:num. select (\\l:num. NUM_LT l (k j1) /\\ (?q0:num. NUM_LT q0 np /\\ v j1 l = ${xv("q0", "(gb i1)")})))"
            def boundaryAt(i: String, iBelow: Kernel.Thm): Kernel.Thm = mpn(spec(onBoundary, i), iBelow)
            def picked(i: String, iBelow: Kernel.Thm): Kernel.Thm =
              reduced(force(classical.witness(mpn(inst(literal, "h" -> s"gb $i"), boundaryAt(i, iBelow)))))
            val range = {
              val below = assume("NUM_LT i1 w")
              generalised(discharged(left(picked("i1", below)), "NUM_LT i1 w"), "i1")
            }
            val injective = {
              val first = assume("NUM_LT i1 w")
              val second = assume("NUM_LT i2 w")
              val same = reduced(assume(s"$pick i1 = $pick i2"))
              val result = opened(right(picked("i1", first)), "q1") { one =>
                opened(right(picked("i2", second)), "p1") { other =>
                  val variables = trans(trans(sym(right(one)), congruent("v j1", same)), right(other))
                  val holesEqual = right(sameVariable("q1", "(gb i1)", "p1", "(gb i2)",
                    left(boundaryAt("i1", first)), left(boundaryAt("i2", second)), variables))
                  mpn(spec(holesDiffer, "i1", "i2"), first, second, holesEqual)
                }
              }
              generalised(discharged(result, "NUM_LT i1 w", "NUM_LT i2 w", s"$pick i1 = $pick i2"), "i1", "i2")
            }
            mpn(spec(injection, "w", "k j1", pick), range, injective)
          }
        }
      }

    /* ------------------------------------------------------- 4. the descent */

    /** The least measure of clause `pp`, which has one at most `r`, named `name`. */
    def leastOf(pp: String, atR: Kernel.Thm, name: String)(reach: (Kernel.Thm, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
      val instance = spec(pf(Peano.LeastNumber), s"\\z:num. ${measured(pp, "z")}")
      val (some, _) = logic.destImp(instance.conclusion).getOrElse(refuse("an implication", instance.conclusion))
      opened(mpn(instance, wit(some, List("r"), atR)), name) { body =>
        val smaller = right(body)
        val notAbove = refuted(prop(s"NUM_LT r $name")) { above => absurdN(mpn(spec(smaller, "r"), above), atR) }
        reach(left(body), smaller, mpn(spec(pf(Peano.AtMostFromNotBelow), "r", name), notAbove))
      }
    }

    /** From the first step no set of `r` implies, a parent whose least measure is more than half of `r`. */
    def descend(step: Kernel.Thm, jBelow: Kernel.Thm, minimal: Kernel.Thm, notMeasured: Kernel.Thm): Kernel.Thm = {
      val goal = prop(s"?j1:num. ${mid("j1")}")
      val carriesA = part(step, 2, 4)
      val carriesB = part(step, 3, 4)
      def inRange(parent: String, below: Kernel.Thm): Kernel.Thm =
        mpn(spec(pf(Peano.StrictTransitive), parent, "j", "m"), conj(below, jBelow))
      def measuredAt(parent: String, below: Kernel.Thm): Kernel.Thm =
        byContradiction(prop(measured(parent, "r"))) { not =>
          absurdN(mpn(spec(minimal, parent), below), conj(inRange(parent, below), not))
        }
      def midAt(parent: String, below: Kernel.Thm, t: String, holds: Kernel.Thm, smaller: Kernel.Thm, atMostR: Kernel.Thm, twice: Kernel.Thm): Kernel.Thm =
        wit(goal, List(parent), conj(inRange(parent, below),
          wit(prop(midRest(parent)), List(t), conj(holds, conj(smaller, conj(atMostR, twice))))))
      val paBelow = part(step, 0, 4)
      val pbBelow = part(step, 1, 4)
      leastOf("pa", measuredAt("pa", paBelow), "ta") { (aHolds, aSmaller, aAtMost) =>
        leastOf("pb", measuredAt("pb", pbBelow), "tb") { (bHolds, bSmaller, bAtMost) =>
          val union = mpn(resolventMeasured, carriesA, carriesB, aHolds, bHolds)
          val rBelowSum = byContradiction(prop("NUM_LT r (NUM_ADD ta tb)")) { not =>
            val atMost = mpn(spec(pf(Peano.AtMostFromNotBelow), "r", "NUM_ADD ta tb"), not)
            absurdN(notMeasured, mpn(inst(measuredMonotone, "t" -> "NUM_ADD ta tb", "z" -> "r"), union, atMost))
          }
          byDisjunction(spec(pf(Peano.Total), "ta", "tb"))(
            aBelowB => {
              val twice = mpn(spec(pf(Peano.AddMonotoneBoth), "ta", "tb", "tb", "tb"), conj(aBelowB, spec(pf(Peano.Reflexive), "tb")))
              val rTwice = mpn(spec(pf(Peano.BelowThenAtMost), "r", "NUM_ADD ta tb", "NUM_ADD tb tb"), conj(rBelowSum, twice))
              midAt("pb", pbBelow, "tb", bHolds, bSmaller, bAtMost, rTwice)
            },
            bBelowA => {
              val twice = mpn(spec(pf(Peano.AddMonotoneBoth), "ta", "ta", "tb", "ta"), conj(spec(pf(Peano.Reflexive), "ta"), bBelowA))
              val rTwice = mpn(spec(pf(Peano.BelowThenAtMost), "r", "NUM_ADD ta tb", "NUM_ADD ta ta"), conj(rBelowSum, twice))
              midAt("pa", paBelow, "ta", aHolds, aSmaller, aAtMost, rTwice)
            }
          )
        }
      }
    }

    /* ------------------------------------------------------- the theorem */

    /** [[ExpanderPigeonhole.ExpanderWidth]]. */
    lazy val width: Kernel.Thm = {
      val inputsText = s"!j:num. NUM_LT j inputs ==> $Clause"
      val positive = assume("NUM_LT ZERO r")
      val matchable = assume(Matchable)
      val inputs = assume(inputsText)
      val refutation = assume("RES_REFUTATION k v s inputs m")
      val halves = openDefinition(Resolving.Refutation, refutation, "k", "v", "s", "inputs", "m")
      val justified = left(halves)
      val goal = prop("?j:num. NUM_LT j m /\\ NUM_LE w (k j)")
      def big(z: String): String = s"(NUM_LT $z m /\\ ~${measured(z, "r")})"

      // The empty clause is a step no set of `r` pigeons implies, so there is a first one.
      val least = opened(right(halves), "e") { empty =>
        val notMeasured = refuted(prop(measured("e", "r"))) { at =>
          opened(at, "sx") { chosen =>
            absurdN(mpn(inst(emptyUnimplied, "j" -> "e"), right(empty), matchable, left(chosen)), right(chosen))
          }
        }
        val instance = spec(pf(Peano.LeastNumber), s"\\z:num. ${big("z")}")
        val (some, _) = logic.destImp(instance.conclusion).getOrElse(refuse("an implication", instance.conclusion))
        mpn(instance, wit(some, List("e"), conj(left(empty), notMeasured)))
      }

      val result = opened(least, "j") { body =>
        val jBig = left(body)
        val minimal = right(body)
        val jBelow = left(jBig)
        val notMeasured = right(jBig)
        val notInput = refuted(prop("NUM_LT j inputs")) { isInput =>
          absurdN(notMeasured, mpn(inputMeasured, positive, mpn(spec(inputs, "j"), isInput)))
        }
        val justification = openDefinition(Resolving.JustifiedName, mpn(spec(justified, "j"), jBelow), "k", "v", "s", "inputs", "j")
        val midGoal = prop(s"?j1:num. ${mid("j1")}")
        val midExists = byDisjunction(justification)(
          isInput => exFalso(midGoal, absurd(notInput, isInput)),
          resolvent => opened(resolvent, "pa") { afterA =>
            opened(afterA, "pb") { afterB =>
              opened(afterB, "x") { step => descend(step, jBelow, minimal, notMeasured) }
            }
          }
        )
        opened(midExists, "j1") { midBody => wit(goal, List("j1"), conj(left(midBody), wide(midBody))) }
      }
      generalised(discharged(result, "NUM_LT ZERO r", Matchable, Expanding, inputsText, "RES_REFUTATION k v s inputs m"),
        "np", "n", "adj", "r", "w", "k", "v", "s", "inputs", "m")
    }
  }
}
