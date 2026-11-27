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
 * turns a true formula into a provable one is completeness, proved once and in this file: for the
 * closed bounded formulas, [[Truth.ProvesBounded]], which also refutes the false ones, and for the
 * closed Sigma-1 sentences, [[Truth.ProvesSigma]], which proves the true ones and nothing more.
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
 * == The representations by doubling ==
 *
 * `NUM_TRI_GRAPH` is the code of `v0 + v0 = v1 * S v1`, and [[Truth.TriangleGraphTrue]] says it
 * holds at an environment exactly when `e 0 = NUM_TRI (e 1)`. Variable `0` is the value and
 * variables `1`, `2` the arguments in order, which is the convention every representation follows.
 * It is quantifier-free because `NUM_TRI n` is the unique solution of `2x = n(n+1)`, so the
 * division the closed form wants is never written; that is the reason `Numbering` defined the
 * triangle by recursion rather than as a quotient, spent a second time.
 *
 * The pairing and the constructor are spent the same way, a third time. `NUM_PAIR a b` is
 * `NUM_TRI (a + b) + a`, so twice the pair is `(a + b) * S (a + b) + (a + a)`, and twice
 * `NUM_CODE t p`, which is the successor of a pair, is that number's second successor. Each graph
 * is therefore one equation, `v0 + v0 = ...`, with no quantifier: `NUM_PAIR_GRAPH` and
 * `NUM_CODE_GRAPH`. `docs/adr/0040` predicted bounded quantifiers for the pairing; the doubling
 * makes them unnecessary. The three are one proof, `graphByDoubling`, which needs only the doubled
 * closed form of the function and the cancellation of a doubling.
 *
 * == The projections, where the bounded quantifier first appears ==
 *
 * `NUM_FST_GRAPH` and `NUM_SND_GRAPH` say that `v0` is a component of `v1` by a universal below
 * `v1`: no other component below the argument makes it the pair, so the argument does. The doubling
 * is spent a fourth time inside the body, and what is new is that the bound is a variable, which
 * [[Truth.TrueAllBelowVariable]] reads, and that the pairing has to be onto, which
 * `Numbering.NUM_PAIR_ONTO` says: a projection is chosen, and at a number nobody has shown to be a
 * pair it says nothing. [[Truth.FirstGraphTrue]] has the argument.
 *
 * What these facts do NOT say, since this is the sentence a reader would round up: that PA proves
 * the graph at the numerals of a value and its arguments. What carries a graph's truth there is
 * [[Truth.ProvesBoundedInstance]], once for every arity: the numerals of `s 0`, `s 1`, ... put for
 * the graph's variables by [[Truth.InstanceName]], provable when the graph is true at `s` and
 * refutable when it is false. A representation reaches it by discharging three premises at its
 * code, that it is a formula, bounded, and has its free variables below the arity, and
 * [[Truth.TriangleRepresented]], [[Truth.PairRepresented]] and [[Truth.CodeRepresented]] are the
 * graphs by doubling having done so, and [[Truth.FirstRepresented]] and
 * [[Truth.SecondRepresented]] the two projections: the walk of their codes that discharges the premises is `Representing`, which
 * reads equations, negations, implications and the bounded universal, sees through the other
 * abbreviations of `Language`, and refuses any other code by name.
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

  /** The code of `v0 + v0 = (v1 + v2) * S (v1 + v2) + (v1 + v1)`, the graph of `NUM_PAIR`. */
  val PairGraphName: String = "NUM_PAIR_GRAPH"

  /** The code of `v0 + v0 = S (S ((v1 + v2) * S (v1 + v2) + (v1 + v1)))`, the graph of `NUM_CODE`. */
  val CodeGraphName: String = "NUM_CODE_GRAPH"

  /**
   * The code of `(!v2. v2 < v1 ==> ~(v1 + v1 = 2 * NUM_PAIR v0 v2)) ==> v1 + v1 = 2 * NUM_PAIR v0 v1`,
   * the graph of `NUM_FST`, each doubled pair written as its closed form, as the pairing's graph
   * writes it.
   *
   * The first formula of the four with a quantifier, and it is bounded by the argument: `v0` is the
   * first component of `v1` when some `b` at most `v1` makes `v1` the pair of `v0` and `b`, since a
   * component is never above its pair. "Some `b` below `v1`, or `b` is `v1`" is written as the
   * implication from "no `b` below" to the case `b = v1`, which is the same in a classical reading
   * and needs no disjunction. The argument is the bound, and not its successor, because the class
   * admits a variable or a numeral as a bound and no other term.
   */
  val FirstGraphName: String = "NUM_FST_GRAPH"

  /** The same for `NUM_SND`, with the quantified component in the first slot: `v0` second of `v1`. */
  val SecondGraphName: String = "NUM_SND_GRAPH"

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
   * `|- !a b. NUM_PAIR a b + NUM_PAIR a b = (a + b) * SUC (a + b) + (a + a)`
   *
   * Twice the pair, with the triangle's doubling spent on its first summand: the closed form
   * [[PairGraphTrue]] stands on.
   */
  val PairDoubled: String = "NUM_PAIR_DOUBLE"

  /**
   * `|- !e. NUM_TRUE NUM_PAIR_GRAPH e = (e 0 = NUM_PAIR (e 1) (e 2))`
   *
   * The graph of the pairing, as the truth of one equation of the object language. The
   * left-to-right half is the one to check, as for the triangle: it is the cancellation of a
   * doubling, and it is what makes the graph single-valued.
   */
  val PairGraphTrue: String = "NUM_PAIR_GRAPH_TRUE"

  /**
   * `|- !t p. NUM_CODE t p + NUM_CODE t p = SUC (SUC ((t + p) * SUC (t + p) + (t + t)))`
   *
   * Twice the code, which is the successor of a pair: two successors outside [[PairDoubled]].
   */
  val CodeDoubled: String = "NUM_CODE_DOUBLE"

  /** `|- !e. NUM_TRUE NUM_CODE_GRAPH e = (e 0 = NUM_CODE (e 1) (e 2))`, the same for the constructor. */
  val CodeGraphTrue: String = "NUM_CODE_GRAPH_TRUE"

  /**
   * `|- !e. NUM_TRUE NUM_FST_GRAPH e = (e 0 = NUM_FST (e 1))`
   *
   * The graph is evaluated through [[TrueAllBelowVariable]], and what is left is that "no `b` below
   * `e 1` makes `e 1` the pair of `e 0` and `b`, so `e 1` does" holds exactly when `e 0` is the first
   * component. From right to left the pair `e 1` is, by `NUM_PAIR_ONTO`, has `e 0` first and some
   * `b` second with `b` at most `e 1`: below it the premise is refuted at `b`, and at it the
   * conclusion is the doubled closed form. From left to right, either half reaching an equation
   * between `e 1` doubled and a doubled pair cancels the doubling and projects. This is where the
   * pairing being onto is spent, and the only place: at a number not known to be a pair,
   * `NUM_FST` says nothing.
   */
  val FirstGraphTrue: String = "NUM_FST_GRAPH_TRUE"

  /** `|- !e. NUM_TRUE NUM_SND_GRAPH e = (e 0 = NUM_SND (e 1))`, the same proof at the other slot. */
  val SecondGraphTrue: String = "NUM_SND_GRAPH_TRUE"

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
   * `NUM_BOUNDED p` says every quantifier in `p` is bounded: `p` is built from equations by
   * negation, implication and the bounded universal `!i. i < b ==> q`, where `b` is a variable
   * other than `v_i` and the order's own witness, or a numeral. The class completeness is proved
   * for next, an existential below being written as the negation of a universal below.
   *
   * **The bound is a variable or a numeral, and not any term.** Putting a numeral for a variable
   * keeps the class, since a variable bound becomes a numeral or stays a variable, and a closed
   * formula of the class has every bound a numeral, which is the form the four facts about a
   * quantifier below a numeral in `Deduction` consume. A bound written as a term would first have
   * to be brought to a numeral inside PA under the quantifier, and what is lost is nothing a
   * formula with one unbounded existential more cannot say: `?y. y = t /\ !i. i < y ==> q`.
   *
   * Like `NUM_GROUND` it says nothing about the formula being well formed; a statement about it
   * asks for `NUM_FORM` beside it.
   */
  val BoundedName: String = "NUM_BOUNDED"

  /** `|- !a b. NUM_BOUNDED (a = b) = T`, coded: every equation is bounded. */
  val BoundedEquality: String = "NUM_BOUNDED_EQ"

  /** `|- !p. NUM_BOUNDED ~p = NUM_BOUNDED p`, coded. */
  val BoundedNegation: String = "NUM_BOUNDED_NOT"

  /** `|- !p q. NUM_BOUNDED (p ==> q) = (NUM_BOUNDED p /\ NUM_BOUNDED q)`, coded. */
  val BoundedImplication: String = "NUM_BOUNDED_IMP"

  /**
   * `|- !z i t p. NUM_BOUNDED (NUM_ALL_BELOW z i t p) =`
   *   `(~(z = i) /\ ((?j. t = v_j /\ ~(j = i) /\ ~(j = z)) \/ (?n. t = NUM_NUMERAL n)) /\`
   *   `NUM_BOUNDED p)`
   *
   * The quantifier the class admits. The order's witness must differ from the quantified index,
   * or `?z. i + S z = t` would bind the `i` it is about; a variable bound must differ from both,
   * or it would be bound by one of them. Any other universal is not in the class.
   */
  val BoundedAllBelow: String = "NUM_BOUNDED_ALL_BELOW"

  /**
   * `|- !j q. NUM_BOUNDED (!v_j. q) ==> ?z t p. (!v_j. q) = NUM_ALL_BELOW z j t p`, coded.
   *
   * A universal in the class is a universal below: the reading an induction over the class needs
   * at a quantifier, since the code it is handed is `NUM_CODE 8 (NUM_PAIR j q)` and the facts
   * about a quantifier below are stated at `NUM_ALL_BELOW`. With [[BoundedAllBelow]] at what it
   * yields, it also gives the conditions on the witness and the bound.
   */
  val BoundedUniversal: String = "NUM_BOUNDED_ALL"

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
   * `|- !p q. NUM_FORM (p ==> q) ==> NUM_FORM p /\ NUM_FORM q`, coded.
   *
   * The converse of `Language`'s introduction rule for an implication, read off `NUM_FORM`'s cases:
   * a formula at tag `7` was built by that rule, the other three tags being distinct numerals.
   * It is here rather than beside the introduction because a bounded universal is the first thing
   * that needs it: the body of `NUM_ALL_BELOW z i t p` sits under an implication, and nothing about
   * `p` follows from the universal being a formula until the implication is taken apart.
   */
  val FormImplicationParts: String = "NUM_FORM_IMP_PARTS"

  /**
   * `|- !x k p. NUM_FORM p ==> NUM_BOUNDED p ==> NUM_BOUNDED (p[numeral k/x])`
   *
   * The class survives a numeral put for a variable, which is what lets the completeness induction
   * take a bounded universal's instances as bounded formulas again. By strong induction on the code.
   * At a universal the substitution either stops, at its own index, or goes under; under, the bound
   * is where the choice of the class shows: a variable bound becomes the numeral when it is `x` and
   * stays a variable otherwise, and a numeral bound is left alone, being closed. A bound allowed to be
   * any term would come out of this as any term, which the class does not hold, and this is why the
   * class names the two.
   */
  val BoundedAtNumeral: String = "NUM_BOUNDED_SUBST_NUMERAL"

  /**
   * `NUM_RANK p` counts the connectives and quantifiers of the formula `p`: an equation is `0`, a
   * negation and a universal one more than their body, an implication one more than its two
   * parts together, and a code that is no formula `0`.
   *
   * It is the measure the completeness induction descends on, and the code is not, because an
   * instance of a bounded universal has a numeral where the universal has a variable and its code
   * is larger: the induction from a universal to its instances goes up in the code and down in
   * the rank. What makes that work is [[RankAtNumeral]], the rank reading only the shape the
   * substitution keeps.
   */
  val RankName: String = "NUM_RANK"

  /** `|- !a b. NUM_RANK (a = b) = 0`, coded. */
  val RankEquality: String = "NUM_RANK_EQ"

  /** `|- !p. NUM_RANK ~p = SUC (NUM_RANK p)`, coded. */
  val RankNegation: String = "NUM_RANK_NOT"

  /** `|- !p q. NUM_RANK (p ==> q) = SUC (NUM_RANK p + NUM_RANK q)`, coded. */
  val RankImplication: String = "NUM_RANK_IMP"

  /** `|- !j p. NUM_RANK (!v_j. p) = SUC (NUM_RANK p)`, coded. */
  val RankUniversal: String = "NUM_RANK_ALL"

  /**
   * `|- !x k p. NUM_FORM p ==> NUM_RANK (p[numeral k/x]) = NUM_RANK p`
   *
   * A numeral put for a variable leaves the rank alone: the substitution changes terms and the
   * rank reads none, and where it stops at a universal over `x` it changes nothing at all. By
   * strong induction on the code, each case two clauses of the substitution and the rank and the
   * hypothesis at the parts.
   */
  val RankAtNumeral: String = "NUM_RANK_SUBST_NUMERAL"

  /**
   * `|- !x k t. NUM_TERM t ==> !w. NUM_FREE_TERM w (t[numeral k/x]) ==> NUM_FREE_TERM w t /\ ~(w = x)`
   *
   * A numeral put for a variable brings no variable in and takes that one out: what is free after
   * it was free before and is not `x`. By strong induction on the code; the variable case is the
   * only one with content, where `v_x` becomes a numeral and a numeral is closed.
   *
   * It and [[FreeFormAtNumeral]] are here rather than in `Language`, beside the substitution and
   * freeness they are about, because completeness is the first thing to need them: an instance of
   * a closed universal is closed only if this holds.
   */
  val FreeTermAtNumeral: String = "NUM_FREE_TERM_SUBST_NUMERAL"

  /**
   * `|- !x k p. NUM_FORM p ==> !w. NUM_FREE_FORM w (p[numeral k/x]) ==> NUM_FREE_FORM w p /\ ~(w = x)`
   *
   * [[FreeTermAtNumeral]] for formulas. At a universal over `x` the substitution stops, and a
   * variable free in it is not `x` because the universal binds `x`; at a universal over another
   * index the hypothesis at the body applies unless the universal binds the variable asked about.
   */
  val FreeFormAtNumeral: String = "NUM_FREE_FORM_SUBST_NUMERAL"

  /**
   * `|- !e z i n. ~(z = i) ==> NUM_TRUE (NUM_LESS z v_i (numeral n)) e = e i < n`
   *
   * The order's code is true exactly where the order holds, for a variable below a numeral. The
   * code is `?v_z. v_i + S v_z = n` written as `~!v_z. ~...`, so the truth is the double negation
   * of a universal, and `NUM_ADD_SHIFT` moves the successor to where `NUM_LT`'s definition has it.
   * The witness must not be `i`, or the quantifier would bind the variable it is about.
   */
  val TrueLessNumeral: String = "NUM_TRUE_LESS_NUMERAL"

  /**
   * `|- !e z i n p. ~(z = i) ==>`
   *   `NUM_TRUE (NUM_ALL_BELOW z i (numeral n) p) e = !m. m < n ==> NUM_TRUE p e[i := m]`
   *
   * A universal below a numeral is true when its body is true at every value below, which is the
   * reading the completeness induction takes to the instances: with `NUM_TRUE_SUBST_NUMERAL` the
   * body at `e[i := m]` is the instance at the numeral of `m`.
   */
  val TrueAllBelowNumeral: String = "NUM_TRUE_ALL_BELOW_NUMERAL"

  /**
   * `|- !e z i k. ~(z = i) ==> ~(k = z) ==> NUM_TRUE (NUM_LESS z v_i v_k) e = e i < e k`
   *
   * [[TrueLessNumeral]] below a variable rather than a numeral, which is what a formula with free
   * variables is read through before any numeral has been put for them: the graph of a projection
   * bounds its quantifier by its argument. The bound must not be the witness, or the existential
   * the order abbreviates would bind it.
   */
  val TrueLessVariable: String = "NUM_TRUE_LESS_VAR"

  /**
   * `|- !e z i k p. ~(z = i) ==> ~(k = i) ==> ~(k = z) ==>`
   *   `NUM_TRUE (NUM_ALL_BELOW z i v_k p) e = !m. m < e k ==> NUM_TRUE p e[i := m]`
   *
   * [[TrueAllBelowNumeral]] below a variable, under the three conditions [[BoundedAllBelow]] puts on
   * a variable bound, so that every universal of the bounded class has a reading.
   */
  val TrueAllBelowVariable: String = "NUM_TRUE_ALL_BELOW_VAR"

  /**
   * `|- !e p. NUM_FORM p ==> NUM_BOUNDED p ==> (!w. ~(NUM_FREE_FORM w p)) ==>`
   *   `(NUM_TRUE p e ==> NUM_PROV p) /\ (~(NUM_TRUE p e) ==> NUM_PROV ~p)`
   *
   * PA decides every closed formula of the bounded class: a true one is provable and a false one
   * has a provable negation. This is the completeness the second incompleteness theorem rests
   * on, for the formulas a bounded decoding of provability is written in.
   *
   * By strong induction on [[RankName]], at a fixed environment. An equation is
   * [[ProvesTrueEquation]] or [[ProvesFalseEquation]], its terms being closed because the
   * formula is; a negation and an implication are what [[ProvesGround]] does with them. A
   * universal is in the class only below a variable or a numeral, and a variable bound would be
   * free in it, so it is below a numeral; its truth is its body's at every value below
   * ([[TrueAllBelowNumeral]]), which is its instance's truth at the numeral of that value
   * (`NUM_TRUE_SUBST_NUMERAL`). Each instance is a formula, in the class, closed
   * ([[FreeFormAtNumeral]]) and of the body's rank ([[RankAtNumeral]]), which is below the
   * universal's, so the hypothesis decides it, and `Deduction`'s two facts about a universal
   * below a numeral assemble the instances.
   */
  val ProvesBounded: String = "NUM_PROV_BOUNDED"

  /**
   * `NUM_SIGMA n p`: `p` is `n` unbounded existentials in front of a formula of the bounded class.
   *
   * A primitive recursion on `n` rather than a recursion on the code: the class is what a prefix of
   * existentials does to [[BoundedName]], and the induction that consumes it goes down the prefix
   * one quantifier at a time. The formula at the bottom is asked to be a formula as well as
   * bounded, so that every member of the class is a formula ([[SigmaForm]]) without an inversion
   * of `NUM_FORM` under the existential. A sentence is Sigma-1 when it is in the class at some
   * `n`, which is the form the decoding of provability is written in.
   */
  val SigmaName: String = "NUM_SIGMA"

  /** `|- !p. NUM_SIGMA 0 p = NUM_FORM p /\ NUM_BOUNDED p`. */
  val SigmaZero: String = "NUM_SIGMA_ZERO"

  /** `|- !n p. NUM_SIGMA (SUC n) p = ?j q. p = NUM_EXISTS j q /\ NUM_SIGMA n q`. */
  val SigmaSuccessor: String = "NUM_SIGMA_SUC"

  /** `|- !n p. NUM_SIGMA n p ==> NUM_FORM p`, by induction on `n` with `NUM_FORM_EXISTS`. */
  val SigmaForm: String = "NUM_SIGMA_FORM"

  /**
   * `|- !n x k p. NUM_SIGMA n p ==> NUM_SIGMA n (p[numeral k/x])`
   *
   * The class keeps its members when a numeral is put for a variable, with the same number of
   * existentials. By induction on `n`: at zero it is [[BoundedAtNumeral]] and the substitution
   * keeping formulas; at an existential over `x` the substitution stops, and over another index it
   * goes under and the hypothesis takes the body.
   */
  val SigmaAtNumeral: String = "NUM_SIGMA_SUBST_NUMERAL"

  /**
   * `|- !e j p. NUM_TRUE (NUM_EXISTS j p) e = ?n. NUM_TRUE p e[j := n]`
   *
   * The existential is the negation of a universal of a negation, and its truth is read through
   * the three clauses and the classical equivalence of `~!n. ~P n` with `?n. P n`.
   */
  val TrueExists: String = "NUM_TRUE_EXISTS"

  /**
   * `|- !n e p. NUM_SIGMA n p ==> (!w. ~(NUM_FREE_FORM w p)) ==> NUM_TRUE p e ==> NUM_PROV p`
   *
   * Sigma-1 completeness: PA proves every true closed sentence of the class. Only the true half,
   * unlike [[ProvesBounded]]: a false existential has no witness to refute, and refuting it would
   * need every instance refuted, of which there are infinitely many.
   *
   * By induction on `n`, at a fixed environment. At zero the sentence is a closed formula of the
   * bounded class and [[ProvesBounded]] proves it. At `SUC n` it is `NUM_EXISTS j q`, true, so
   * [[TrueExists]] gives a value `m` at which `q` is true with `j` sent to it, which is the truth of
   * the instance `q[numeral m/j]` (`NUM_TRUE_SUBST_NUMERAL`). The instance is in the class at `n`
   * ([[SigmaAtNumeral]]) and closed, by [[FreeFormAtNumeral]] and the existential binding `j`, so
   * the hypothesis proves it, and `NUM_PROV_EXISTS_INTRO` introduces the existential at the
   * numeral.
   */
  val ProvesSigma: String = "NUM_PROV_SIGMA"

  /**
   * `NUM_INST n s p`: `p` with the numeral of `s i` put for `v_i` at every `i` below `n`.
   *
   * What a representation is asked about at concrete arguments: its graph has its value at
   * variable `0` and its arguments at `1`, `2`, ..., so the sentence PA is to prove is the graph
   * with a numeral at each of those, and an environment `s` names the numbers. A primitive
   * recursion on `n` rather than one constant per arity, so that the bridge from truth to
   * provability is proved once for every graph however many arguments it has. The substitutions
   * are made from variable `0` up; since a numeral is closed, the order is invisible to the truth
   * ([[InstanceTrue]]), and it is fixed only so that the constant has one definition.
   */
  val InstanceName: String = "NUM_INST"

  /** `|- !s p. NUM_INST ZERO s p = p`. */
  val InstanceZero: String = "NUM_INST_ZERO"

  /** `|- !n s p. NUM_INST (SUC n) s p = NUM_SUBST_FORM n (NUM_NUMERAL (s n)) (NUM_INST n s p)`. */
  val InstanceSuccessor: String = "NUM_INST_SUC"

  /** `|- !n s p. NUM_FORM p ==> NUM_FORM (NUM_INST n s p)`, each substitution keeping formulas. */
  val InstanceForm: String = "NUM_INST_FORM"

  /**
   * `|- !n s p. NUM_FORM p ==> NUM_BOUNDED p ==> NUM_BOUNDED (NUM_INST n s p)`, by induction on
   * `n` with [[BoundedAtNumeral]] at each step and [[InstanceForm]] for the formula it asks for.
   */
  val InstanceBounded: String = "NUM_INST_BOUNDED"

  /**
   * `|- !m n s p. NUM_SIGMA m p ==> NUM_SIGMA m (NUM_INST n s p)`, with [[SigmaAtNumeral]] at each
   * step: the number of existentials in front does not move.
   */
  val InstanceSigma: String = "NUM_INST_SIGMA"

  /**
   * `|- !n s p. NUM_FORM p ==> !w. NUM_FREE_FORM w (NUM_INST n s p) ==> NUM_FREE_FORM w p /\ ~(w < n)`
   *
   * What is free after the substitutions was free before and is not one of the variables
   * substituted: [[FreeFormAtNumeral]] at each step, and `NUM_LT_SUC_CASES` to read `~(w < SUC n)`
   * off `~(w < n)` and `~(w = n)`. A formula whose free variables are all below `n` is therefore
   * closed once instantiated, which is what completeness asks for.
   */
  val InstanceFree: String = "NUM_INST_FREE"

  /**
   * `|- !n s p. NUM_FORM p ==> !e. NUM_TRUE (NUM_INST n s p) e = NUM_TRUE p (\j. COND (j < n) (s j) (e j))`
   *
   * The instance is true at `e` exactly when `p` is true at the environment that reads `s` below
   * `n` and `e` from `n` up. By induction on `n` with [[TrueAtNumeral]] at each step, the induction
   * hypothesis taken at the environment that step has updated. The two environments are equal at
   * each point by a case split on whether it is below `n` or is `n`, and the abstraction rule closes
   * them. At zero the environment is `\j. COND (j < 0) (s j) (e j)`, equal to `\j. e j`, and that is
   * `e` only by `ETA`: this fact and the two below rest on it, where the truth facts before them do
   * not.
   */
  val InstanceTrue: String = "NUM_INST_TRUE"

  /**
   * `|- !n s p. NUM_FORM p ==> NUM_BOUNDED p ==> (!w. NUM_FREE_FORM w p ==> w < n) ==>`
   *   `(NUM_TRUE p s ==> NUM_PROV (NUM_INST n s p)) /\`
   *   `(~(NUM_TRUE p s) ==> NUM_PROV (NUM_CODE 6 (NUM_INST n s p)))`
   *
   * The bridge every bounded representation crosses: a formula of the class whose free variables
   * are below `n`, true at `s`, is provable in PA with the numerals of `s 0`, ..., `s (n - 1)` put
   * for its variables, and false at `s`, refutable there. For a graph, `s 0` is the value and the
   * rest the arguments. It is [[ProvesBounded]] at the instance, which is a formula
   * ([[InstanceForm]]), in the class ([[InstanceBounded]]) and closed ([[InstanceFree]]), and whose
   * truth at `s` is `p`'s at `\j. COND (j < n) (s j) (s j)` ([[InstanceTrue]]), which is `s`.
   */
  val ProvesBoundedInstance: String = "NUM_PROV_BOUNDED_INST"

  /**
   * `|- !m n s p. NUM_SIGMA m p ==> (!w. NUM_FREE_FORM w p ==> w < n) ==> NUM_TRUE p s ==>`
   *   `NUM_PROV (NUM_INST n s p)`
   *
   * The same bridge for a Sigma-1 formula, through [[ProvesSigma]] and [[InstanceSigma]], and with
   * only its true half, as there.
   */
  val ProvesSigmaInstance: String = "NUM_PROV_SIGMA_INST"

  /**
   * `|- !s. (s 0 = NUM_TRI (s 1) ==> NUM_PROV (NUM_INST 2 s NUM_TRI_GRAPH)) /\`
   *   `(~(s 0 = NUM_TRI (s 1)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 2 s NUM_TRI_GRAPH)))`
   *
   * The triangle is represented in PA: at every point, its graph with the numerals of `s 0` and
   * `s 1` put for its variables is provable when `s 0` is the triangle of `s 1` and refutable when
   * it is not. [[ProvesBoundedInstance]] at the graph, whose three premises, a formula, in the
   * bounded class and with its free variables below two, are each shown by walking its code, and
   * whose truth is [[TriangleGraphTrue]]. The two below are the same proof at three variables.
   */
  val TriangleRepresented: String = "NUM_TRI_REPR"

  /** [[TriangleRepresented]] for the pairing, at three variables, through [[PairGraphTrue]]. */
  val PairRepresented: String = "NUM_PAIR_REPR"

  /** [[TriangleRepresented]] for the constructor, at three variables, through [[CodeGraphTrue]]. */
  val CodeRepresented: String = "NUM_CODE_REPR"

  /** [[CodeRepresented]] for `NUM_FST`: the first quantified graph to reach the bridge. */
  val FirstRepresented: String = "NUM_FST_REPR"

  /** The same for `NUM_SND`. */
  val SecondRepresented: String = "NUM_SND_REPR"

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

  /**
   * `(v1 + v2) * S (v1 + v2) + (v1 + v1)`, coded: twice the pair of `v1` and `v2`, the right side
   * both [[PairGraphText]] and [[CodeGraphText]] are written over. Built from named parts because
   * it is three levels deep and `v1 + v2` occurs twice, which is easier to check named than nested.
   */
  private val PairDoubledText: String = doubledPairText(1, 2)

  /**
   * `(v_a + v_b) * S (v_a + v_b) + (v_a + v_a)`, coded: twice the pair of `v_a` and `v_b`, which
   * [[PairDoubledText]] is at `1` and `2` and the projections' graphs are at the variables they
   * read.
   */
  private def doubledPairText(a: Int, b: Int): String = {
    val sum = s"(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 $a) (NUM_CODE 0 $b)))"
    val product = s"(NUM_CODE 4 (NUM_PAIR $sum (NUM_CODE 2 $sum)))"
    val first = s"(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 $a) (NUM_CODE 0 $a)))"
    s"(NUM_CODE 3 (NUM_PAIR $product $first))"
  }

  /** `v1 + v1`, coded: twice the argument a projection is read at. */
  private val ArgumentDoubledText: String = "(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 0 1)))"

  /**
   * `(!v2. v2 < v1 ==> ~(v1 + v1 = 2 * NUM_PAIR v_a v_b)) ==> v1 + v1 = 2 * NUM_PAIR v_a' v_b'`,
   * coded, with the quantified component at `v2` in the body and at `v1` in the conclusion; the
   * order's witness is `v3`. The graph of a projection, `left` saying which slot `v0` is.
   */
  private def projectionGraphText(left: Boolean): String = {
    def doubled(other: Int): String = if (left) doubledPairText(0, other) else doubledPairText(other, 0)
    val body = s"(NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR $ArgumentDoubledText ${doubled(2)})))"
    val conclusion = s"(NUM_CODE 5 (NUM_PAIR $ArgumentDoubledText ${doubled(1)}))"
    s"NUM_CODE 7 (NUM_PAIR (NUM_ALL_BELOW 3 2 (NUM_CODE 0 1) $body) $conclusion)"
  }

  /** [[FirstGraphName]]'s code: `v0` is the first component of `v1`. */
  val FirstGraphText: String = projectionGraphText(left = true)

  /** [[SecondGraphName]]'s code: `v0` is the second component of `v1`. */
  val SecondGraphText: String = projectionGraphText(left = false)

  /** `v0 + v0`, coded: the left side of every graph by doubling. */
  private val ValueDoubledText: String = "(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0)))"

  /** `v0 + v0 = (v1 + v2) * S (v1 + v2) + (v1 + v1)`, coded. */
  val PairGraphText: String = s"NUM_CODE 5 (NUM_PAIR $ValueDoubledText $PairDoubledText)"

  /** `v0 + v0 = S (S ((v1 + v2) * S (v1 + v2) + (v1 + v1)))`, coded. */
  val CodeGraphText: String =
    s"NUM_CODE 5 (NUM_PAIR $ValueDoubledText (NUM_CODE 2 (NUM_CODE 2 $PairDoubledText)))"

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
    PairDoubled ->
      ("!a:num b:num. NUM_ADD (NUM_PAIR a b) (NUM_PAIR a b) = " +
        "NUM_ADD (NUM_MUL (NUM_ADD a b) (SUC (NUM_ADD a b))) (NUM_ADD a a)"),
    PairGraphTrue -> "!e:num -> num. NUM_TRUE NUM_PAIR_GRAPH e = (e 0 = NUM_PAIR (e 1) (e 2))",
    CodeDoubled ->
      ("!t:num p:num. NUM_ADD (NUM_CODE t p) (NUM_CODE t p) = " +
        "SUC (SUC (NUM_ADD (NUM_MUL (NUM_ADD t p) (SUC (NUM_ADD t p))) (NUM_ADD t t)))"),
    CodeGraphTrue -> "!e:num -> num. NUM_TRUE NUM_CODE_GRAPH e = (e 0 = NUM_CODE (e 1) (e 2))",
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
    BoundedEquality -> "!a:num. !b:num. NUM_BOUNDED (NUM_CODE 5 (NUM_PAIR a b)) = T",
    BoundedNegation -> "!p:num. NUM_BOUNDED (NUM_CODE 6 p) = NUM_BOUNDED p",
    BoundedImplication ->
      "!p:num. !q:num. NUM_BOUNDED (NUM_CODE 7 (NUM_PAIR p q)) = (NUM_BOUNDED p /\\ NUM_BOUNDED q)",
    BoundedAllBelow ->
      ("!z:num. !i:num. !t:num. !p:num. NUM_BOUNDED (NUM_ALL_BELOW z i t p) = " +
        "(~(z = i) /\\ ((?j:num. t = NUM_CODE 0 j /\\ ~(j = i) /\\ ~(j = z)) \\/ " +
        "(?n:num. t = NUM_NUMERAL n)) /\\ NUM_BOUNDED p)"),
    BoundedUniversal ->
      ("!j:num. !q:num. NUM_BOUNDED (NUM_CODE 8 (NUM_PAIR j q)) ==> " +
        "?z:num t:num p:num. NUM_CODE 8 (NUM_PAIR j q) = NUM_ALL_BELOW z j t p"),
    ValueAtNumeral ->
      ("!x:num k:num t:num. NUM_TERM t ==> !e:num -> num. " +
        "NUM_VALUE (NUM_SUBST_TERM x (NUM_NUMERAL k) t) e = NUM_VALUE t (\\j:num. COND (j = x) k (e j))"),
    TrueAtNumeral ->
      ("!x:num k:num p:num. NUM_FORM p ==> !e:num -> num. " +
        "NUM_TRUE (NUM_SUBST_FORM x (NUM_NUMERAL k) p) e = NUM_TRUE p (\\j:num. COND (j = x) k (e j))"),
    FormImplicationParts ->
      "!p:num q:num. NUM_FORM (NUM_CODE 7 (NUM_PAIR p q)) ==> NUM_FORM p /\\ NUM_FORM q",
    BoundedAtNumeral ->
      ("!x:num k:num p:num. NUM_FORM p ==> NUM_BOUNDED p ==> " +
        "NUM_BOUNDED (NUM_SUBST_FORM x (NUM_NUMERAL k) p)"),
    RankEquality -> "!a:num. !b:num. NUM_RANK (NUM_CODE 5 (NUM_PAIR a b)) = ZERO",
    RankNegation -> "!p:num. NUM_RANK (NUM_CODE 6 p) = SUC (NUM_RANK p)",
    RankImplication ->
      "!p:num. !q:num. NUM_RANK (NUM_CODE 7 (NUM_PAIR p q)) = SUC (NUM_ADD (NUM_RANK p) (NUM_RANK q))",
    RankUniversal -> "!j:num. !p:num. NUM_RANK (NUM_CODE 8 (NUM_PAIR j p)) = SUC (NUM_RANK p)",
    RankAtNumeral ->
      ("!x:num k:num p:num. NUM_FORM p ==> " +
        "NUM_RANK (NUM_SUBST_FORM x (NUM_NUMERAL k) p) = NUM_RANK p"),
    FreeTermAtNumeral ->
      ("!x:num k:num t:num. NUM_TERM t ==> !w:num. " +
        "NUM_FREE_TERM w (NUM_SUBST_TERM x (NUM_NUMERAL k) t) ==> NUM_FREE_TERM w t /\\ ~(w = x)"),
    FreeFormAtNumeral ->
      ("!x:num k:num p:num. NUM_FORM p ==> !w:num. " +
        "NUM_FREE_FORM w (NUM_SUBST_FORM x (NUM_NUMERAL k) p) ==> NUM_FREE_FORM w p /\\ ~(w = x)"),
    TrueLessNumeral ->
      ("!e:num -> num. !z:num i:num n:num. ~(z = i) ==> " +
        "NUM_TRUE (NUM_LESS z (NUM_CODE 0 i) (NUM_NUMERAL n)) e = e i < n"),
    TrueAllBelowNumeral ->
      ("!e:num -> num. !z:num i:num n:num p:num. ~(z = i) ==> " +
        "NUM_TRUE (NUM_ALL_BELOW z i (NUM_NUMERAL n) p) e = " +
        "(!m:num. m < n ==> NUM_TRUE p (\\j:num. COND (j = i) m (e j)))"),
    TrueLessVariable ->
      ("!e:num -> num. !z:num i:num k:num. ~(z = i) ==> ~(k = z) ==> " +
        "NUM_TRUE (NUM_LESS z (NUM_CODE 0 i) (NUM_CODE 0 k)) e = e i < e k"),
    TrueAllBelowVariable ->
      ("!e:num -> num. !z:num i:num k:num p:num. ~(z = i) ==> ~(k = i) ==> ~(k = z) ==> " +
        "NUM_TRUE (NUM_ALL_BELOW z i (NUM_CODE 0 k) p) e = " +
        "(!m:num. m < e k ==> NUM_TRUE p (\\j:num. COND (j = i) m (e j)))"),
    ProvesBounded ->
      ("!e:num -> num. !p:num. NUM_FORM p ==> NUM_BOUNDED p ==> (!w:num. ~(NUM_FREE_FORM w p)) ==> " +
        "(NUM_TRUE p e ==> NUM_PROV p) /\\ (~(NUM_TRUE p e) ==> NUM_PROV (NUM_CODE 6 p))"),
    SigmaZero -> "!p:num. NUM_SIGMA ZERO p = (NUM_FORM p /\\ NUM_BOUNDED p)",
    SigmaSuccessor ->
      "!n:num p:num. NUM_SIGMA (SUC n) p = (?j:num q:num. p = NUM_EXISTS j q /\\ NUM_SIGMA n q)",
    SigmaForm -> "!n:num p:num. NUM_SIGMA n p ==> NUM_FORM p",
    SigmaAtNumeral ->
      "!n:num x:num k:num p:num. NUM_SIGMA n p ==> NUM_SIGMA n (NUM_SUBST_FORM x (NUM_NUMERAL k) p)",
    TrueExists ->
      ("!e:num -> num. !j:num. !p:num. " +
        "NUM_TRUE (NUM_EXISTS j p) e = (?n:num. NUM_TRUE p (\\k:num. COND (k = j) n (e k)))"),
    ProvesSigma ->
      ("!n:num e:num -> num p:num. NUM_SIGMA n p ==> (!w:num. ~(NUM_FREE_FORM w p)) ==> " +
        "NUM_TRUE p e ==> NUM_PROV p"),
    InstanceZero -> "!s:num -> num. !p:num. NUM_INST ZERO s p = p",
    InstanceSuccessor ->
      ("!n:num. !s:num -> num. !p:num. " +
        "NUM_INST (SUC n) s p = NUM_SUBST_FORM n (NUM_NUMERAL (s n)) (NUM_INST n s p)"),
    InstanceForm -> "!n:num s:num -> num p:num. NUM_FORM p ==> NUM_FORM (NUM_INST n s p)",
    InstanceBounded ->
      "!n:num s:num -> num p:num. NUM_FORM p ==> NUM_BOUNDED p ==> NUM_BOUNDED (NUM_INST n s p)",
    InstanceSigma -> "!m:num n:num s:num -> num p:num. NUM_SIGMA m p ==> NUM_SIGMA m (NUM_INST n s p)",
    InstanceFree ->
      ("!n:num s:num -> num p:num. NUM_FORM p ==> !w:num. " +
        "NUM_FREE_FORM w (NUM_INST n s p) ==> NUM_FREE_FORM w p /\\ ~(w < n)"),
    InstanceTrue ->
      ("!n:num s:num -> num p:num. NUM_FORM p ==> !e:num -> num. " +
        "NUM_TRUE (NUM_INST n s p) e = NUM_TRUE p (\\j:num. COND (j < n) (s j) (e j))"),
    ProvesBoundedInstance ->
      ("!n:num s:num -> num p:num. NUM_FORM p ==> NUM_BOUNDED p ==> " +
        "(!w:num. NUM_FREE_FORM w p ==> w < n) ==> " +
        "(NUM_TRUE p s ==> NUM_PROV (NUM_INST n s p)) /\\ " +
        "(~(NUM_TRUE p s) ==> NUM_PROV (NUM_CODE 6 (NUM_INST n s p)))"),
    ProvesSigmaInstance ->
      ("!m:num n:num s:num -> num p:num. NUM_SIGMA m p ==> " +
        "(!w:num. NUM_FREE_FORM w p ==> w < n) ==> NUM_TRUE p s ==> NUM_PROV (NUM_INST n s p)"),
    TriangleRepresented ->
      ("!s:num -> num. (s 0 = NUM_TRI (s 1) ==> NUM_PROV (NUM_INST 2 s NUM_TRI_GRAPH)) /\\ " +
        "(~(s 0 = NUM_TRI (s 1)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 2 s NUM_TRI_GRAPH)))"),
    PairRepresented ->
      ("!s:num -> num. (s 0 = NUM_PAIR (s 1) (s 2) ==> NUM_PROV (NUM_INST 3 s NUM_PAIR_GRAPH)) /\\ " +
        "(~(s 0 = NUM_PAIR (s 1) (s 2)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 3 s NUM_PAIR_GRAPH)))"),
    CodeRepresented ->
      ("!s:num -> num. (s 0 = NUM_CODE (s 1) (s 2) ==> NUM_PROV (NUM_INST 3 s NUM_CODE_GRAPH)) /\\ " +
        "(~(s 0 = NUM_CODE (s 1) (s 2)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 3 s NUM_CODE_GRAPH)))"),
    FirstGraphTrue -> "!e:num -> num. NUM_TRUE NUM_FST_GRAPH e = (e 0 = NUM_FST (e 1))",
    SecondGraphTrue -> "!e:num -> num. NUM_TRUE NUM_SND_GRAPH e = (e 0 = NUM_SND (e 1))",
    FirstRepresented ->
      ("!s:num -> num. (s 0 = NUM_FST (s 1) ==> NUM_PROV (NUM_INST 2 s NUM_FST_GRAPH)) /\\ " +
        "(~(s 0 = NUM_FST (s 1)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 2 s NUM_FST_GRAPH)))"),
    SecondRepresented ->
      ("!s:num -> num. (s 0 = NUM_SND (s 1) ==> NUM_PROV (NUM_INST 2 s NUM_SND_GRAPH)) /\\ " +
        "(~(s 0 = NUM_SND (s 1)) ==> NUM_PROV (NUM_CODE 6 (NUM_INST 2 s NUM_SND_GRAPH)))")
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

  /**
   * The step of the bounded class, as text.
   *
   * The universal's guard is the whole shape `!X. NUM_LESS W v_X B ==> Z`, with `W` and `B` read
   * back out of the order's code, so a universal whose antecedent is anything else falls through
   * to `F`. Its branch recurses on `Z`, two codes and two pairs below `s`, which is the one place
   * a recursion here reaches further down than a payload's pair.
   */
  val BoundedStepText: String = {
    val index = "NUM_FST (NUM_PAYLOAD s)"
    val implication = "NUM_SND (NUM_PAYLOAD s)"
    val antecedent = s"NUM_FST (NUM_PAYLOAD ($implication))"
    val body = s"NUM_SND (NUM_PAYLOAD ($implication))"
    val witness = s"NUM_FST (NUM_PAYLOAD (NUM_PAYLOAD ($antecedent)))"
    val bound = s"NUM_SND (NUM_PAYLOAD (NUM_PAYLOAD (NUM_SND (NUM_PAYLOAD (NUM_PAYLOAD ($antecedent))))))"
    "\\f:num -> bool. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) T " +
      "(COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) (f (NUM_PAYLOAD s)) " +
      "(COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "(f (NUM_FST (NUM_PAYLOAD s)) /\\ f (NUM_SND (NUM_PAYLOAD s))) " +
      s"(COND (s = NUM_CODE 8 (NUM_PAIR ($index) (NUM_CODE 7 (NUM_PAIR " +
      s"(NUM_LESS ($witness) (NUM_CODE 0 ($index)) ($bound)) ($body))))) " +
      s"(~(($witness) = ($index)) /\\ " +
      s"((?j:num. ($bound) = NUM_CODE 0 j /\\ ~(j = ($index)) /\\ ~(j = ($witness))) \\/ " +
      s"(?n:num. ($bound) = NUM_NUMERAL n)) /\\ f ($body)) " +
      "F)))"
  }

  /** The step of the rank, as text, with the guards the truth's step has. */
  val RankStepText: String =
    "\\f:num -> num. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) ZERO " +
      "(COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) (SUC (f (NUM_PAYLOAD s))) " +
      "(COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "(SUC (NUM_ADD (f (NUM_FST (NUM_PAYLOAD s))) (f (NUM_SND (NUM_PAYLOAD s))))) " +
      "(COND (s = NUM_CODE 8 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "(SUC (f (NUM_SND (NUM_PAYLOAD s)))) " +
      "ZERO)))"

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

      groundLogic <- numbering.logic.over(groundTheory)
      withBounded <- Language.defineShaped(
        numbering, recursion, groundTheory, provability.notation, groundLogic,
        BoundedName, BoundedStepText, Type.Bool, Nil)
      (boundedTheory, boundedDefinition, boundedNamed) = withBounded

      boundedLogic <- numbering.logic.over(boundedTheory)
      withRank <- Language.defineShaped(
        numbering, recursion, boundedTheory, provability.notation, boundedLogic,
        RankName, RankStepText, numbers, Nil)
      (rankTheory, rankDefinition, rankNamed) = withRank

      // The Sigma-1 class, a primitive recursion on the number of existentials in front.
      rankLogic <- numbering.logic.over(rankTheory)
      onNumbers <- naturals.recursion
      withSigma <- Recursion.define(
        rankLogic, naturals, rankTheory, provability.notation, onNumbers, SigmaName,
        Type.fun(numbers, Type.Bool),
        "\\p:num. NUM_FORM p /\\ NUM_BOUNDED p",
        "\\v:num -> bool. \\i:num. \\p:num. ?j:num q:num. p = NUM_EXISTS j q /\\ v q",
        None)
      (sigmaTheory, sigmaDefinition, sigmaAtZero, sigmaAtSuccessor) = withSigma

      graphBody <- Parser.term(sigmaTheory, provability.notation, TriangleGraphText, numbers)
      withGraph <- LogicError.lift(Kernel.defineConstant(sigmaTheory, TriangleGraphName, graphBody))
      (triangleTheory, graphDefinition) = withGraph
      pairGraphBody <- Parser.term(triangleTheory, provability.notation, PairGraphText, numbers)
      withPairGraph <- LogicError.lift(
        Kernel.defineConstant(triangleTheory, PairGraphName, pairGraphBody))
      (pairTheory, pairGraphDefinition) = withPairGraph
      codeGraphBody <- Parser.term(pairTheory, provability.notation, CodeGraphText, numbers)
      withCodeGraph <- LogicError.lift(
        Kernel.defineConstant(pairTheory, CodeGraphName, codeGraphBody))
      (codeTheory, codeGraphDefinition) = withCodeGraph
      firstGraphBody <- Parser.term(codeTheory, provability.notation, FirstGraphText, numbers)
      withFirstGraph <- LogicError.lift(Kernel.defineConstant(codeTheory, FirstGraphName, firstGraphBody))
      (firstTheory, firstGraphDefinition) = withFirstGraph
      secondGraphBody <- Parser.term(firstTheory, provability.notation, SecondGraphText, numbers)
      withSecondGraph <- LogicError.lift(Kernel.defineConstant(firstTheory, SecondGraphName, secondGraphBody))
      (graphsTheory, secondGraphDefinition) = withSecondGraph

      // The instantiation, a primitive recursion on how many variables have had a numeral put for
      // them, the environment and the formula being the arguments of the function it produces.
      codeLogic <- numbering.logic.over(graphsTheory)
      withInstance <- Recursion.define(
        codeLogic, naturals, graphsTheory, provability.notation, onNumbers, InstanceName,
        Type.fun(environments, Type.fun(numbers, numbers)),
        "\\s:num -> num. \\p:num. p",
        "\\v:(num -> num) -> num -> num. \\i:num. \\s:num -> num. \\p:num. " +
          "NUM_SUBST_FORM i (NUM_NUMERAL (s i)) (v s p)",
        None)
      (theory, instanceDefinition, instanceAtZero, instanceAtSuccessor) = withInstance
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
      boundedEquality <- clauses.plain(boundedNamed, BoundedEquality)
      boundedNegation <- clauses.plain(boundedNamed, BoundedNegation)
      boundedImplication <- clauses.plain(boundedNamed, BoundedImplication)
      abbreviations <- Vector(Language.AllBelowCases, Language.LessCases, Language.ExistsCases)
        .foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) { (carried, name) =>
          for {
            found <- carried
            fact <- language.fact(name)
            rule <- Rewrite.Rule.of(logic, fact)
          } yield found :+ rule
        }
      boundedAllBelow <- clauses.abbreviated(boundedNamed, BoundedAllBelow, abbreviations)
      allBelowCases <- language.fact(Language.AllBelowCases)
      boundedUniversal <- boundedShape(
        logic, statements, clauses, boundedNamed, allBelowCases, naturals.classical)
      rankEquality <- clauses.plain(rankNamed, RankEquality, numbers)
      rankNegation <- clauses.plain(rankNamed, RankNegation, numbers)
      rankImplication <- clauses.plain(rankNamed, RankImplication, numbers)
      rankUniversal <- clauses.plain(rankNamed, RankUniversal, numbers)
      sigmaZero <- recursionClause(logic, statements, SigmaZero, sigmaAtZero, List("p" -> numbers))
      sigmaSuccessor <- recursionClause(
        logic, statements, SigmaSuccessor, sigmaAtSuccessor, List("p" -> numbers))
      instanceZero <- recursionClause(
        logic, statements, InstanceZero, instanceAtZero, List("s" -> environments, "p" -> numbers))
      instanceSuccessor <- recursionClause(
        logic, statements, InstanceSuccessor, instanceAtSuccessor,
        List("s" -> environments, "p" -> numbers))
      modusPonens <- provability.fact(Provability.ModusPonens)
      doubleNegation <- naturals.classical.fact(Classical.DoubleNegation)

      semiring <- Semiring.construct(numbering.peano)
      doubled <- triangleDoubled(logic, statements, naturals, numbering, semiring)
      graphEvaluation = Vector(valueVariable, valueSuccessor, valueSum, valueProduct, trueEquality)
      graph <- graphByDoubling(
        logic, statements, numbering, TriangleGraphTrue, graphDefinition, doubled, graphEvaluation)
      pairDefinition <- numbering.definition(Numbering.PairName)
      pairDoubled <- pairDoubling(logic, statements, pairDefinition, doubled, semiring)
      pairGraph <- graphByDoubling(
        logic, statements, numbering, PairGraphTrue, pairGraphDefinition, pairDoubled,
        graphEvaluation)
      codeDefinition <- numbering.definition(Numbering.CodeName)
      codeDoubled <- codeDoubling(logic, statements, numbering.peano, codeDefinition, pairDoubled)
      codeGraph <- graphByDoubling(
        logic, statements, numbering, CodeGraphTrue, codeGraphDefinition, codeDoubled,
        graphEvaluation)

      evaluation <- Evaluation.of(
        logic, theory, provability.notation, language, numbering, deduction, statements,
        valueZero, valueSuccessor, valueSum, valueProduct, trueEquality, trueNegation,
        Grounding(trueImplication, groundEquality, groundNegation, groundImplication, groundUniversal,
          modusPonens, doubleNegation, naturals.classical, valueVariable, valueNumeral, trueUniversal),
        Bounding(boundedEquality, boundedNegation, boundedImplication, boundedAllBelow, boundedUniversal,
          successor),
        Ranking(rankEquality, rankNegation, rankImplication, rankUniversal),
        Sigmas(sigmaZero, sigmaSuccessor),
        Instances(instanceZero, instanceSuccessor))

      // Each representation, the bridge at its graph, with the graph's three premises walked.
      bridge <- evaluation.get(ProvesBoundedInstance).toRight(MissingDefinition(ProvesBoundedInstance))
      bounding = Bounding(boundedEquality, boundedNegation, boundedImplication, boundedAllBelow, boundedUniversal,
        successor)
      representing = new Representing(logic, theory, provability.notation, language, numbering.peano,
        successor, naturals.classical, statements, bounding, bridge)
      triangleRepresented <- representing.of(TriangleRepresented, graphDefinition, graph)
      pairRepresented <- representing.of(PairRepresented, pairGraphDefinition, pairGraph)
      codeRepresented <- representing.of(CodeRepresented, codeGraphDefinition, codeGraph)

      // The projections' graphs, the first with a quantifier: their truth reads the universal below
      // a variable, which the evaluation proved, so they come after it rather than beside the others.
      allBelowVariable <- evaluation.get(TrueAllBelowVariable).toRight(MissingDefinition(TrueAllBelowVariable))
      projectionGraphs = new ProjectionGraphs(logic, theory, provability.notation, numbering, successor,
        naturals.classical, statements, pairDoubled, graphEvaluation ++ Vector(trueImplication, trueNegation),
        allBelowVariable)
      firstGraph <- projectionGraphs.of(FirstGraphTrue, firstGraphDefinition)
      secondGraph <- projectionGraphs.of(SecondGraphTrue, secondGraphDefinition)
      firstRepresented <- representing.of(FirstRepresented, firstGraphDefinition, firstGraph)
      secondRepresented <- representing.of(SecondRepresented, secondGraphDefinition, secondGraph)
    } yield new Truth(
      language,
      theory,
      provability.notation,
      logic,
      Map(
        ValueName -> valueDefinition,
        TrueName -> truthDefinition,
        GroundName -> groundDefinition,
        BoundedName -> boundedDefinition,
        RankName -> rankDefinition,
        SigmaName -> sigmaDefinition,
        InstanceName -> instanceDefinition,
        TriangleGraphName -> graphDefinition,
        PairGraphName -> pairGraphDefinition,
        CodeGraphName -> codeGraphDefinition,
        FirstGraphName -> firstGraphDefinition,
        SecondGraphName -> secondGraphDefinition
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
        PairDoubled -> pairDoubled,
        PairGraphTrue -> pairGraph,
        CodeDoubled -> codeDoubled,
        CodeGraphTrue -> codeGraph,
        GroundEquality -> groundEquality,
        GroundNegation -> groundNegation,
        GroundImplication -> groundImplication,
        GroundUniversal -> groundUniversal,
        BoundedEquality -> boundedEquality,
        BoundedNegation -> boundedNegation,
        BoundedImplication -> boundedImplication,
        BoundedAllBelow -> boundedAllBelow,
        BoundedUniversal -> boundedUniversal,
        RankEquality -> rankEquality,
        RankNegation -> rankNegation,
        RankImplication -> rankImplication,
        RankUniversal -> rankUniversal,
        SigmaZero -> sigmaZero,
        SigmaSuccessor -> sigmaSuccessor,
        InstanceZero -> instanceZero,
        InstanceSuccessor -> instanceSuccessor,
        TriangleRepresented -> triangleRepresented,
        PairRepresented -> pairRepresented,
        CodeRepresented -> codeRepresented,
        FirstGraphTrue -> firstGraph,
        SecondGraphTrue -> secondGraph,
        FirstRepresented -> firstRepresented,
        SecondRepresented -> secondRepresented
      ) ++ evaluation
    )
  }

  /**
   * A clause of a primitive recursion on the naturals, from the equation `Recursion.define` hands
   * back for the whole function: specialised at its leading quantifiers, applied to fresh
   * variables named and typed by `arguments`, and reduced, then compared with the statement
   * published. [[SigmaName]] takes the formula, [[InstanceName]] the environment and the formula.
   */
  private def recursionClause(
    logic: Logic,
    statements: Statements,
    name: String,
    equation: Kernel.Thm,
    arguments: List[(String, Type)]
  ): Either[LogicError, Kernel.Thm] = {
    for {
      stripped <- Logic.stripForall(equation.conclusion)
      binders = stripped._1.toList
      fresh = arguments.foldLeft(List.empty[FVar]) { case (taken, (wanted, ty)) =>
        taken :+ Conv.freshVariable(wanted, ty, binders.toSet ++ taken)
      }
      opened <- logic.rules.specAll(equation, binders)
      applied <- fresh.foldLeft[Either[LogicError, Kernel.Thm]](Right(opened))((carried, argument) =>
        carried.flatMap(Conv.apThm(_, argument)))
      sides <- Term.destEq(applied.conclusion).toRight(NotOfForm("an equation", applied.conclusion))
      reduced <- Conv.betaNormalise(sides._2)
      clause <- Conv.trans(applied, reduced)
      closed <- logic.rules.genAll(clause, binders ++ fresh)
      checked <- statements.checked(name, closed)
    } yield checked
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

    /** A clause of a recursion that reads no environment, by default one answering a truth value. */
    def plain(named: Kernel.Thm, name: String, answers: Type = Type.Bool): Either[LogicError, Kernel.Thm] =
      for {
        statement <- statements.statement(name)
        stripped <- Logic.stripForall(statement)
        (variables, body) = stripped
        sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
        code <- sides._1 match {
          case App(_, coded) => Right(coded)
          case other => Left(NotOfForm("a predicate read at a code", other))
        }
        reduced <- opened(named, code, Vector.empty, answers)
        general <- rules.genAll(reduced, variables.toList)
        result <- statements.checked(name, general)
      } yield result

    /**
     * The recursion equation of a truth-valued recursion at one code, its projections taken off
     * and every guard the tags decide settled. A guard they cannot decide stays standing, and the
     * caller compares what is left with a statement or splits on it.
     */
    def opened(
      named: Kernel.Thm,
      code: Term,
      unfolding: Vector[Rewrite.Rule],
      answers: Type = Type.Bool
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.spec(code, named)
        cleaned <- Rewrite.inTheorem(projections ++ unfolding, instance)
        settled <- Language.settleGuards(numbering, logic, successor, answers, cleaned)
        reduced <- Conv
          .betaNormalise(settled.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, settled)))
      } yield reduced

    /**
     * A clause of a truth-valued recursion stated at an abbreviation rather than at a code.
     *
     * The abbreviation is unfolded into the code it names first, by `unfolding`, and the recursion
     * equation is read there; its own step may name the same abbreviations, so the projections are
     * taken off with them unfolded as well, and the guards then compare two codes. The name goes
     * back on the left by congruence with the unfolding, so the published statement says
     * `NUM_ALL_BELOW` where the reader writes it.
     */
    def abbreviated(
      named: Kernel.Thm,
      name: String,
      unfolding: Vector[Rewrite.Rule]
    ): Either[LogicError, Kernel.Thm] =
      for {
        statement <- statements.statement(name)
        stripped <- Logic.stripForall(statement)
        (variables, body) = stripped
        sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
        read <- sides._1 match {
          case App(head, abbreviation) => Right((head, abbreviation))
          case other => Left(NotOfForm("a predicate read at an abbreviation", other))
        }
        (predicate, abbreviation) = read
        expanded <- Rewrite.rewrite(unfolding, abbreviation)
        code <- Term.destEq(expanded.conclusion).map(_._2)
          .toRight(NotOfForm("an equation", expanded.conclusion))
        reduced <- opened(named, code, unfolding)
        folded <- Conv.apTerm(predicate, expanded).flatMap(Conv.trans(_, reduced))
        general <- rules.genAll(folded, variables.toList)
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

  /**
   * [[BoundedUniversal]], by splitting on the universal's guard in the recursion equation.
   *
   * Where it holds, the guard is the equation the statement asks for, `NUM_ALL_BELOW` read
   * backwards at the witness, bound and body it names; where it fails, the class says `F` there
   * and the assumption is absurd.
   */
  private def boundedShape(
    logic: Logic,
    statements: Statements,
    clauses: Clauses,
    named: Kernel.Thm,
    allBelowCases: Kernel.Thm,
    classical: Classical
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    /** `goal` from `proved`, a proof of its body at `witnesses`, one existential at a time. */
    def introduced(goal: Term, witnesses: List[Term], proved: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      witnesses match {
        case Nil =>
          if (proved.conclusion == goal) Right(proved)
          else Left(NotOfForm("the body of the existential", proved.conclusion))
        case witness :: rest =>
          for {
            predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
            applied <- LogicError.lift(Term.app(predicate, witness))
            inner <- Term.betaReduce(applied).toRight(NotOfForm("a predicate", predicate))
            below <- introduced(inner, rest, proved)
            result <- rules.existsIntro(predicate, witness, below)
          } yield result
      }

    for {
      statement <- statements.statement(BoundedUniversal)
      stripped <- Logic.stripForall(statement)
      (variables, body) = stripped
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (claim, goal) = parts
      code <- claim match {
        case App(_, coded) => Right(coded)
        case other => Left(NotOfForm("a predicate read at a code", other))
      }
      reduced <- clauses.opened(named, code, Vector.empty)
      split <- Term.destEq(reduced.conclusion).map(_._2) match {
        case Some(App(App(App(_, guard), yes), no)) => Right((guard, yes, no))
        case _ => Left(NotOfForm("the universal's guard left standing", reduced.conclusion))
      }
      (guard, yes, no) = split
      shape <- Term.destEq(guard).map(_._2).toRight(NotOfForm("an equation", guard))
      pieces <- shape match {
        case App(App(_, _), App(App(_, index),
          App(App(_, _), App(App(_, App(App(App(_, witness), _), bound)), inner)))) =>
          Right((index, witness, bound, inner))
        case other => Left(NotOfForm("a universal over an order's implication", other))
      }
      (index, witness, bound, inner) = pieces
      assumed <- LogicError.lift(Kernel.assume(claim))
      conditional <- LogicError.lift(Kernel.eqMp(reduced, assumed))
      condFalse <- classical.fact(Classical.CondFalse)
        .map(Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), _))
      middle <- classical.fact(Classical.ExcludedMiddle).flatMap(rules.spec(guard, _))
      whenHeld <- for {
        held <- LogicError.lift(Kernel.assume(guard))
        unfolded <- rules.specAll(allBelowCases, List(witness, index, bound, inner))
        folded <- Conv.sym(unfolded).flatMap(Conv.trans(held, _))
        result <- introduced(goal, List(witness, bound, inner), folded)
      } yield result
      whenDenied <- for {
        denied <- logic.mkNot(guard).flatMap(term => LogicError.lift(Kernel.assume(term)))
        falls <- rules.specAll(condFalse, List(guard, yes, no)).flatMap(rules.mp(_, denied))
        absurd <- LogicError.lift(Kernel.eqMp(falls, conditional))
        result <- rules.falsityElim(goal, absurd)
      } yield result
      cases <- rules.disjElim(middle, whenHeld, whenDenied)
      discharged <- rules.disch(claim, cases)
      general <- rules.genAll(discharged, variables.toList)
      result <- statements.checked(BoundedUniversal, general)
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
   * A graph whose formula is `v0 + v0 = R`, from the doubled closed form `!x. F x + F x = R x`:
   * [[TriangleGraphTrue]], [[PairGraphTrue]] and [[CodeGraphTrue]].
   *
   * The graph's truth is first evaluated: unfolding the constant and rewriting with the value and
   * truth clauses gives, for the triangle, `NUM_TRUE NUM_TRI_GRAPH e = (e 0 + e 0 = e 1 * SUC (e 1))`.
   * What is left is an equivalence between two propositions about numbers, and its two halves are
   * different kinds of fact. From right to left it is the doubled closed form at the arguments
   * with `e 0` rewritten. From left to right it is the uniqueness of the solution: `x + x = y + y`
   * gives `x = y`, which is doubling cancelled, `NUM_MUL_TWO` turning each side into a product by
   * two and `NUM_MUL_CANCEL_LEFT` taking the two off.
   *
   * The arguments are read off the statement, `e 0 = F (e 1) ... (e k)`, and the doubled closed form
   * is specialised at them in the order `F` takes them, which is the order its quantifiers bind for
   * all three. If that ever stops being so, the specialised right side differs from the evaluated
   * one and the final `Conv.trans` refuses rather than proving another statement.
   */
  private def graphByDoubling(
    logic: Logic,
    statements: Statements,
    numbering: Numbering,
    name: String,
    graphDefinition: Kernel.Thm,
    doubled: Kernel.Thm,
    evaluation: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def arguments(applied: Term): List[Term] = applied match {
      case App(function, last) => arguments(function) :+ last
      case _ => Nil
    }

    for {
      statement <- statements.statement(name)
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
      (value, functionOfArguments) = meaningSides
      atArguments <- rules.specAll(doubled, arguments(functionOfArguments))

      // From right to left, under `e 0 = F (e 1) ...`: `e 0 + e 0` is the doubled closed form.
      assumedMeaning <- LogicError.lift(Kernel.assume(meaning))
      firstSummand <- Conv.apTerm(plus, assumedMeaning).flatMap(Conv.apThm(_, value))
      plusValue <- LogicError.lift(Term.app(plus, functionOfArguments))
      secondSummand <- Conv.apTerm(plusValue, assumedMeaning)
      forward <- Conv.trans(firstSummand, secondSummand).flatMap(Conv.trans(_, atArguments))

      // From left to right, under the evaluated equation: `x + x = R` and `F + F = R` give
      // `x + x = F + F`, and doubling cancels.
      assumedEquation <- LogicError.lift(Kernel.assume(equation))
      same <- Conv.sym(atArguments).flatMap(Conv.trans(assumedEquation, _))
      backward <- cancelDoubling(logic, numbering.peano, value, functionOfArguments, same)

      equivalence = Kernel.deductAntisym(forward, backward)
      atEnvironment <- Conv.trans(evaluated, equivalence)
      general <- rules.gen(environment, atEnvironment)
      result <- statements.checked(name, general)
    } yield result
  }

  /**
   * [[PairDoubled]].
   *
   * The pair unfolds to `T + a` with `T` the triangle at `a + b`, so twice it is
   * `(T + a) + (T + a)`; the semiring, reading `T` as an atom, regroups that into
   * `(T + T) + (a + a)`, and [[TriangleDoubled]] at `a + b` replaces the first summand.
   */
  private def pairDoubling(
    logic: Logic,
    statements: Statements,
    pairDefinition: Kernel.Thm,
    triangleDoubled: Kernel.Thm,
    semiring: Semiring
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      statement <- statements.statement(PairDoubled)
      stripped <- Logic.stripForall(statement)
      (bound, body) = stripped
      sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
      plus <- sides._1 match {
        case App(App(head, _), _) => Right(head)
        case other => Left(NotOfForm("a sum", other))
      }
      variables <- bound match {
        case Vector(a, b) => Right((a, b))
        case _ => Left(NotOfForm("a claim about two numbers", statement))
      }
      (a, b) = variables
      pair <- sides._1 match {
        case App(_, second) => Right(second)
        case other => Left(NotOfForm("a sum", other))
      }

      // `P + P = (T + a) + (T + a)`
      opened <- Conv.unfold(pairDefinition, List(a, b))
      openedValue <- Term.destEq(opened.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", opened.conclusion))
      first <- Conv.apTerm(plus, opened).flatMap(Conv.apThm(_, pair))
      plusOpened <- LogicError.lift(Term.app(plus, openedValue))
      second <- Conv.apTerm(plusOpened, opened)
      unfolded <- Conv.trans(first, second)

      // `(T + a) + (T + a) = (T + T) + (a + a)`
      triangle <- openedValue match {
        case App(App(_, t), _) => Right(t)
        case other => Left(NotOfForm("a triangle plus a number", other))
      }
      twiceTriangle <- LogicError.lift(Term.appAll(plus, List(triangle, triangle)))
      twiceA <- LogicError.lift(Term.appAll(plus, List(a, a)))
      regroupedTarget <- LogicError.lift(Term.appAll(plus, List(twiceTriangle, twiceA)))
      unfoldedValue <- Term.destEq(unfolded.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      regrouped <- semiring.prove(unfoldedValue, regroupedTarget)

      // `(T + T) + (a + a) = (a + b) * SUC (a + b) + (a + a)`
      sum <- triangle match {
        case App(_, inner) => Right(inner)
        case other => Left(NotOfForm("the triangle of a sum", other))
      }
      atSum <- rules.spec(sum, triangleDoubled)
      replaced <- Conv.apTerm(plus, atSum).flatMap(Conv.apThm(_, twiceA))

      proved <- Conv.trans(unfolded, regrouped).flatMap(Conv.trans(_, replaced))
      general <- rules.gen(b, proved).flatMap(rules.gen(a, _))
      result <- statements.checked(PairDoubled, general)
    } yield result
  }

  /**
   * [[CodeDoubled]].
   *
   * The code unfolds to `SUC P`, and `SUC P + SUC P` is `SUC (SUC (P + P))` by `NUM_SUC_ADD` and
   * `NUM_ADD_SUC`; [[PairDoubled]] at `t` and `p` replaces `P + P` under the two successors.
   */
  private def codeDoubling(
    logic: Logic,
    statements: Statements,
    peano: Peano,
    codeDefinition: Kernel.Thm,
    pairDoubled: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      statement <- statements.statement(CodeDoubled)
      stripped <- Logic.stripForall(statement)
      (bound, body) = stripped
      sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
      variables <- bound match {
        case Vector(t, p) => Right((t, p))
        case _ => Left(NotOfForm("a claim about two numbers", statement))
      }
      (t, p) = variables

      // `C + C = SUC P + SUC P`, unfolding both occurrences at once.
      opened <- Conv.unfold(codeDefinition, List(t, p))
      opening <- Rewrite.Rule.all(logic, Vector(opened))
      unfolded <- Rewrite.rewrite(opening, sides._1)

      // `SUC P + SUC P = SUC (SUC (P + P))`
      successors <- Vector(Peano.SuccessorPlus, Peano.AddAtSuccessor)
        .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
          carried.flatMap(found => peano.fact(name).map(found :+ _))
        }
        .flatMap(Rewrite.Rule.all(logic, _))
      unfoldedValue <- Term.destEq(unfolded.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      lifted <- Rewrite.rewrite(successors, unfoldedValue)

      // `SUC (SUC (P + P)) = SUC (SUC R)`, by congruence under the two successors rather than by
      // a rewrite: the left side repeats `t` and `p`, and a rule read from it would be a
      // non-linear pattern.
      atComponents <- rules.specAll(pairDoubled, List(t, p))
      liftedValue <- Term.destEq(lifted.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", lifted.conclusion))
      successor <- liftedValue match {
        case App(head, _) => Right(head)
        case other => Left(NotOfForm("a successor", other))
      }
      replaced <- Conv.apTerm(successor, atComponents).flatMap(Conv.apTerm(successor, _))

      proved <- Conv.trans(unfolded, lifted).flatMap(Conv.trans(_, replaced))
      general <- rules.gen(p, proved).flatMap(rules.gen(t, _))
      result <- statements.checked(CodeDoubled, general)
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

  /** What the closure of the bounded class reads: its clauses, and tags told apart. */
  private final case class Bounding(
    equality: Kernel.Thm,
    negation: Kernel.Thm,
    implication: Kernel.Thm,
    allBelow: Kernel.Thm,
    universal: Kernel.Thm,
    successor: Successor
  )

  /** The rank's four clauses, which the rank's own induction reads. */
  private final case class Ranking(
    equality: Kernel.Thm,
    negation: Kernel.Thm,
    implication: Kernel.Thm,
    universal: Kernel.Thm
  )

  /** The two clauses of [[SigmaName]], which the Sigma-1 facts read. */
  private final case class Sigmas(zero: Kernel.Thm, successor: Kernel.Thm)

  /** The two clauses of [[InstanceName]], which the instantiation's inductions read. */
  private final case class Instances(zero: Kernel.Thm, successor: Kernel.Thm)

  /**
   * What the direct-style derivations over a graph's code share: refusal, the constants of the
   * coding and of the order, carrying a theorem across an equation, and two numerals compared.
   *
   * A numeral is put below a larger one through their successor forms, which `Successor.spell`
   * gives both, by a chain of `n < SUC n` joined by transitivity; two different numerals are apart
   * by `Successor.distinct`.
   */
  private abstract class Direct(logic: Logic, theory: Theory, notation: Notation, peano: Peano, successor: Successor) {
    protected val rules: Rules = logic.rules
    protected val numbers: Type = TyApp(Natural.TypeName, Nil)
    protected val environments: Type = Type.fun(numbers, numbers)

    protected def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)
    protected def refused(error: LogicError): Nothing = throw new RefusedHere(error)
    protected def constant(name: String, ty: Type): Term =
      force(LogicError.lift(theory.constant(name, ty)))
    protected def applied(head: Term, arguments: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, arguments)))
    protected def sides(theorem: Kernel.Thm): (Term, Term) =
      force(Term.destEq(theorem.conclusion).toRight(NotOfForm("an equation", theorem.conclusion)))
    protected def assumed(claim: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(claim)))
    protected def equal(left: Term, right: Term): Term = force(LogicError.lift(Term.eq(left, right)))
    protected def denial(claim: Term): Term = force(logic.mkNot(claim))

    protected val coding: Term = constant(Numbering.CodeName, Type.fun(numbers, Type.fun(numbers, numbers)))
    protected val pairing: Term = constant(Numbering.PairName, Type.fun(numbers, Type.fun(numbers, numbers)))
    protected val below: Term = constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
    protected val plus: Term = constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
    protected val tags: Vector[Term] =
      (0 to 8).toVector.map(k => force(Parser.term(theory, notation, k.toString, numbers)))

    protected def lessThan(left: Term, right: Term): Term = applied(below, List(left, right))

    /** `|- held[to/from]` from `|- from = to` and `|- held`, `held` being `template(from)`. */
    protected def along(template: Term => Term, equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm = {
      val (from, _) = sides(equation)
      val hole = Term.variable("hole", Term.typeOf(from))
      force(LogicError.lift(Term.abs(hole, template(hole))).flatMap(Conv.apTerm(_, equation))
        .flatMap(Conv.betaSides).flatMap(e => LogicError.lift(Kernel.eqMp(e, held))))
    }

    private def depth(term: Term): Int = term match {
      case App(_, inner) => 1 + depth(inner)
      case _ => 0
    }
    private def spelled(numeral: Term): Kernel.Thm = force(successor.spell(numeral))

    /** `|- j < n` for two numerals with `j` the smaller, through their successor forms. */
    protected def numeralBelow(j: Term, n: Term): Kernel.Thm = {
      val (spelledJ, spelledN) = (spelled(j), spelled(n))
      val (from, to) = (sides(spelledJ)._2, sides(spelledN)._2)
      if (depth(from) >= depth(to)) refused(NotOfForm("a variable below the bound the representation states", j))
      val step = force(peano.fact(Peano.BelowSuccessor)) // !n. n < SUC n
      val transitive = force(peano.fact(Peano.StrictTransitive))
      def upper(order: Kernel.Thm): Term = order.conclusion match {
        case App(App(_, _), high) => high
        case other => refused(NotOfForm("an order", other))
      }
      // from < SUC from < ... < to, one successor at a time, each joined by transitivity
      def climb(held: Kernel.Thm): Kernel.Thm =
        if (upper(held) == to) held
        else {
          val next = force(rules.spec(upper(held), step))
          climb(force(rules.specAll(transitive, List(from, upper(held), upper(next)))
            .flatMap(t => rules.conjIntro(held, next).flatMap(rules.mp(t, _)))))
        }
      val reached = climb(force(rules.spec(from, step)))
      val atJ = along(x => lessThan(x, to), force(Conv.sym(spelledJ)), reached)
      along(x => lessThan(j, x), force(Conv.sym(spelledN)), atJ)
    }

    /** `|- ~(a = b)` for two different numerals, which `Successor.distinct` settles. */
    protected def apart(a: Term, b: Term): Kernel.Thm = force(successor.distinct(a, b))
  }

  /**
   * A representation in PA, from the graph's truth and [[ProvesBoundedInstance]]: what
   * [[TriangleRepresented]], [[PairRepresented]], [[CodeRepresented]], [[FirstRepresented]] and
   * [[SecondRepresented]] are each an instance of.
   *
   * The bridge asks three things of the graph, and each is shown by walking its code rather than
   * stated for it: that it is a formula, by the term and formula rules of `Language` at each
   * constructor; that it is in the bounded class, by its clause at each constructor; and that what
   * is free in it is below the number of variables put for. The bound is read off the published
   * statement, so it is written once.
   *
   * **What the walk reads, and the three readings do not read the same codes.** That the code is a
   * formula is `Language.wellFormedIn`, which reads every constructor of the grammar, the constant
   * zero and a numeral among them, and every abbreviation of `Language` through its equation. That
   * it is bounded is read here: equations, negations, implications, and a universal only written as
   * `NUM_ALL_BELOW`, where its clause is applied with the witness and the index apart and the bound
   * a variable apart from both or a numeral; the other abbreviations are read through their
   * equations, and a raw universal, an order or an existential outside one is not in the class and
   * is refused as such. That its free variables are below the bound is the freeness reading below,
   * whose rules hold no clause for the constant zero: a code with zero in it passes the first two
   * readings and is refused at this one, by the shape left standing. No graph here writes zero, so
   * that refusal has never been met; adding `NUM_FREE_TERM_ZERO` to the rules is what a graph
   * written with zero would need first.
   *
   * **The freeness is the one reading with a case split.** `NUM_FREE_FORM w` is rewritten through
   * the freeness clauses and the abbreviations, and what comes back is built from disjunctions,
   * `j = w` for each variable occurring, and, at each binder over `v_j`, `COND (j = w) F q`. Each
   * `j = w` is put below the bound, unless a binder over `v_j` encloses it, and then the binder's
   * guard `~(j = w)` refutes it; a binder's `COND` is split on its guard, and the side where `w` is
   * the bound variable is `F`.
   */
  private final class Representing(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    language: Language,
    peano: Peano,
    successor: Successor,
    classical: Classical,
    statements: Statements,
    bounding: Bounding,
    bridge: Kernel.Thm
  ) extends Direct(logic, theory, notation, peano, successor) {
    private def fact(name: String): Kernel.Thm = force(language.fact(name))

    private val freeIn = constant(Language.FormulaFreeName, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
    private val numeralOf = constant(Language.NumeralName, Type.fun(numbers, numbers))
    private val binary = Type.fun(numbers, Type.fun(numbers, numbers))
    private val allBelow = constant(Language.AllBelowName, Type.fun(numbers, Type.fun(numbers, binary)))
    private val less = constant(Language.LessName, Type.fun(numbers, binary))
    private val existsOf = constant(Language.ExistsName, binary)

    /** `(tag, payload)` of a code written `NUM_CODE tag payload`, the tag's value read off [[tags]]. */
    private def opened(code: Term): Option[(Int, Term)] = code match {
      case App(App(head, tag), payload) if head == coding && tags.contains(tag) =>
        Some((tags.indexOf(tag), payload))
      case _ => None
    }
    private def halves(payload: Term): Option[(Term, Term)] = payload match {
      case App(App(head, left), right) if head == pairing => Some((left, right))
      case _ => None
    }
    private def pairOf(code: Term, payload: Term): (Term, Term) =
      halves(payload).getOrElse(refused(NotOfForm("a code whose payload is a pair", code)))

    private val boundedness = constant(BoundedName, Type.fun(numbers, Type.Bool))

    /** `|- NUM_FORM code`, which `Language` walks, abbreviations included. */
    private def formOf(code: Term): Kernel.Thm = force(language.wellFormedIn(code))

    /** `|- NUM_BOUNDED code`, the bounded universal read by its own clause. */
    private def boundedOf(code: Term): Kernel.Thm = {
      def carried(clause: Kernel.Thm, proved: Kernel.Thm): Kernel.Thm =
        force(Conv.sym(clause).flatMap(back => LogicError.lift(Kernel.eqMp(back, proved))))
      opened(code) match {
        case Some((5, payload)) =>
          val (left, right) = pairOf(code, payload)
          force(rules.specAll(bounding.equality, List(left, right)).flatMap(rules.eqTruthElim))
        case Some((6, inner)) =>
          carried(force(rules.spec(inner, bounding.negation)), boundedOf(inner))
        case Some((7, payload)) =>
          val (left, right) = pairOf(code, payload)
          carried(force(rules.specAll(bounding.implication, List(left, right))),
            force(rules.conjIntro(boundedOf(left), boundedOf(right))))
        case _ => code match {
          case App(App(App(App(head, z), i), t), p) if head == allBelow =>
            val clause = force(rules.specAll(bounding.allBelow, List(z, i, t, p)))
            val (_, conditions) = sides(clause)
            val (_, rest) = force(logic.destConj(conditions).toRight(NotOfForm("a conjunction", conditions)))
            val (boundShape, _) = force(logic.destConj(rest).toRight(NotOfForm("a conjunction", rest)))
            val (asVariable, asNumeral) = force(logic.destDisj(boundShape).toRight(NotOfForm("a disjunction", boundShape)))
            def witnessed(existential: Term, witness: Term, proof: Term => Kernel.Thm): Kernel.Thm = {
              val predicate = force(logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential)))
              val instance = sides(force(LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaNormalise)))._2
              force(rules.existsIntro(predicate, witness, proof(instance)))
            }
            val shape = opened(t) match {
              case Some((0, index)) =>
                val atIndex = witnessed(asVariable, index, _ =>
                  force(rules.conjIntro(apart(index, i), apart(index, z)).flatMap(rules.conjIntro(Conv.refl(t), _))))
                force(rules.disjIntro1(asNumeral, atIndex))
              case _ => t match {
                case App(head, n) if head == numeralOf =>
                  force(rules.disjIntro2(asVariable, witnessed(asNumeral, n, _ => Conv.refl(t))))
                case _ => refused(NotOfForm("a bound that is a variable or a numeral", t))
              }
            }
            carried(clause, force(rules.conjIntro(shape, boundedOf(p)).flatMap(rules.conjIntro(apart(z, i), _))))
          case _ => language.unfolding(code) match {
            case Some(opened) if !isUnbounded(code) =>
              val unfolding = force(opened)
              along(x => applied(boundedness, List(x)), force(Conv.sym(unfolding)), boundedOf(sides(unfolding)._2))
            case _ => refused(NotOfForm("a formula of the bounded class: a universal only as NUM_ALL_BELOW", code))
          }
        }
      }
    }

    /** An order or an existential standing alone, which unfolds to a universal the class refuses. */
    private def isUnbounded(code: Term): Boolean = code match {
      case App(App(App(head, _), _), _) if head == less => true
      case App(App(head, _), _) if head == existsOf => true
      case _ => false
    }

    private val atBool = Map(Classical.TypeVariable -> Type.Bool)
    private val condTrue = Kernel.instType(atBool, force(classical.fact(Classical.CondTrue)))
    private val condFalse = Kernel.instType(atBool, force(classical.fact(Classical.CondFalse)))
    private val conditional = constant(Classical.Conditional, Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))))

    /** `|- !w. NUM_FREE_FORM w G ==> w < n`, from `G = code`. */
    private def coveredBy(graph: Term, definition: Kernel.Thm, bound: Term): Kernel.Thm = {
      val w = Term.variable("w", numbers)
      val atW = applied(freeIn, List(w))
      val atCode = force(Conv.apTerm(atW, definition)) // NUM_FREE_FORM w G = NUM_FREE_FORM w code
      val freeness = Vector(Language.FormulaFreeEquality, Language.FormulaFreeNegation,
        Language.FormulaFreeImplication, Language.FormulaFreeUniversal, Language.FreeSum, Language.FreeProduct,
        Language.FreeSuccessor, Language.FreeVariable).map(fact) ++
        Language.Abbreviations.values.map(_._1).toVector.sorted.map(fact)
      val reading = force(Rewrite.Rule.all(logic, freeness).flatMap(Rewrite.rewrite(_, sides(atCode)._2))
        .flatMap(Conv.trans(atCode, _)))
      val goal = lessThan(w, bound)
      def falsum(held: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(goal, held))
      // `held` is a reading of the freeness under the guards of the binders enclosing it
      def inRange(held: Kernel.Thm, guards: Map[Term, Kernel.Thm]): Kernel.Thm = held.conclusion match {
        case c if c == logic.falsity => falsum(held)
        case App(App(App(head, guard), yes), no) if head == conditional && yes == logic.falsity =>
          val reached = force(classical.cases(guard,
            falsum(force(rules.specAll(condTrue, List(guard, yes, no)).flatMap(rules.mp(_, assumed(guard)))
              .flatMap(e => LogicError.lift(Kernel.eqMp(e, held))))), {
              val denied = assumed(denial(guard))
              val passed = force(rules.specAll(condFalse, List(guard, yes, no)).flatMap(rules.mp(_, denied))
                .flatMap(e => LogicError.lift(Kernel.eqMp(e, held))))
              inRange(passed, guards.updated(guard, denied))
            }))
          reached
        case disjunction if logic.destDisj(disjunction).isDefined =>
          val (l, r) = logic.destDisj(disjunction).get
          force(rules.disjElim(held, inRange(assumed(l), guards), inRange(assumed(r), guards)))
        case _ =>
          val (index, other) = sides(held)
          if (other != w) refused(NotOfForm("a variable equal to the one asked about", held.conclusion))
          guards.get(held.conclusion) match {
            case Some(denied) => falsum(force(rules.notElim(denied, held)))
            case None => along(x => lessThan(x, bound), held, numeralBelow(index, bound))
          }
      }
      val free = applied(freeIn, List(w, graph))
      val premise = assumed(free)
      force(LogicError.lift(Kernel.eqMp(reading, premise)).map(inRange(_, Map.empty))
        .flatMap(rules.disch(free, _)).flatMap(rules.gen(w, _)))
    }

    /** The statement published as `name`, proved for the graph `G = code` whose truth is `graphTrue`. */
    def of(name: String, definition: Kernel.Thm, graphTrue: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      try {
        val (graph, code) = sides(definition)
        val statement = force(statements.statement(name))
        // the bound, read off the statement's first consequent: NUM_PROV (NUM_INST bound s G)
        val (_, body) = force(Logic.stripForall(statement))
        val bound = logic.destConj(body).flatMap { case (first, _) => logic.destImp(first) }.map(_._2) match {
          case Some(App(_, App(App(App(_, n), _), _))) => n
          case _ => refused(NotOfForm("a representation as the bridge states it", statement))
        }
        val s = Term.variable("s", environments)
        val formula = force(Conv.sym(definition).flatMap(Conv.apTerm(constant(Language.FormulaName,
          Type.fun(numbers, Type.Bool)), _)).flatMap(e => LogicError.lift(Kernel.eqMp(e, formOf(code)))))
        val bounded = force(Conv.sym(definition).flatMap(Conv.apTerm(constant(BoundedName,
          Type.fun(numbers, Type.Bool)), _)).flatMap(e => LogicError.lift(Kernel.eqMp(e, boundedOf(code)))))
        val decided = force(rules.specAll(bridge, List(bound, s, graph)).flatMap(rules.mp(_, formula))
          .flatMap(rules.mp(_, bounded)).flatMap(rules.mp(_, coveredBy(graph, definition, bound))))
        val meaning = force(rules.spec(s, graphTrue)) // NUM_TRUE G s = (s 0 = f (s 1) ...)
        val (proved, refuted) = force(logic.destConj(decided.conclusion)
          .toRight(NotOfForm("a conjunction", decided.conclusion))) match {
          case (yes, no) => (force(logic.destImp(yes).toRight(NotOfForm("an implication", yes)))._2,
            force(logic.destImp(no).toRight(NotOfForm("an implication", no)))._2)
        }
        val read = along(
          held => force(logic.mkImp(held, proved).flatMap(l =>
            logic.mkNot(held).flatMap(logic.mkImp(_, refuted)).flatMap(logic.mkConj(l, _)))),
          meaning, decided)
        statements.checked(name, force(rules.gen(s, read)))
      } catch { case refusal: RefusedHere => Left(refusal.error) }
  }

  /**
   * [[FirstGraphTrue]] and [[SecondGraphTrue]], one derivation at the slot the statement names.
   *
   * The graph's truth is evaluated by the truth's and the value's clauses, with
   * [[TrueAllBelowVariable]] at the bounded universal, its three conditions discharged as numerals
   * apart, and the updated environment read at `0`, `1` and `2` past the update at `2`. What is
   * left is `(!m. m < e 1 ==> ~A m) ==> A (e 1)`, `A m` saying that `e 1` doubled is the pair of
   * `e 0` and `m` doubled, or of `m` and `e 0` for the second slot, in the pair's doubled closed
   * form. Each `A x` gives the projection: cancel the doubling and project, which is the lemma both
   * halves spend. The docstring of [[FirstGraphTrue]] has the two halves.
   */
  private final class ProjectionGraphs(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    numbering: Numbering,
    successor: Successor,
    classical: Classical,
    statements: Statements,
    pairDoubled: Kernel.Thm,
    evaluation: Vector[Kernel.Thm],
    allBelowVariable: Kernel.Thm
  ) extends Direct(logic, theory, notation, numbering.peano, successor) {
    private val peano = numbering.peano
    private def numberingFact(name: String): Kernel.Thm = force(numbering.fact(name))
    private val atNumbers = Map(Classical.TypeVariable -> numbers)
    private val condTrue = Kernel.instType(atNumbers, force(classical.fact(Classical.CondTrue)))
    private val condFalse = Kernel.instType(atNumbers, force(classical.fact(Classical.CondFalse)))

    /** `|- !x y. COND (a = 2) x y = ...`, the update at `2` read at the index `a`. */
    private def readAt(a: Term): Kernel.Thm = {
      val x = Term.variable("x", numbers)
      val y = Term.variable("y", numbers)
      val guard = equal(a, tags(2))
      val read =
        if (a == tags(2)) force(rules.specAll(condTrue, List(guard, x, y)).flatMap(rules.mp(_, Conv.refl(a))))
        else force(rules.specAll(condFalse, List(guard, x, y)).flatMap(rules.mp(_, apart(a, tags(2)))))
      force(rules.genAll(read, List(x, y)))
    }

    def of(name: String, definition: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      try {
        val left = name match {
          case FirstGraphTrue => true
          case SecondGraphTrue => false
          case other => refused(MissingDefinition(other))
        }
        val statement = force(statements.statement(name))
        val (bound, body) = force(Logic.stripForall(statement))
        val e = bound.headOption.getOrElse(refused(NotOfForm("a claim about every environment", statement)))
        val (truthOfGraph, meaning) = force(Term.destEq(body).toRight(NotOfForm("an equation", body)))
        val (e0, projected) = force(Term.destEq(meaning).toRight(NotOfForm("an equation", meaning)))
        val (projection, e1) = projected match {
          case App(head, argument) => (head, argument)
          case other => refused(NotOfForm("a projection at one argument", other))
        }

        // TRUE G e = ((!m. m < e 1 ==> ~A m) ==> A (e 1))
        val p = Term.variable("p", numbers)
        val universal = force(rules.specAll(allBelowVariable, List(e, tags(3), tags(2), tags(1), p))
          .flatMap(rules.mp(_, apart(tags(3), tags(2)))).flatMap(rules.mp(_, apart(tags(1), tags(2))))
          .flatMap(rules.mp(_, apart(tags(1), tags(3)))).flatMap(rules.gen(p, _)))
        val evaluated = force(Rewrite.Rule.all(logic, Vector(definition, universal) ++ evaluation ++
          Vector(tags(0), tags(1), tags(2)).map(readAt)).flatMap(Rewrite.rewrite(_, truthOfGraph)))
        val reading = sides(evaluated)._2
        val (premise, conclusion) = force(logic.destImp(reading).toRight(NotOfForm("an implication", reading)))

        /** `A x`, read off the premise at `x` rather than written again. */
        def claim(x: Term): Term = {
          val instance = force(rules.spec(x, assumed(premise))).conclusion
          val (_, denied) = force(logic.destImp(instance).toRight(NotOfForm("an implication", instance)))
          force(logic.destNot(denied).toRight(NotOfForm("a negation", denied)))
        }
        if (claim(e1) != conclusion) refused(NotOfForm("the premise's claim at the argument", conclusion))

        def components(other: Term): List[Term] = if (left) List(e0, other) else List(other, e0)
        val ofPair = numberingFact(if (left) Numbering.FirstOfPair else Numbering.SecondOfPair)

        // A x ==> e 0 = proj (e 1): cancel the doubling, then project
        def projects(x: Term): Kernel.Thm = {
          val held = assumed(claim(x))
          val doubled = force(rules.specAll(pairDoubled, components(x))) // P + P = R
          val (twice, _) = sides(doubled)
          val pair = twice match {
            case App(App(_, summand), _) => summand
            case other => refused(NotOfForm("a doubled pair", other))
          }
          val same = force(Conv.sym(doubled).flatMap(Conv.trans(held, _))) // e 1 + e 1 = P + P
          val identified = force(cancelDoubling(logic, peano, e1, pair, same)) // e 1 = P
          val reached = force(Conv.apTerm(projection, identified)
            .flatMap(Conv.trans(_, force(rules.specAll(ofPair, components(x)))))
            .flatMap(Conv.sym))
          force(rules.disch(claim(x), reached))
        }

        // from the reading to the projection, by contradiction
        val forward = {
          val deniedTerm = denial(meaning)
          val denied = assumed(deniedTerm)
          val (variables, _) = force(Logic.stripForall(premise))
          val m = variables.headOption.getOrElse(refused(NotOfForm("a universal", premise)))
          val nowhere = force(rules.notIntro(claim(m),
            force(rules.mp(projects(m), assumed(claim(m))).flatMap(rules.notElim(denied, _)))))
          val everywhere = force(rules.disch(lessThan(m, e1), nowhere).flatMap(rules.gen(m, _)))
          val atArgument = force(rules.mp(assumed(reading), everywhere))
          val absurd = force(rules.mp(projects(e1), atArgument).flatMap(rules.notElim(denied, _)))
          force(classical.contradiction(meaning, absurd))
        }

        // from the projection to the reading: the pair `e 1` is, below the argument or at it
        val backward = {
          val onto = force(rules.spec(e1, numberingFact(Numbering.PairOnto)))
          def opening(existential: Kernel.Thm, label: String, avoid: Set[FVar])(proceed: (FVar, Kernel.Thm) => Kernel.Thm)
            : Kernel.Thm = {
            val predicate = force(logic.destExistsPredicate(existential.conclusion)
              .toRight(NotOfForm("an existential", existential.conclusion)))
            val witness = Conv.freshVariable(label, numbers, avoid ++ Term.freeVariables(existential.conclusion))
            val instance = sides(force(LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaNormalise)))._2
            force(rules.existsElim(existential, witness, proceed(witness, assumed(instance))))
          }
          val avoid = Term.freeVariables(reading) ++ Set(e)
          opening(onto, "a", avoid) { (a, rest) =>
            opening(rest, "b", avoid + a) { (b, shape) => // e 1 = NUM_PAIR a b
              val (component, other) = if (left) (a, b) else (b, a)
              val projectedIs = force(Conv.apTerm(projection, shape)
                .flatMap(Conv.trans(_, force(rules.specAll(ofPair, List(a, b)))))) // proj (e 1) = component
              val toComponent = force(Conv.trans(assumed(meaning), projectedIs)) // e 0 = component
              def pairAt(x: Term): Term = applied(pairing, if (left) List(x, other) else List(other, x))
              val reshaped = along(x => equal(e1, pairAt(x)), force(Conv.sym(toComponent)), shape) // e 1 = pair at e 0
              val doubledPair = force(rules.specAll(pairDoubled, components(other)))
              val atOther = force(Conv.apTerm(plus, reshaped).flatMap(Conv.apThm(_, e1))
                .flatMap(first => Conv.apTerm(applied(plus, List(pairAt(e0))), reshaped).flatMap(Conv.trans(first, _)))
                .flatMap(Conv.trans(_, doubledPair))) // A other
              if (atOther.conclusion != claim(other)) refused(NotOfForm("the premise's claim at the other component", atOther.conclusion))
              val componentBound = force(rules.specAll(numberingFact(if (left) Numbering.PairRight else Numbering.PairLeft),
                components(other)))
              val atMostArgument = along(x => applied(componentBound.conclusion match {
                case App(App(order, _), _) => order
                case shapeless => refused(NotOfForm("an order", shapeless))
              }, List(other, x)), force(Conv.sym(reshaped)), componentBound) // other <= e 1
              val split = force(peano.fact(Peano.BelowOrEqual).flatMap(rules.specAll(_, List(other, e1)))
                .flatMap(rules.mp(_, atMostArgument))) // other < e 1 \/ other = e 1
              val belowCase = {
                val refutedThere = force(rules.spec(other, assumed(premise)).flatMap(rules.mp(_, assumed(lessThan(other, e1)))))
                force(rules.notElim(refutedThere, atOther).flatMap(rules.falsityElim(conclusion, _)))
              }
              val atCase = along(claim, assumed(equal(other, e1)), atOther)
              force(rules.disjElim(split, belowCase, atCase).flatMap(rules.disch(premise, _)))
            }
          }
        }

        val equivalence = Kernel.deductAntisym(backward, forward) // reading = meaning
        statements.checked(name, force(Conv.trans(evaluated, equivalence).flatMap(rules.gen(e, _))))
      } catch { case refusal: RefusedHere => Left(refusal.error) }
  }

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
      grounding: Grounding,
      bounding: Bounding,
      ranking: Ranking,
      sigmas: Sigmas,
      instances: Instances
    ): Either[LogicError, Map[String, Kernel.Thm]] =
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
          parts <- statements.checked(FormImplicationParts, built.formImplicationParts(bounding))
          boundedAt <- statements.checked(BoundedAtNumeral, built.boundedAtNumeral(grounding, bounding, parts))
          rankAt <- statements.checked(RankAtNumeral, built.rankAtNumeral(grounding, ranking))
          freeTermAt <- statements.checked(FreeTermAtNumeral, built.freeTermAtNumeral(grounding))
          freeFormAt <- statements.checked(FreeFormAtNumeral, built.freeFormAtNumeral(grounding, freeTermAt))
          lessTruth <- statements.checked(TrueLessNumeral, built.trueLessNumeral(grounding))
          allBelowTruth <- statements.checked(TrueAllBelowNumeral, built.trueAllBelowNumeral(grounding, lessTruth))
          lessVariable <- statements.checked(TrueLessVariable, built.trueLessVariable(grounding))
          allBelowVariable <- statements.checked(TrueAllBelowVariable,
            built.trueAllBelowVariable(grounding, lessVariable))
          complete <- statements.checked(ProvesBounded, built.provesBounded(grounding, bounding, ranking, equation,
            denial, parts, truthAt, boundedAt, rankAt, freeFormAt, allBelowTruth))
          sigmaForm <- statements.checked(SigmaForm, built.sigmaForm(sigmas))
          sigmaAt <- statements.checked(SigmaAtNumeral, built.sigmaAtNumeral(grounding, sigmas, boundedAt))
          existsTruth <- statements.checked(TrueExists, built.trueExists(grounding))
          sigmaComplete <- statements.checked(ProvesSigma, built.provesSigma(grounding, sigmas, sigmaForm, sigmaAt,
            existsTruth, truthAt, freeFormAt, complete))
          instanceForm <- statements.checked(InstanceForm, built.instanceForm(instances))
          instanceBounded <- statements.checked(InstanceBounded,
            built.instanceBounded(instances, instanceForm, boundedAt))
          instanceSigma <- statements.checked(InstanceSigma, built.instanceSigma(instances, sigmaAt))
          instanceFree <- statements.checked(InstanceFree,
            built.instanceFree(grounding, instances, instanceForm, freeFormAt))
          instanceTrue <- statements.checked(InstanceTrue,
            built.instanceTrue(grounding, instances, instanceForm, truthAt))
          boundedBridge <- statements.checked(ProvesBoundedInstance, built.provesBoundedInstance(grounding,
            instanceForm, instanceBounded, instanceFree, instanceTrue, complete))
          sigmaBridge <- statements.checked(ProvesSigmaInstance, built.provesSigmaInstance(grounding,
            sigmaForm, instanceForm, instanceSigma, instanceFree, instanceTrue, sigmaComplete))
        } yield Map(
          ProvesValue -> value,
          ProvesTrueEquation -> equation,
          ProvesFalseEquation -> denial,
          ProvesGround -> ground,
          ValueAtNumeral -> valueAt,
          TrueAtNumeral -> truthAt,
          FormImplicationParts -> parts,
          BoundedAtNumeral -> boundedAt,
          RankAtNumeral -> rankAt,
          FreeTermAtNumeral -> freeTermAt,
          FreeFormAtNumeral -> freeFormAt,
          TrueLessNumeral -> lessTruth,
          TrueAllBelowNumeral -> allBelowTruth,
          TrueLessVariable -> lessVariable,
          TrueAllBelowVariable -> allBelowVariable,
          ProvesBounded -> complete,
          SigmaForm -> sigmaForm,
          SigmaAtNumeral -> sigmaAt,
          TrueExists -> existsTruth,
          ProvesSigma -> sigmaComplete,
          InstanceForm -> instanceForm,
          InstanceBounded -> instanceBounded,
          InstanceSigma -> instanceSigma,
          InstanceFree -> instanceFree,
          InstanceTrue -> instanceTrue,
          ProvesBoundedInstance -> boundedBridge,
          ProvesSigmaInstance -> sigmaBridge)
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
              force(Conv.betaNormalise(applied(update, List(b))))) // VALUE v_b e[x := k] = COND (b = x) k (e b)
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
            val update = updated(environment, x, k) // e[x := k]
            def bound(env: Term): Term = updated(env, u, n) // env[u := n]
            def underQuantifier(bodyEquation: Kernel.Thm): Kernel.Thm =
              force(LogicError.lift(Kernel.abs(n, bodyEquation)).flatMap(Conv.apTerm(universals, _)))
            def truthThrough(s: Term, envEquation: Kernel.Thm): Kernel.Thm =
              force(Conv.apTerm(applied(truth, List(s)), envEquation))
            val atUpdate = apply(g.trueUniversal, List(update, u, v)) // TRUE (!v_u. v) e[x := k] = !n. TRUE v e[x := k][u := n]
            val substitution = apply(languageFact(Language.FormulaSubstituteUniversal), List(x, nk, u, v))
            def truthOfSubstituted(equation: Kernel.Thm): Kernel.Thm =
              force(Conv.apTerm(truth, equation).flatMap(Conv.apThm(_, environment)))
            val atShape = split(equal(u, x))(
              isX => {
                // The substitution stops, and e[x := k][u := n] is e[u := n], since u is x.
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

    /* ------------------------------------- the bounded class under a numeral put for a variable */

    private val boundedPredicate = constant(BoundedName, property)
    private def isFormula(s: Term): Term = applied(formPredicate, List(s))
    private def bounded(s: Term): Term = applied(boundedPredicate, List(s))
    private def conjuncts(t: Term): (Term, Term) =
      logic.destConj(t).getOrElse(throw new RefusedHere(NotOfForm("a conjunction", t)))
    private def disjuncts(t: Term): (Term, Term) =
      logic.destDisj(t).getOrElse(throw new RefusedHere(NotOfForm("a disjunction", t)))

    /** The two arguments of a binary application, `f a b`. */
    private def arguments(t: Term): (Term, Term) = t match {
      case App(App(_, first), second) => (first, second)
      case other => throw new RefusedHere(NotOfForm("an application to two arguments", other))
    }

    /** The guard and the two branches of `COND p a b`. */
    private def branches(t: Term): (Term, Term, Term) = t match {
      case App(App(App(_, guard), yes), no) => (guard, yes, no)
      case other => throw new RefusedHere(NotOfForm("a conditional", other))
    }

    /** `goal`, an existential, from its body at `witness`. */
    private def introduced(goal: Term, witness: Term, proved: Kernel.Thm): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(goal)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", goal)))
      force(rules.existsIntro(predicate, witness, proved))
    }

    private lazy val codeInjective = force(numbering.fact(Numbering.CodeInjective))
    private lazy val pairInjective = force(numbering.fact(Numbering.PairInjective))

    /** [[FormImplicationParts]], from `NUM_FORM`'s cases at tag `7`, the other tags refused. */
    def formImplicationParts(bounding: Bounding): Kernel.Thm = {
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)
      val whole = code(7, pair(p, q))
      val goal = force(logic.mkConj(isFormula(p), isFormula(q)))
      val held = assumed(isFormula(whole))
      val shapes = force(rules.spec(whole, languageFact(Language.FormulaCases)).flatMap(unfolding =>
        LogicError.lift(Kernel.eqMp(unfolding, held))))
      val reached = opened(shapes, "a", Set(p, q)) { (a, withTag) =>
        opened(withTag, "b", Set(p, q, a)) { (b, shaped) =>
          val injected = apply(codeInjective, List(tags(7), pair(p, q), a, b), force(rules.conjElim1(shaped)))
          val tagIs = force(rules.conjElim1(injected)) // 7 = a
          val payloadIs = force(rules.conjElim2(injected)) // NUM_PAIR p q = b
          val alternatives = force(rules.conjElim2(shaped))
          val (equalityCase, rest1) = disjuncts(alternatives.conclusion)
          val (negationCase, rest2) = disjuncts(rest1)
          val (implicationCase, universalCase) = disjuncts(rest2)
          def refuted(alternative: Term, tag: Int): Kernel.Thm = {
            val sevenIs = force(Conv.trans(tagIs, force(rules.conjElim1(assumed(alternative)))))
            val never = force(bounding.successor.distinct(tags(7), tags(tag)))
            force(rules.notElim(never, sevenIs).flatMap(rules.falsityElim(goal, _)))
          }
          val asImplication =
            opened(force(rules.conjElim2(assumed(implicationCase))), "u", Set(p, q, a, b)) { (u, withLeft) =>
              opened(withLeft, "v", Set(p, q, a, b, u)) { (v, pieces) =>
                val pairs = force(Conv.trans(payloadIs, force(rules.conjElim1(pieces))))
                val components = apply(pairInjective, List(p, q, u, v), pairs) // p = u /\ q = v
                val forms = force(rules.conjElim2(pieces))
                val atP = moved(isFormula, force(Conv.sym(force(rules.conjElim1(components)))),
                  force(rules.conjElim1(forms)))
                val atQ = moved(isFormula, force(Conv.sym(force(rules.conjElim2(components)))),
                  force(rules.conjElim2(forms)))
                force(rules.conjIntro(atP, atQ))
              }
            }
          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, refuted(universalCase, 8)))
          val lastThree = force(rules.disjElim(assumed(rest1), refuted(negationCase, 6), lastTwo))
          force(rules.disjElim(alternatives, refuted(equalityCase, 5), lastThree))
        }
      }
      force(rules.disch(isFormula(whole), reached).flatMap(rules.genAll(_, List(p, q))))
    }

    /** [[BoundedAtNumeral]], by strong induction on the code, one case per shape of a formula. */
    def boundedAtNumeral(g: Grounding, bounding: Bounding, parts: Kernel.Thm): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val nk = numeral(k) // closed, so a bound it replaces is a numeral, which the class takes
      val substitutedHead = applied(formulaSubstituting, List(x, nk))
      val termSubstitutedHead = applied(substituting, List(x, nk))
      def substituted(s: Term): Term = applied(formulaSubstituting, List(x, nk, s))
      def claimAt(s: Term): Term = imp(isFormula(s), imp(bounded(s), bounded(substituted(s))))
      /** `NUM_BOUNDED r` from `NUM_BOUNDED l` and `l = r`. */
      def through(equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm = moved(bounded, equation, held)
      val strictTransitive = force(numbering.peano.fact(Peano.StrictTransitive))

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimAt(y))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimAt(z))))
      val earlier = assumed(hypothesis)
      val yIsForm = assumed(isFormula(y))
      val yIsBounded = assumed(bounded(y))
      def atComponent(part: Term, isBelow: Kernel.Thm, partIsForm: Kernel.Thm, partIsBounded: Kernel.Thm)
        : Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsForm))
          .flatMap(rules.mp(_, partIsBounded)))

      val shapes = force(rules.spec(y, languageFact(Language.FormulaCases)).flatMap(unfolding =>
        LogicError.lift(Kernel.eqMp(unfolding, yIsForm))))
      val taken0 = Set(y, z, x, k)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => bounded(substituted(t)), force(Conv.sym(yIsShape)), atShape)
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          def shapeIsBounded(yIsShape: Kernel.Thm): Kernel.Thm = through(yIsShape, yIsBounded)
          val (equalityCase, rest1) = disjuncts(alternatives.conclusion)
          val (negationCase, rest2) = disjuncts(rest1)
          val (implicationCase, universalCase) = disjuncts(rest2)
          def pairCase(held: Kernel.Thm)(proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, pieces) =>
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, force(rules.conjElim1(pieces)))))
                proceed(u, v, yIsShape, force(rules.conjElim2(pieces)))
              }
            }
          }

          // An equation: every equation is in the class, substituted or not.
          val asEquality = pairCase(assumed(equalityCase)) { (u, v, yIsShape, _) =>
            val substitution = apply(languageFact(Language.FormulaSubstituteEquality), List(x, nk, u, v))
            val (left, right) = arguments(arguments(sides(substitution)._2)._2)
            val atResult = force(rules.eqTruthElim(apply(bounding.equality, List(left, right))))
            back(through(force(Conv.sym(substitution)), atResult), yIsShape)
          }

          // A negation: the hypothesis at its body.
          val asNegation = {
            val held = assumed(negationCase)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held)), refl(b))))
            val bIsBounded = force(LogicError.lift(
              Kernel.eqMp(apply(bounding.negation, List(b)), shapeIsBounded(yIsShape))))
            val atB = atComponent(b, belowY(belowCode(6, b), b, yIsShape), force(rules.conjElim2(held)), bIsBounded)
            val substitution = apply(languageFact(Language.FormulaSubstituteNegation), List(x, nk, b))
            val atResult = force(Conv.sym(apply(bounding.negation, List(substituted(b)))).flatMap(folded =>
              LogicError.lift(Kernel.eqMp(folded, atB))))
            back(through(force(Conv.sym(substitution)), atResult), yIsShape)
          }

          // An implication: the hypothesis at both sides.
          val asImplication = pairCase(assumed(implicationCase)) { (u, v, yIsShape, forms) =>
            val both = force(LogicError.lift(
              Kernel.eqMp(apply(bounding.implication, List(u, v)), shapeIsBounded(yIsShape))))
            val atU = atComponent(u, belowY(belowPair(7, u, v, first = true), u, yIsShape),
              force(rules.conjElim1(forms)), force(rules.conjElim1(both)))
            val atV = atComponent(v, belowY(belowPair(7, u, v, first = false), v, yIsShape),
              force(rules.conjElim2(forms)), force(rules.conjElim2(both)))
            val substitution = apply(languageFact(Language.FormulaSubstituteImplication), List(x, nk, u, v))
            val atResult = force(
              Conv.sym(apply(bounding.implication, List(substituted(u), substituted(v)))).flatMap(folded =>
                rules.conjIntro(atU, atV).flatMap(joined => LogicError.lift(Kernel.eqMp(folded, joined)))))
            back(through(force(Conv.sym(substitution)), atResult), yIsShape)
          }

          // A universal: in the class only as an order's universal, whose parts the clause gives.
          val asUniversal = pairCase(assumed(universalCase)) { (u, v, yIsShape, vIsForm) =>
            val inverted = apply(bounding.universal, List(u, v), shapeIsBounded(yIsShape))
            val avoid = taken0 + a + b + u + v
            opened(inverted, "w", avoid) { (w, atW) =>
              opened(atW, "c", avoid + w) { (c, atC) =>
                opened(atC, "r", avoid + w + c) { (r, isAllBelow) =>
                  // code8 (pair u v) = NUM_ALL_BELOW w u c r = code8 (pair u (code7 (pair less r)))
                  val unfolding = apply(languageFact(Language.AllBelowCases), List(w, u, c, r))
                  val whole = sides(unfolding)._2
                  val implication = arguments(arguments(whole)._2)._2
                  val less = arguments(arguments(implication)._2)._1
                  val shapes8 = chained(isAllBelow, unfolding)
                  val payloads = force(rules.conjElim2(
                    apply(codeInjective, List(tags(8), pair(u, v), tags(8), pair(u, implication)), shapes8)))
                  val vIs = force(rules.conjElim2(apply(pairInjective, List(u, v, u, implication), payloads)))
                  val rIsForm = force(rules.conjElim2(apply(parts, List(less, r), moved(isFormula, vIs, vIsForm))))

                  val allBelowIsBounded = through(isAllBelow, shapeIsBounded(yIsShape))
                  val clause = force(LogicError.lift(
                    Kernel.eqMp(apply(bounding.allBelow, List(w, u, c, r)), allBelowIsBounded)))
                  val apart = force(rules.conjElim1(clause)) // ~(w = u)
                  val boundHeld = force(rules.conjElim1(force(rules.conjElim2(clause))))
                  val rIsBounded = force(rules.conjElim2(force(rules.conjElim2(clause))))

                  val rBelow = apply(strictTransitive, List(r, implication, whole),
                    force(rules.conjIntro(belowPair(7, less, r, first = false),
                      belowPair(8, u, implication, first = false))))
                  val atR = atComponent(r, belowY(rBelow, r, chained(yIsShape, shapes8)), rIsForm, rIsBounded)

                  val substitution = chained(force(Conv.apTerm(substitutedHead, isAllBelow)),
                    apply(languageFact(Language.AllBelowSubstitute), List(x, nk, w, u, c, r)))
                  val (_, stopped, under) = branches(sides(substitution)._2)
                  val atShape = split(equal(u, x))(
                    isX => through(force(Conv.sym(chained(substitution, taken(isX, stopped, under)))),
                      allBelowIsBounded),
                    notX => {
                      val (newBound, substitutedBody) = arguments(under)
                      def boundAt(t: Term): Term =
                        conjuncts(conjuncts(sides(apply(bounding.allBelow, List(w, u, t, substitutedBody)))._2)._2)._1
                      val (_, unchanged, termSubstituted) = branches(newBound)
                      val newBoundHeld = split(equal(w, x))(
                        isWX => moved(boundAt, force(Conv.sym(taken(isWX, unchanged, termSubstituted))), boundHeld),
                        notWX => {
                          val (variableGoal, numeralGoal) = disjuncts(boundAt(termSubstituted))
                          val (variableHad, numeralHad) = disjuncts(boundHeld.conclusion)
                          val asVariable = opened(assumed(variableHad), "j", avoid + w + c + r) { (j, held) =>
                            val atVariable = chained(force(Conv.apTerm(termSubstitutedHead, force(rules.conjElim1(held)))),
                              apply(languageFact(Language.SubstituteVariable), List(x, nk, j)))
                            split(equal(j, x))(
                              isJX => force(rules.disjIntro2(variableGoal,
                                introduced(numeralGoal, k, chained(atVariable, taken(isJX, nk, code(0, j)))))),
                              notJX => force(rules.disjIntro1(numeralGoal,
                                introduced(variableGoal, j, force(rules.conjIntro(
                                  chained(atVariable, passed(notJX, nk, code(0, j))),
                                  force(rules.conjElim2(held))))))))
                          }
                          val asNumeral = opened(assumed(numeralHad), "n", avoid + w + c + r) { (n, held) =>
                            val nowhere = force(rules.spec(numeral(n), closedCases).flatMap(unfolded =>
                              LogicError.lift(Kernel.eqMp(unfolded, numeralClosed(n)))).flatMap(rules.spec(x, _)))
                            val idle = apply(languageFact(Language.SubstituteIdle), List(x, nk, numeral(n)),
                              numeralTerm(n), nowhere)
                            val atNumeral = chained(force(Conv.apTerm(termSubstitutedHead, held)), idle)
                            force(rules.disjIntro2(variableGoal, introduced(numeralGoal, n, atNumeral)))
                          }
                          val joined = force(rules.disjElim(boundHeld, asVariable, asNumeral))
                          moved(boundAt, force(Conv.sym(passed(notWX, unchanged, termSubstituted))), joined)
                        })
                      val atUnder = force(Conv.sym(apply(bounding.allBelow, List(w, u, newBound, substitutedBody)))
                        .flatMap(folded => rules.conjIntro(newBoundHeld, atR).flatMap(rules.conjIntro(apart, _))
                          .flatMap(joined => LogicError.lift(Kernel.eqMp(folded, joined)))))
                      through(force(Conv.sym(chained(substitution, passed(notX, stopped, under)))), atUnder)
                    })
                  back(atShape, yIsShape)
                }
              }
            }
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(rules.disch(bounded(y), reached).flatMap(rules.disch(isFormula(y), _))
        .flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val p = Term.variable("p", numbers)
      force(rules.mp(instance, step).flatMap(rules.spec(p, _)).flatMap(rules.genAll(_, List(x, k, p))))
    }

    /* --------------------------------------------------- the rank under a numeral put for a variable */

    private val rankOf = constant(RankName, Type.fun(numbers, numbers))

    /**
     * [[RankAtNumeral]], by strong induction on the code, one case per shape of a formula.
     *
     * Every case is the substitution's clause and the rank's on the left, the rank's clause on the
     * right, and the hypothesis at the parts between them, which `met` joins. The universal splits
     * first on whether it binds `x`, where the substitution stops and there is nothing to join.
     */
    def rankAtNumeral(g: Grounding, ranking: Ranking): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val nk = numeral(k)
      def rank(s: Term): Term = applied(rankOf, List(s))
      def substituted(s: Term): Term = applied(formulaSubstituting, List(x, nk, s))
      def kept(s: Term): Term = equal(rank(substituted(s)), rank(s))
      def claimAt(s: Term): Term = imp(isFormula(s), kept(s))

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimAt(y))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimAt(z))))
      val earlier = assumed(hypothesis)
      val yIsForm = assumed(isFormula(y))
      def atComponent(part: Term, isBelow: Kernel.Thm, partIsForm: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsForm)))

      val shapes = force(rules.spec(y, languageFact(Language.FormulaCases)).flatMap(unfolding =>
        LogicError.lift(Kernel.eqMp(unfolding, yIsForm))))
      val taken0 = Set(y, z, x, k)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(kept, force(Conv.sym(yIsShape)), atShape)
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          val (equalityCase, rest1) = disjuncts(alternatives.conclusion)
          val (negationCase, rest2) = disjuncts(rest1)
          val (implicationCase, universalCase) = disjuncts(rest2)
          def pairCase(held: Kernel.Thm)(proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, pieces) =>
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, force(rules.conjElim1(pieces)))))
                proceed(u, v, yIsShape, force(rules.conjElim2(pieces)))
              }
            }
          }

          // An equation: substituted or not, its rank is zero.
          val asEquality = pairCase(assumed(equalityCase)) { (u, v, yIsShape, _) =>
            back(met(Vector(languageFact(Language.FormulaSubstituteEquality), ranking.equality),
              kept(code(5, pair(u, v)))), yIsShape)
          }

          // A negation: the hypothesis at its body.
          val asNegation = {
            val held = assumed(negationCase)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held)), refl(b))))
            val atB = atComponent(b, belowY(belowCode(6, b), b, yIsShape), force(rules.conjElim2(held)))
            back(met(Vector(languageFact(Language.FormulaSubstituteNegation), ranking.negation, atB),
              kept(code(6, b))), yIsShape)
          }

          // An implication: the hypothesis at both sides.
          val asImplication = pairCase(assumed(implicationCase)) { (u, v, yIsShape, forms) =>
            val atU = atComponent(u, belowY(belowPair(7, u, v, first = true), u, yIsShape),
              force(rules.conjElim1(forms)))
            val atV = atComponent(v, belowY(belowPair(7, u, v, first = false), v, yIsShape),
              force(rules.conjElim2(forms)))
            back(met(Vector(languageFact(Language.FormulaSubstituteImplication), ranking.implication, atU, atV),
              kept(code(7, pair(u, v)))), yIsShape)
          }

          // A universal: over `x` the substitution stops; over another index it goes under.
          val asUniversal = pairCase(assumed(universalCase)) { (u, v, yIsShape, vIsForm) =>
            val shape = code(8, pair(u, v))
            val substitution = apply(languageFact(Language.FormulaSubstituteUniversal), List(x, nk, u, v))
            val (_, stopped, under) = branches(sides(substitution)._2)
            val atShape = split(equal(u, x))(
              isX => force(Conv.apTerm(rankOf, chained(substitution, taken(isX, stopped, under)))),
              notX => {
                val atV = atComponent(v, belowY(belowPair(8, u, v, first = false), v, yIsShape), vIsForm)
                met(Vector(chained(substitution, passed(notX, stopped, under)), ranking.universal, atV), kept(shape))
              })
            back(atShape, yIsShape)
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(rules.disch(isFormula(y), reached).flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val p = Term.variable("p", numbers)
      force(rules.mp(instance, step).flatMap(rules.spec(p, _)).flatMap(rules.genAll(_, List(x, k, p))))
    }

    /* ----------------------------------------- free variables after a numeral is put for one */

    private val freeInTerm = constant(Language.FreeName, Type.fun(numbers, property))
    private val freeInFormula = constant(Language.FormulaFreeName, Type.fun(numbers, property))
    private def freeTerm(i: Term, s: Term): Term = applied(freeInTerm, List(i, s))
    private def freeForm(i: Term, s: Term): Term = applied(freeInFormula, List(i, s))
    private def conj(left: Term, right: Term): Term = force(logic.mkConj(left, right))
    private def disj(left: Term, right: Term): Term = force(logic.mkDisj(left, right))

    /** `r` from `l` and `l = r`. */
    private def unfold(equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(LogicError.lift(Kernel.eqMp(equation, held)))

    /** `l` from `r` and `l = r`. */
    private def fold(equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(Conv.sym(equation).flatMap(back => LogicError.lift(Kernel.eqMp(back, held))))

    /** The two halves of `COND p a b` over truth values, which a freeness clause at a binder is. */
    private final class Propositions(g: Grounding) {
      private val atBool = Map(Classical.TypeVariable -> Type.Bool)
      private val condTrue = Kernel.instType(atBool, force(g.classical.fact(Classical.CondTrue)))
      private val condFalse = Kernel.instType(atBool, force(g.classical.fact(Classical.CondFalse)))

      /** `COND p a b = a` from `p`, at `bool`. */
      def takenAt(guard: Kernel.Thm, a: Term, b: Term): Kernel.Thm =
        apply(condTrue, List(guard.conclusion, a, b), guard)

      /** `COND p a b = b` from `~p`, at `bool`. */
      def passedAt(denied: Kernel.Thm, a: Term, b: Term): Kernel.Thm = {
        val guard = logic.destNot(denied.conclusion)
          .getOrElse(throw new RefusedHere(NotOfForm("a negation", denied.conclusion)))
        apply(condFalse, List(guard, a, b), denied)
      }
    }

    /** [[FreeTermAtNumeral]], by strong induction on the code, one case per shape of a term. */
    def freeTermAtNumeral(g: Grounding): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val w = Term.variable("w", numbers)
      val nk = numeral(k)
      val apart = denial(equal(w, x))
      def substituted(s: Term): Term = applied(substituting, List(x, nk, s))
      def survives(s: Term): Term = imp(freeTerm(w, substituted(s)), conj(freeTerm(w, s), apart))
      def everywhere(s: Term): Term = force(logic.mkForall(w, survives(s)))
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
      /** `free w s /\ ~(w = x)` from `free w (s[numeral k/x])`, at a part below `y`. */
      def survivor(part: Term, isBelow: Kernel.Thm, partIsTerm: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsTerm))
          .flatMap(rules.spec(w, _)).flatMap(rules.mp(_, held)))

      val shapes = unfold(force(rules.spec(y, languageFact(Language.TermCases))), yIsTerm)
      val taken0 = Set(y, z, x, k, w)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(everywhere, force(Conv.sym(yIsShape)), force(rules.gen(w, atShape)))
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          /** `survives(shape)`, from a proof of its conclusion under its premise. */
          def assuming(shape: Term)(proved: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
            val premise = freeTerm(w, substituted(shape))
            force(rules.disch(premise, proved(assumed(premise))))
          }
          def through(substitution: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
            moved(t => freeTerm(w, t), substitution, held)
          val (variableCase, rest1) = disjuncts(alternatives.conclusion)
          val (zeroCase, rest2) = disjuncts(rest1)
          val (successorCase, binaryCase) = disjuncts(rest2)

          // A variable: v_x becomes the numeral, which has no variable; any other stays itself.
          val asVariable = {
            val shape = code(0, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(assumed(variableCase), refl(b))))
            val substitution = apply(languageFact(Language.SubstituteVariable), List(x, nk, b))
            back(assuming(shape) { held =>
              split(equal(b, x))(
                isX => {
                  val atNumeral = through(chained(substitution, taken(isX, nk, shape)), held)
                  val never = force(rules.spec(w, unfold(force(rules.spec(nk, closedCases)), numeralClosed(k))))
                  force(rules.notElim(never, atNumeral).flatMap(rules.falsityElim(conj(freeTerm(w, shape), apart), _)))
                },
                notX => {
                  val atVariable = through(chained(substitution, passed(notX, nk, shape)), held)
                  val bIsW = unfold(apply(languageFact(Language.FreeVariable), List(w, b)), atVariable)
                  val wIsX = equal(w, x)
                  val different = force(rules.notElim(notX, chained(bIsW, assumed(wIsX))).flatMap(rules.notIntro(wIsX, _)))
                  force(rules.conjIntro(atVariable, different))
                })
            }, yIsShape)
          }

          // Zero: nothing is free in it, substituted or not.
          val asZero = {
            val held0 = assumed(zeroCase)
            val shape = code(1, tags(0))
            val yIsShape = force(Conv.trans(yIsCode,
              codeCongruence(force(rules.conjElim1(held0)), force(rules.conjElim2(held0)))))
            back(assuming(shape) { held =>
              val atZero = through(apply(languageFact(Language.SubstituteZero), List(x, nk)), held)
              val falsity = unfold(apply(languageFact(Language.FreeZero), List(w)), atZero)
              force(rules.falsityElim(conj(freeTerm(w, shape), apart), falsity))
            }, yIsShape)
          }

          // A successor: the hypothesis at its argument.
          val asSuccessor = {
            val held0 = assumed(successorCase)
            val shape = code(2, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held0)), refl(b))))
            val isBelow = belowY(belowCode(2, b), b, yIsShape)
            back(assuming(shape) { held =>
              val atSuccessor = through(apply(languageFact(Language.SubstituteSuccessor), List(x, nk, b)), held)
              val inner = unfold(apply(languageFact(Language.FreeSuccessor), List(w, substituted(b))), atSuccessor)
              val survived = survivor(b, isBelow, force(rules.conjElim2(held0)), inner)
              val atShape = fold(apply(languageFact(Language.FreeSuccessor), List(w, b)), force(rules.conjElim1(survived)))
              force(rules.conjIntro(atShape, force(rules.conjElim2(survived))))
            }, yIsShape)
          }

          // A sum or a product: the hypothesis at whichever operand the variable is free in.
          val asBinary = {
            val held0 = assumed(binaryCase)
            val whichTag = force(rules.conjElim1(held0))
            opened(force(rules.conjElim2(held0)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, parts) =>
                val payloadIsPair = force(rules.conjElim1(parts))
                val components = force(rules.conjElim2(parts))
                val (sumTag, productTag) = disjuncts(whichTag.conclusion)
                def binary(tag: Int, tagEquation: Kernel.Thm): Kernel.Thm = {
                  val shape = code(tag, pair(u, v))
                  val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagEquation, payloadIsPair)))
                  val (substituteName, freeName) =
                    if (tag == 3) (Language.SubstituteSum, Language.FreeSum)
                    else (Language.SubstituteProduct, Language.FreeProduct)
                  back(assuming(shape) { held =>
                    val atPair = through(apply(languageFact(substituteName), List(x, nk, u, v)), held)
                    val either = unfold(apply(languageFact(freeName), List(w, substituted(u), substituted(v))), atPair)
                    val (leftPremise, rightPremise) = disjuncts(either.conclusion)
                    def side(part: Term, first: Boolean, partIsTerm: Kernel.Thm, premise: Term): Kernel.Thm = {
                      val survived = survivor(part, belowY(belowPair(tag, u, v, first), part, yIsShape), partIsTerm,
                        assumed(premise))
                      val here = force(rules.conjElim1(survived))
                      val inPair =
                        if (first) force(rules.disjIntro1(freeTerm(w, v), here))
                        else force(rules.disjIntro2(freeTerm(w, u), here))
                      force(rules.conjIntro(fold(apply(languageFact(freeName), List(w, u, v)), inPair),
                        force(rules.conjElim2(survived))))
                    }
                    force(rules.disjElim(either,
                      side(u, first = true, force(rules.conjElim1(components)), leftPremise),
                      side(v, first = false, force(rules.conjElim2(components)), rightPremise)))
                  }, yIsShape)
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

    /** [[FreeFormAtNumeral]], by strong induction on the code, one case per shape of a formula. */
    def freeFormAtNumeral(g: Grounding, freeTermAt: Kernel.Thm): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val propositions = new Propositions(g)
      import propositions.*
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val w = Term.variable("w", numbers)
      val nk = numeral(k)
      val apart = denial(equal(w, x))
      def substituted(s: Term): Term = applied(formulaSubstituting, List(x, nk, s))
      def survives(s: Term): Term = imp(freeForm(w, substituted(s)), conj(freeForm(w, s), apart))
      def everywhere(s: Term): Term = force(logic.mkForall(w, survives(s)))
      def claimAt(s: Term): Term = imp(isFormula(s), everywhere(s))
      /** `free w s /\ ~(w = x)` for a term `s`, from its substituted form being free. */
      def termSurvivor(s: Term, sIsTerm: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
        force(rules.specAll(freeTermAt, List(x, k, s)).flatMap(rules.mp(_, sIsTerm))
          .flatMap(rules.spec(w, _)).flatMap(rules.mp(_, held)))

      val y = Term.variable("y", numbers)
      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(y, claimAt(y))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(applied(below, List(z, y)), claimAt(z))))
      val earlier = assumed(hypothesis)
      val yIsForm = assumed(isFormula(y))
      def survivor(part: Term, isBelow: Kernel.Thm, partIsForm: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
        force(rules.spec(part, earlier).flatMap(rules.mp(_, isBelow)).flatMap(rules.mp(_, partIsForm))
          .flatMap(rules.spec(w, _)).flatMap(rules.mp(_, held)))

      val shapes = unfold(force(rules.spec(y, languageFact(Language.FormulaCases))), yIsForm)
      val taken0 = Set(y, z, x, k, w)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val yIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(everywhere, force(Conv.sym(yIsShape)), force(rules.gen(w, atShape)))
          def belowY(isBelowShape: Kernel.Thm, part: Term, yIsShape: Kernel.Thm): Kernel.Thm =
            moved(t => applied(below, List(part, t)), force(Conv.sym(yIsShape)), isBelowShape)
          def assuming(shape: Term)(proved: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
            val premise = freeForm(w, substituted(shape))
            force(rules.disch(premise, proved(assumed(premise))))
          }
          def through(substitution: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
            moved(t => freeForm(w, t), substitution, held)
          val (equalityCase, rest1) = disjuncts(alternatives.conclusion)
          val (negationCase, rest2) = disjuncts(rest1)
          val (implicationCase, universalCase) = disjuncts(rest2)
          def pairCase(held: Kernel.Thm)(proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, pieces) =>
                val yIsShape = force(Conv.trans(yIsCode, codeCongruence(tagIs, force(rules.conjElim1(pieces)))))
                proceed(u, v, yIsShape, force(rules.conjElim2(pieces)))
              }
            }
          }
          /** Free in one side of a pair of the substituted shape, so free in that side of the shape. */
          def eitherSide(
            either: Kernel.Thm,
            u: Term,
            v: Term,
            freeIn: (Term, Term) => Term,
            folding: Kernel.Thm,
            atSide: (Term, Boolean, Kernel.Thm) => Kernel.Thm
          ): Kernel.Thm = {
            val (leftPremise, rightPremise) = disjuncts(either.conclusion)
            def side(part: Term, first: Boolean, premise: Term): Kernel.Thm = {
              val survived = atSide(part, first, assumed(premise))
              val here = force(rules.conjElim1(survived))
              val inPair =
                if (first) force(rules.disjIntro1(freeIn(w, v), here))
                else force(rules.disjIntro2(freeIn(w, u), here))
              force(rules.conjIntro(fold(folding, inPair), force(rules.conjElim2(survived))))
            }
            force(rules.disjElim(either, side(u, first = true, leftPremise), side(v, first = false, rightPremise)))
          }

          // An equation: the term lemma at whichever side the variable is free in.
          val asEquality = pairCase(assumed(equalityCase)) { (u, v, yIsShape, terms) =>
            val shape = code(5, pair(u, v))
            back(assuming(shape) { held =>
              val atPair = through(apply(languageFact(Language.FormulaSubstituteEquality), List(x, nk, u, v)), held)
              val either = unfold(apply(languageFact(Language.FormulaFreeEquality),
                List(w, applied(substituting, List(x, nk, u)), applied(substituting, List(x, nk, v)))), atPair)
              eitherSide(either, u, v, freeTerm, apply(languageFact(Language.FormulaFreeEquality), List(w, u, v)),
                (part, first, premise) => termSurvivor(part,
                  force(if (first) rules.conjElim1(terms) else rules.conjElim2(terms)), premise))
            }, yIsShape)
          }

          // A negation: the hypothesis at its body.
          val asNegation = {
            val held0 = assumed(negationCase)
            val shape = code(6, b)
            val yIsShape = force(Conv.trans(yIsCode, codeCongruence(force(rules.conjElim1(held0)), refl(b))))
            val isBelow = belowY(belowCode(6, b), b, yIsShape)
            back(assuming(shape) { held =>
              val atNegation = through(apply(languageFact(Language.FormulaSubstituteNegation), List(x, nk, b)), held)
              val inner = unfold(apply(languageFact(Language.FormulaFreeNegation), List(w, substituted(b))), atNegation)
              val survived = survivor(b, isBelow, force(rules.conjElim2(held0)), inner)
              val atShape = fold(apply(languageFact(Language.FormulaFreeNegation), List(w, b)),
                force(rules.conjElim1(survived)))
              force(rules.conjIntro(atShape, force(rules.conjElim2(survived))))
            }, yIsShape)
          }

          // An implication: the hypothesis at whichever side the variable is free in.
          val asImplication = pairCase(assumed(implicationCase)) { (u, v, yIsShape, forms) =>
            val shape = code(7, pair(u, v))
            back(assuming(shape) { held =>
              val atPair = through(apply(languageFact(Language.FormulaSubstituteImplication), List(x, nk, u, v)), held)
              val either = unfold(apply(languageFact(Language.FormulaFreeImplication),
                List(w, substituted(u), substituted(v))), atPair)
              eitherSide(either, u, v, freeForm, apply(languageFact(Language.FormulaFreeImplication), List(w, u, v)),
                (part, first, premise) => survivor(part, belowY(belowPair(7, u, v, first), part, yIsShape),
                  force(if (first) rules.conjElim1(forms) else rules.conjElim2(forms)), premise))
            }, yIsShape)
          }

          // A universal: over `x` the variable is bound and so is not `x`; over another index, the
          // hypothesis at the body, unless the universal binds the variable asked about.
          val asUniversal = pairCase(assumed(universalCase)) { (u, v, yIsShape, vIsForm) =>
            val shape = code(8, pair(u, v))
            val substitution = apply(languageFact(Language.FormulaSubstituteUniversal), List(x, nk, u, v))
            val (_, stopped, under) = branches(sides(substitution)._2)
            def freeClause(body: Term): Kernel.Thm = apply(languageFact(Language.FormulaFreeUniversal), List(w, u, body))
            back(assuming(shape) { held =>
              val goal = conj(freeForm(w, shape), apart)
              split(equal(u, x))(
                isX => {
                  val atShape = through(chained(substitution, taken(isX, stopped, under)), held)
                  val (_, never, inside) = branches(sides(freeClause(v))._2)
                  val wIsX = equal(w, x)
                  val uIsW = chained(isX, force(Conv.sym(assumed(wIsX))))
                  val falsity = unfold(chained(freeClause(v), takenAt(uIsW, never, inside)), atShape)
                  force(rules.notIntro(wIsX, falsity).flatMap(rules.conjIntro(atShape, _)))
                },
                notX => {
                  val atUnder = through(chained(substitution, passed(notX, stopped, under)), held)
                  val reading = unfold(freeClause(substituted(v)), atUnder)
                  val (_, never, inside) = branches(reading.conclusion)
                  split(equal(u, w))(
                    isW => force(rules.falsityElim(goal, unfold(takenAt(isW, never, inside), reading))),
                    notW => {
                      val inner = unfold(passedAt(notW, never, inside), reading)
                      val survived = survivor(v, belowY(belowPair(8, u, v, first = false), v, yIsShape), vIsForm, inner)
                      val (_, neverHere, insideHere) = branches(sides(freeClause(v))._2)
                      val atShape = fold(chained(freeClause(v), passedAt(notW, neverHere, insideHere)),
                        force(rules.conjElim1(survived)))
                      force(rules.conjIntro(atShape, force(rules.conjElim2(survived))))
                    })
                })
            }, yIsShape)
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(rules.disch(isFormula(y), reached).flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(y, _)))
      val p = Term.variable("p", numbers)
      force(rules.mp(instance, step).flatMap(rules.spec(p, _)).flatMap(rules.genAll(_, List(x, k, p))))
    }

    /* ------------------------------------------------- the truth of a universal below a numeral */

    private val universals = force(logic.universalAt(numbers))
    private val successorConstant = constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
    private val arithmeticSum = constant(Peano.Addition, arithmetic)
    private def headOf(t: Term): Term = t match {
      case App(head, _) => head
      case other => throw new RefusedHere(NotOfForm("an application", other))
    }

    /**
     * What the order's bound is, for the two facts each about the order and the bounded universal:
     * a numeral, worth `n` everywhere, or a variable `v_k`, worth `e k` wherever the witness `z` and
     * the quantified index are not `k`. Everything else in the two proofs is the same, and is written
     * once in [[lessTruth]] and [[allBelowTruth]] with this deciding the three places they differ: the
     * code of the bound, its value, and the conditions it costs.
     */
    private sealed trait Bound {
      /** The bound's own variable, `n` or `k`, quantified in the statement after `z` and `i`. */
      def variable: FVar
      def code: Term
      def valueAt(e: Term): Term
    }
    private object Bound {
      final class AtNumeral extends Bound {
        val variable: FVar = Term.variable("n", numbers)
        val code: Term = numeral(variable)
        def valueAt(e: Term): Term = variable
      }
      final class AtVariable extends Bound {
        val variable: FVar = Term.variable("k", numbers)
        val code: Term = Evaluation.this.code(0, variable)
        def valueAt(e: Term): Term = applied(e, List(variable))
      }
    }

    /** [[TrueLessNumeral]], the order's code read through the existential it abbreviates. */
    def trueLessNumeral(g: Grounding): Kernel.Thm = lessTruth(g, new Bound.AtNumeral)

    /** [[TrueLessVariable]], the same below a variable that is not the witness. */
    def trueLessVariable(g: Grounding): Kernel.Thm = lessTruth(g, new Bound.AtVariable)

    private def lessTruth(g: Grounding, bound: Bound): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val e = environment
      val z = Term.variable("z", numbers)
      val i = Term.variable("i", numbers)
      val n = bound.variable
      val nn = bound.code
      val limit = bound.valueAt(e)
      val apartTerm = denial(equal(z, i))
      val apart = assumed(apartTerm)
      val notIZ = force(rules.notIntro(equal(i, z),
        force(rules.notElim(apart, force(Conv.sym(assumed(equal(i, z))))))))
      // a variable bound is read at the witness's update, which passes it by when it is not `z`
      val boundApartTerm = denial(equal(n, z))
      val boundPassed: Vector[Kernel.Thm] = bound match {
        case _: Bound.AtNumeral => Vector(g.valueNumeral)
        case _: Bound.AtVariable => Vector.empty
      }

      // NUM_LESS z v_i n = NUM_EXISTS z body = ~(!v_z. ~body), coded
      val lessUnfold = apply(languageFact(Language.LessCases), List(z, code(0, i), nn))
      val (lessCode, existential) = sides(lessUnfold)
      val body = arguments(existential)._2
      val existsUnfold = apply(languageFact(Language.ExistsCases), List(z, body))
      val universal = arguments(sides(existsUnfold)._2)._2
      val outer = chained(force(Conv.apTerm(truth, chained(lessUnfold, existsUnfold)).flatMap(Conv.apThm(_, e))),
        apply(trueNegation, List(e, universal))) // TRUE less e = ~TRUE (!v_z. ~body) e

      val d = Conv.freshVariable("d", numbers, Set(e, z, i, n))
      val ei = applied(e, List(i))
      val passedBound = bound match {
        case _: Bound.AtNumeral => Vector.empty
        case _: Bound.AtVariable => Vector(passed(assumed(boundApartTerm), d, limit))
      }
      val atD = unfolded(
        Vector(trueNegation, trueEquality, valueSum, valueSuccessor, g.valueVariable) ++ boundPassed ++
          passedBound ++ Vector(passed(notIZ, d, ei), taken(refl(z), d, applied(e, List(z)))),
        applied(truth, List(code(6, body), updated(e, z, d)))) // = ~(e i + SUC d = limit)
      val quantified = chained(apply(g.trueUniversal, List(e, z, code(6, body))),
        force(LogicError.lift(Kernel.abs(d, atD)).flatMap(Conv.apTerm(universals, _))))
      val read = chained(outer, force(Conv.apTerm(headOf(denial(applied(truth, List(universal, e)))), quantified)))
      val reading = sides(read)._2 // ~(!d. ~(e i + SUC d = limit))

      // `e i < limit` is `NUM_LE (SUC (e i)) limit`, which is `?d. SUC (e i) + d = limit`, and the
      // shift moves the successor across.
      val lt = applied(below, List(ei, limit))
      val gap = force(for {
        strict <- numbering.peano.definition(Peano.StrictOrder)
        atMost <- numbering.peano.definition(Peano.NonStrictOrder)
        first <- Conv.unfold(strict, List(ei, limit))
        second <- Conv.unfold(atMost, List(applied(successorConstant, List(ei)), limit))
        joined <- Conv.trans(first, second)
      } yield joined) // e i < limit = ?d. SUC (e i) + d = limit
      val shift = force(numbering.peano.fact(Peano.Shift))
      def shifted(at: Term): Kernel.Thm = force(rules.specAll(shift, List(ei, at))) // e i + SUC d = SUC (e i) + d

      val backward = {
        val held = assumed(lt)
        val denied = force(logic.destNot(reading).toRight(NotOfForm("a negation", reading)))
        val absurd = opened(unfold(gap, held), "d", Set(e, z, i, n)) { (w, atW) =>
          val atWitness = chained(shifted(w), atW) // e i + SUC w = limit
          val instance = force(rules.spec(w, assumed(denied)))
          force(rules.notElim(instance, atWitness))
        }
        force(rules.notIntro(denied, absurd)) // under `lt`: the reading
      }
      val forward = {
        val held = assumed(reading)
        force(g.classical.cases(lt, assumed(lt), {
          val notLt = assumed(denial(lt))
          val w = Conv.freshVariable("w", numbers, Set(e, z, i, n, d))
          val sum = equal(applied(arithmeticSum, List(ei, applied(successorConstant, List(w)))), limit)
          val reached = fold(gap, introduced(sides(gap)._2, w, chained(force(Conv.sym(shifted(w))), assumed(sum))))
          val never = force(rules.notElim(notLt, reached).flatMap(rules.notIntro(sum, _)))
          val everywhere = force(rules.gen(w, never))
          force(rules.notElim(held, everywhere).flatMap(rules.falsityElim(lt, _)))
        }))
      }
      val equivalent = Kernel.deductAntisym(backward, forward) // reading = lt
      val result = chained(read, equivalent)
      val discharged = bound match {
        case _: Bound.AtNumeral => result
        case _: Bound.AtVariable => force(rules.disch(boundApartTerm, result))
      }
      force(rules.disch(apartTerm, discharged).flatMap(rules.genAll(_, List(e, z, i, n))))
    }

    /** [[TrueAllBelowNumeral]]: the universal's truth read at each instance below the numeral. */
    def trueAllBelowNumeral(g: Grounding, lessTruth: Kernel.Thm): Kernel.Thm =
      allBelowTruth(g, lessTruth, new Bound.AtNumeral)

    /** [[TrueAllBelowVariable]]: the same below a variable that is neither the index nor the witness. */
    def trueAllBelowVariable(g: Grounding, lessTruth: Kernel.Thm): Kernel.Thm =
      allBelowTruth(g, lessTruth, new Bound.AtVariable)

    private def allBelowTruth(g: Grounding, lessTruth: Kernel.Thm, bound: Bound): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val e = environment
      val z = Term.variable("z", numbers)
      val i = Term.variable("i", numbers)
      val n = bound.variable
      val p = Term.variable("p", numbers)
      val nn = bound.code
      val apartTerm = denial(equal(z, i))
      val apart = assumed(apartTerm)
      val notIndexTerm = denial(equal(n, i))
      val notWitnessTerm = denial(equal(n, z))

      val unfolding = apply(languageFact(Language.AllBelowCases), List(z, i, nn, p))
      val coded = sides(unfolding)._2 // !v_i. NUM_LESS z v_i n ==> p, coded
      val implication = arguments(arguments(coded)._2)._2
      val less = arguments(arguments(implication)._2)._1
      val opening = chained(force(Conv.apTerm(truth, unfolding).flatMap(Conv.apThm(_, e))),
        apply(g.trueUniversal, List(e, i, implication)))

      val m = Conv.freshVariable("m", numbers, Set(e, z, i, n, p))
      val em = updated(e, i, m)
      // TRUE less e[i := m] = e[i := m] i < bound, and a variable bound read past the update at `i`
      val (lessAt, boundAt) = bound match {
        case _: Bound.AtNumeral => (apply(lessTruth, List(em, z, i, n), apart), Vector.empty)
        case _: Bound.AtVariable =>
          (apply(lessTruth, List(em, z, i, n), apart, assumed(notWitnessTerm)),
            Vector(passed(assumed(notIndexTerm), m, applied(e, List(n)))))
      }
      val limit = chained(lessAt, unfolded(Vector(taken(refl(i), m, applied(e, List(i)))) ++ boundAt, sides(lessAt)._2))
      val body = chained(apply(g.trueImplication, List(em, less, p)),
        force(Conv.apTerm(headOf(headOf(imp(applied(truth, List(less, em)), applied(truth, List(p, em))))), limit).flatMap(Conv.apThm(_, applied(truth, List(p, em))))))
      val result = chained(opening, force(LogicError.lift(Kernel.abs(m, body)).flatMap(Conv.apTerm(universals, _))))
      val discharged = bound match {
        case _: Bound.AtNumeral => result
        case _: Bound.AtVariable =>
          force(rules.disch(notWitnessTerm, result).flatMap(rules.disch(notIndexTerm, _)))
      }
      force(rules.disch(apartTerm, discharged).flatMap(rules.genAll(_, List(e, z, i, n, p))))
    }

    /* --------------------------------------------------------- the Sigma-1 class and its truth */

    private val sigmaOf = constant(SigmaName, Type.fun(numbers, property))
    private def sigma(n: Term, s: Term): Term = applied(sigmaOf, List(n, s))
    private val zeroNumber = constant(Natural.NumberZero, numbers)
    private val existsOf = constant(Language.ExistsName, arithmetic)
    private def exists(j: Term, s: Term): Term = applied(existsOf, List(j, s))

    /** `!n. claim n`, by induction on `n` from the case at zero and the step `!n. claim n ==> claim (SUC n)`. */
    private def inducted(n: FVar, claim: Term => Term)(base: Kernel.Thm, step: Kernel.Thm): Kernel.Thm = {
      val induction = force(numbering.peano.naturals.fact(Natural.Induction))
      val predicate = force(LogicError.lift(Term.abs(n, claim(n))))
      val instance = force(rules.spec(predicate, induction).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      force(rules.mp(instance, force(rules.conjIntro(base, step))))
    }

    /** `goal`, a chain of existentials, from its body at the witnesses in order. */
    private def witnessed(goal: Term, witnesses: List[Term], proved: Kernel.Thm): Kernel.Thm = witnesses match {
      case Nil => proved
      case witness :: rest =>
        val predicate = logic.destExistsPredicate(goal)
          .getOrElse(throw new RefusedHere(NotOfForm("an existential", goal)))
        val inner = sides(force(LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaNormalise)))._2
        introduced(goal, witness, witnessed(inner, rest, proved))
    }

    /**
     * What `NUM_SIGMA (SUC n) s` holds, opened: `proceed` is handed the existential's index `j`, its
     * body `q`, `s = NUM_EXISTS j q` and `NUM_SIGMA n q`.
     */
    private def existentialOf(sig: Sigmas, n: Term, s: Term, held: Kernel.Thm, avoid: Set[FVar])(
      proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val opening = unfold(apply(sig.successor, List(n, s)), held)
      opened(opening, "j", avoid) { (j, withJ) =>
        opened(withJ, "q", avoid + j) { (q, both) =>
          proceed(j, q, force(rules.conjElim1(both)), force(rules.conjElim2(both)))
        }
      }
    }

    /** `NUM_SIGMA (SUC n) (NUM_EXISTS j q)` from `NUM_SIGMA n q`. */
    private def existentialIn(sig: Sigmas, n: Term, j: Term, q: Term, held: Kernel.Thm): Kernel.Thm = {
      val shape = exists(j, q)
      val clause = apply(sig.successor, List(n, shape))
      fold(clause, witnessed(sides(clause)._2, List(j, q), force(rules.conjIntro(refl(shape), held))))
    }

    /** [[SigmaForm]]: down the prefix, each existential of a formula being a formula. */
    def sigmaForm(sig: Sigmas): Kernel.Thm = {
      val n = Term.variable("n", numbers)
      val p = Term.variable("p", numbers)
      def claim(at: Term): Term = force(logic.mkForall(p, imp(sigma(at, p), isFormula(p))))

      val base = {
        val held = assumed(sigma(zeroNumber, p))
        val form = force(rules.conjElim1(unfold(apply(sig.zero, List(p)), held)))
        force(rules.disch(sigma(zeroNumber, p), form).flatMap(rules.gen(p, _)))
      }
      val step = {
        val hypothesis = assumed(claim(n))
        val above = sigma(applied(successorConstant, List(n)), p)
        val form = existentialOf(sig, n, p, assumed(above), Set(n, p)) { (j, q, pIs, qSigma) =>
          val qForm = apply(hypothesis, List(q), qSigma)
          val whole = apply(languageFact(Language.ExistsFormula), List(j, q), qForm)
          moved(isFormula, force(Conv.sym(pIs)), whole)
        }
        val atSuccessor = force(rules.disch(above, form).flatMap(rules.gen(p, _)))
        force(rules.disch(claim(n), atSuccessor).flatMap(rules.gen(n, _)))
      }
      inducted(n, claim)(base, step)
    }

    /** [[SigmaAtNumeral]]: down the prefix, the substitution stopping at an existential over `x`. */
    def sigmaAtNumeral(g: Grounding, sig: Sigmas, boundedAt: Kernel.Thm): Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val n = Term.variable("n", numbers)
      val x = Term.variable("x", numbers)
      val k = Term.variable("k", numbers)
      val p = Term.variable("p", numbers)
      val nk = numeral(k)
      def substituted(s: Term): Term = applied(formulaSubstituting, List(x, nk, s))
      def claim(at: Term): Term =
        force(logic.mkForall(x, force(logic.mkForall(k, force(logic.mkForall(p,
          imp(sigma(at, p), sigma(at, substituted(p)))))))))

      val base = {
        val held = assumed(sigma(zeroNumber, p))
        val both = unfold(apply(sig.zero, List(p)), held)
        val form = force(rules.conjElim1(both))
        val keptForm = apply(languageFact(Language.FormulaSubstituteKeepsFormulas), List(x, nk, p),
          form, numeralTerm(k))
        val keptBounded = apply(boundedAt, List(x, k, p), form, force(rules.conjElim2(both)))
        val kept = fold(apply(sig.zero, List(substituted(p))), force(rules.conjIntro(keptForm, keptBounded)))
        force(rules.disch(sigma(zeroNumber, p), kept).flatMap(rules.genAll(_, List(x, k, p))))
      }
      val step = {
        val hypothesis = assumed(claim(n))
        val successorN = applied(successorConstant, List(n))
        val above = sigma(successorN, p)
        val kept = existentialOf(sig, n, p, assumed(above), Set(n, x, k, p)) { (j, q, pIs, qSigma) =>
          val shape = exists(j, q)
          val through = apply(languageFact(Language.ExistsSubstitute), List(x, nk, j, q))
          // NUM_SUBST_FORM x nk (NUM_EXISTS j q) = COND (j = x) (NUM_EXISTS j q) (NUM_EXISTS j (subst q))
          val atShape = split(equal(j, x))(
            isX => {
              val stopped = chained(through, taken(isX, shape, exists(j, substituted(q))))
              moved(t => sigma(successorN, t), force(Conv.sym(stopped)), existentialIn(sig, n, j, q, qSigma))
            },
            notX => {
              val under = chained(through, passed(notX, shape, exists(j, substituted(q))))
              val inner = apply(hypothesis, List(x, k, q), qSigma)
              moved(t => sigma(successorN, t), force(Conv.sym(under)),
                existentialIn(sig, n, j, substituted(q), inner))
            })
          moved(t => sigma(successorN, substituted(t)), force(Conv.sym(pIs)), atShape)
        }
        val atSuccessor = force(rules.disch(above, kept).flatMap(rules.genAll(_, List(x, k, p))))
        force(rules.disch(claim(n), atSuccessor).flatMap(rules.gen(n, _)))
      }
      inducted(n, claim)(base, step)
    }

    /** [[TrueExists]]: the existential's code read through its three clauses, then classically. */
    def trueExists(g: Grounding): Kernel.Thm = {
      val e = environment
      val j = Term.variable("j", numbers)
      val p = Term.variable("p", numbers)
      val unfolding = apply(languageFact(Language.ExistsCases), List(j, p))
      val universal = arguments(sides(unfolding)._2)._2 // !v_j. ~p, coded
      val outer = chained(force(Conv.apTerm(truth, unfolding).flatMap(Conv.apThm(_, e))),
        apply(trueNegation, List(e, universal))) // = ~TRUE (!v_j. ~p) e

      val m = Conv.freshVariable("m", numbers, Set(e, j, p))
      val em = updated(e, j, m)
      val atM = apply(trueNegation, List(em, p)) // TRUE ~p e[j := m] = ~TRUE p e[j := m]
      val quantified = chained(apply(g.trueUniversal, List(e, j, code(6, p))),
        force(LogicError.lift(Kernel.abs(m, atM)).flatMap(Conv.apTerm(universals, _))))
      val read = chained(outer, force(Conv.apTerm(headOf(denial(applied(truth, List(universal, e)))), quantified)))
      val reading = sides(read)._2 // ~(!m. ~TRUE p e[j := m])

      val holds = applied(truth, List(p, em))
      val target = force(logic.mkExists(m, holds))
      val backward = {
        val denied = force(logic.destNot(reading).toRight(NotOfForm("a negation", reading)))
        val absurd = opened(assumed(target), "m", Set(e, j, p)) { (w, atW) =>
          force(rules.spec(w, assumed(denied)).flatMap(rules.notElim(_, atW)))
        }
        force(rules.notIntro(denied, absurd)) // under the existential: the reading
      }
      val forward = force(g.classical.cases(target, assumed(target), {
        val never = assumed(denial(target))
        val w = Conv.freshVariable("w", numbers, Set(e, j, p, m))
        val atW = applied(truth, List(p, updated(e, j, w)))
        val refuted = force(rules.notElim(never, introduced(target, w, assumed(atW))).flatMap(rules.notIntro(atW, _)))
        val everywhere = force(rules.gen(w, refuted))
        force(rules.notElim(assumed(reading), everywhere).flatMap(rules.falsityElim(target, _)))
      }))
      val result = chained(read, Kernel.deductAntisym(backward, forward))
      force(rules.genAll(result, List(e, j, p)))
    }

    /** [[ProvesSigma]]: down the prefix at a fixed environment, a witness for each existential. */
    def provesSigma(
      g: Grounding,
      sig: Sigmas,
      sigmaIsForm: Kernel.Thm,
      sigmaAt: Kernel.Thm,
      existsTruth: Kernel.Thm,
      truthAtNumeral: Kernel.Thm,
      freeFormAt: Kernel.Thm,
      complete: Kernel.Thm
    ): Kernel.Thm = {
      val propositions = new Propositions(g)
      import propositions.*
      val e = environment
      val n = Term.variable("n", numbers)
      val p = Term.variable("p", numbers)
      val w = Term.variable("w", numbers)
      def closed(s: Term): Term = force(logic.mkForall(w, denial(freeForm(w, s))))
      def truthAt(s: Term): Term = applied(truth, List(s, e))
      def claimFor(at: Term, s: Term): Term = imp(sigma(at, s), imp(closed(s), imp(truthAt(s), provable(s))))
      def claim(at: Term): Term = force(logic.mkForall(p, claimFor(at, p)))
      def discharged(at: Term, s: Term, proved: Kernel.Thm): Kernel.Thm =
        force(rules.disch(truthAt(s), proved).flatMap(rules.disch(closed(s), _)).flatMap(rules.disch(sigma(at, s), _)))

      val base = {
        val both = unfold(apply(sig.zero, List(p)), assumed(sigma(zeroNumber, p)))
        val decided = apply(complete, List(e, p), force(rules.conjElim1(both)), force(rules.conjElim2(both)),
          assumed(closed(p)))
        val proved = force(rules.mp(force(rules.conjElim1(decided)), assumed(truthAt(p))))
        force(rules.gen(p, discharged(zeroNumber, p, proved)))
      }
      val step = {
        val hypothesis = assumed(claim(n))
        val successorN = applied(successorConstant, List(n))
        val pClosed = assumed(closed(p))
        val proved = existentialOf(sig, n, p, assumed(sigma(successorN, p)), Set(e, n, p)) { (j, q, pIs, qSigma) =>
          val qForm = apply(sigmaIsForm, List(n, q), qSigma)
          val shape = exists(j, q)
          val back = force(Conv.sym(pIs))
          val shapeTrue = moved(truthAt, pIs, assumed(truthAt(p)))
          val witnesses = unfold(apply(existsTruth, List(e, j, q)), shapeTrue)
          opened(witnesses, "m", Set(e, n, p, j, q)) { (m, atM) =>
            val instance = applied(formulaSubstituting, List(j, numeral(m), q))
            val instanceTrue = fold(force(rules.specAll(truthAtNumeral, List(j, m, q)).flatMap(rules.mp(_, qForm))
              .flatMap(rules.spec(e, _))), atM)
            val instanceSigma = apply(sigmaAt, List(n, j, m, q), qSigma)
            val instanceClosed = {
              val f = Conv.freshVariable("f", numbers, Set(e, n, p, j, q, m))
              val premise = freeForm(f, instance)
              val survived = force(rules.specAll(freeFormAt, List(j, m, q)).flatMap(rules.mp(_, qForm))
                .flatMap(rules.spec(f, _)).flatMap(rules.mp(_, assumed(premise)))) // free f q /\ ~(f = j)
              val (l, r) = Term.destEq(logic.destNot(force(rules.conjElim2(survived)).conclusion).get).get
              val flipped = equal(r, l)
              val jNotF = force(rules.notElim(force(rules.conjElim2(survived)), force(Conv.sym(assumed(flipped))))
                .flatMap(rules.notIntro(flipped, _)))
              val clause = apply(languageFact(Language.ExistsFree), List(f, j, q))
              val (_, never, inside) = branches(sides(clause)._2)
              val atShape = fold(chained(clause, passedAt(jNotF, never, inside)), force(rules.conjElim1(survived)))
              val atWhole = moved(t => freeForm(f, t), back, atShape)
              force(rules.spec(f, pClosed).flatMap(rules.notElim(_, atWhole)).flatMap(rules.notIntro(premise, _))
                .flatMap(rules.gen(f, _)))
            }
            val instanceProved = apply(hypothesis, List(instance), instanceSigma, instanceClosed, instanceTrue)
            val introducedShape = apply(deductionFact(Deduction.ExistentialIntroduction), List(j, numeral(m), q),
              qForm, numeralTerm(m), numeralClosed(m), instanceProved)
            moved(provable, back, introducedShape)
          }
        }
        val atSuccessor = force(rules.gen(p, discharged(successorN, p, proved)))
        force(rules.disch(claim(n), atSuccessor).flatMap(rules.gen(n, _)))
      }
      val all = inducted(n, claim)(base, step)
      force(rules.spec(n, all).flatMap(rules.spec(p, _)).flatMap(rules.genAll(_, List(n, e, p))))
    }

    /* ----------------------------------- a numeral put for each variable below n, and the bridge */

    private val instanceOf =
      constant(InstanceName, Type.fun(numbers, Type.fun(environments, Type.fun(numbers, numbers))))
    private def instance(n: Term, s: Term, p: Term): Term = applied(instanceOf, List(n, s, p))
    private val instanceSource = Term.variable("s", environments)
    private def sent(s: Term, i: Term): Term = applied(s, List(i))

    /** `INST 0 s p = p` and `INST (SUC n) s p = SUBST n (numeral (s n)) (INST n s p)`. */
    private def atZero(ins: Instances, s: Term, p: Term): Kernel.Thm = force(rules.specAll(ins.zero, List(s, p)))
    private def atSuccessor(ins: Instances, n: Term, s: Term, p: Term): Kernel.Thm =
      force(rules.specAll(ins.successor, List(n, s, p)))

    /** `!n. claim n` from the case at zero and the step, the induction every fact here makes. */
    private def onInstances(claim: Term => Term)(base: Kernel.Thm)(step: (FVar, Kernel.Thm) => Kernel.Thm)
      : Kernel.Thm = {
      val n = Term.variable("n", numbers)
      val reached = step(n, assumed(claim(n)))
      inducted(n, claim)(base, force(rules.disch(claim(n), reached).flatMap(rules.gen(n, _))))
    }

    /** [[InstanceForm]]: each substitution of a numeral keeps a formula a formula. */
    def instanceForm(ins: Instances): Kernel.Thm = {
      val s = instanceSource
      val p = Term.variable("p", numbers)
      def claim(at: Term): Term = force(logic.mkForall(s, force(logic.mkForall(p,
        imp(isFormula(p), isFormula(instance(at, s, p)))))))
      val held = assumed(isFormula(p))
      val base = force(rules.disch(isFormula(p), moved(isFormula, force(Conv.sym(atZero(ins, s, p))), held))
        .flatMap(rules.genAll(_, List(s, p))))
      onInstances(claim)(base) { (n, hypothesis) =>
        val below = apply(hypothesis, List(s, p), held)
        val kept = apply(languageFact(Language.FormulaSubstituteKeepsFormulas),
          List(n, numeral(sent(s, n)), instance(n, s, p)), below, numeralTerm(sent(s, n)))
        val whole = moved(isFormula, force(Conv.sym(atSuccessor(ins, n, s, p))), kept)
        force(rules.disch(isFormula(p), whole).flatMap(rules.genAll(_, List(s, p))))
      }
    }

    /** [[InstanceBounded]]: [[BoundedAtNumeral]] at each step. */
    def instanceBounded(ins: Instances, instanceIsForm: Kernel.Thm, boundedAt: Kernel.Thm): Kernel.Thm = {
      val s = instanceSource
      val p = Term.variable("p", numbers)
      def claim(at: Term): Term = force(logic.mkForall(s, force(logic.mkForall(p,
        imp(isFormula(p), imp(bounded(p), bounded(instance(at, s, p))))))))
      val form = assumed(isFormula(p))
      val held = assumed(bounded(p))
      def discharged(proved: Kernel.Thm): Kernel.Thm =
        force(rules.disch(bounded(p), proved).flatMap(rules.disch(isFormula(p), _)).flatMap(rules.genAll(_, List(s, p))))
      val base = discharged(moved(bounded, force(Conv.sym(atZero(ins, s, p))), held))
      onInstances(claim)(base) { (n, hypothesis) =>
        val belowForm = apply(instanceIsForm, List(n, s, p), form)
        val belowBounded = apply(hypothesis, List(s, p), form, held)
        val kept = apply(boundedAt, List(n, sent(s, n), instance(n, s, p)), belowForm, belowBounded)
        discharged(moved(bounded, force(Conv.sym(atSuccessor(ins, n, s, p))), kept))
      }
    }

    /** [[InstanceSigma]]: [[SigmaAtNumeral]] at each step, the index of the class held fixed. */
    def instanceSigma(ins: Instances, sigmaAt: Kernel.Thm): Kernel.Thm = {
      val s = instanceSource
      val p = Term.variable("p", numbers)
      val m = Term.variable("m", numbers)
      def claim(at: Term): Term = force(logic.mkForall(s, force(logic.mkForall(p,
        imp(sigma(m, p), sigma(m, instance(at, s, p)))))))
      val held = assumed(sigma(m, p))
      def inClass(t: Term): Term = sigma(m, t)
      def discharged(proved: Kernel.Thm): Kernel.Thm =
        force(rules.disch(sigma(m, p), proved).flatMap(rules.genAll(_, List(s, p))))
      val base = discharged(moved(inClass, force(Conv.sym(atZero(ins, s, p))), held))
      val all = onInstances(claim)(base) { (n, hypothesis) =>
        val below = apply(hypothesis, List(s, p), held)
        val kept = apply(sigmaAt, List(m, n, sent(s, n), instance(n, s, p)), below)
        discharged(moved(inClass, force(Conv.sym(atSuccessor(ins, n, s, p))), kept))
      }
      val n = Term.variable("n", numbers)
      force(rules.specAll(all, List(n, s, p)).flatMap(rules.genAll(_, List(m, n, s, p))))
    }

    /** [[InstanceFree]]: [[FreeFormAtNumeral]] at each step, and the range grown by one. */
    def instanceFree(g: Grounding, ins: Instances, instanceIsForm: Kernel.Thm, freeFormAt: Kernel.Thm)
      : Kernel.Thm = {
      val s = instanceSource
      val p = Term.variable("p", numbers)
      val w = Term.variable("w", numbers)
      def lt(a: Term, b: Term): Term = applied(below, List(a, b))
      def conclusion(at: Term): Term = conj(freeForm(w, p), denial(lt(w, at)))
      def claim(at: Term): Term = force(logic.mkForall(s, force(logic.mkForall(p, imp(isFormula(p),
        force(logic.mkForall(w, imp(freeForm(w, instance(at, s, p)), conclusion(at)))))))))
      val form = assumed(isFormula(p))
      def discharged(at: Term, proved: Kernel.Thm): Kernel.Thm =
        force(rules.disch(freeForm(w, instance(at, s, p)), proved).flatMap(rules.gen(w, _))
          .flatMap(rules.disch(isFormula(p), _)).flatMap(rules.genAll(_, List(s, p))))

      val base = {
        val held = assumed(freeForm(w, instance(zeroNumber, s, p)))
        val freeInP = moved(t => freeForm(w, t), atZero(ins, s, p), held)
        val nowhere = force(rules.spec(w, force(numbering.peano.fact(Peano.NotBelowZero))))
        discharged(zeroNumber, force(rules.conjIntro(freeInP, nowhere)))
      }
      onInstances(claim)(base) { (n, hypothesis) =>
        val successorN = applied(successorConstant, List(n))
        val held = assumed(freeForm(w, instance(successorN, s, p)))
        val freeInStep = moved(t => freeForm(w, t), atSuccessor(ins, n, s, p), held)
        val belowForm = apply(instanceIsForm, List(n, s, p), form)
        val survived = force(rules.specAll(freeFormAt, List(n, sent(s, n), instance(n, s, p)))
          .flatMap(rules.mp(_, belowForm)).flatMap(rules.spec(w, _)).flatMap(rules.mp(_, freeInStep)))
        val notN = force(rules.conjElim2(survived)) // ~(w = n)
        val earlier = force(rules.spec(w, apply(hypothesis, List(s, p), form))
          .flatMap(rules.mp(_, force(rules.conjElim1(survived))))) // free w p /\ ~(w < n)
        val notBelowN = force(rules.conjElim2(earlier))
        val atTop = lt(w, successorN)
        val peeled = apply(force(numbering.peano.fact(Peano.BelowSuccessorCases)), List(n, w), assumed(atTop))
        val absurd = force(rules.disjElim(peeled,
          force(rules.notElim(notBelowN, assumed(lt(w, n)))),
          force(rules.notElim(notN, assumed(equal(w, n))))))
        val notBelowTop = force(rules.notIntro(atTop, absurd))
        discharged(successorN, force(rules.conjIntro(force(rules.conjElim1(earlier)), notBelowTop)))
      }
    }

    /** `\j. COND (j < n) (s j) (e j)`: `s` below `n` and `e` from `n` up. */
    private def readBelow(n: Term, s: Term, e: Term): Term = {
      val j = Conv.freshVariable("j", numbers, Term.freeVariables(n) ++ Term.freeVariables(s) ++ Term.freeVariables(e))
      force(LogicError.lift(Term.abs(j, cond(applied(below, List(j, n)), sent(s, j), sent(e, j)))))
    }

    /** `(\j. f j) = f` at an environment, which is `ETA` and the one place this section spends it. */
    private def etaAt(g: Grounding, f: Term): Kernel.Thm = {
      val eta = Kernel.instType(
        Map(Classical.TypeVariable -> numbers, Classical.CodomainVariable -> numbers),
        force(g.classical.axiom(Classical.Eta)))
      force(rules.spec(f, eta))
    }

    /** `\j. f j`, the abstraction `ETA` equates with `f`. */
    private def expanded(f: Term): Term = {
      val j = Conv.freshVariable("j", numbers, Term.freeVariables(f))
      force(LogicError.lift(Term.abs(j, sent(f, j))))
    }

    /** [[InstanceTrue]]: [[TrueAtNumeral]] at each step, and the two environments met pointwise. */
    def instanceTrue(g: Grounding, ins: Instances, instanceIsForm: Kernel.Thm, truthAtNumeral: Kernel.Thm)
      : Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val s = instanceSource
      val p = Term.variable("p", numbers)
      val e = environment
      def claim(at: Term): Term = force(logic.mkForall(s, force(logic.mkForall(p, imp(isFormula(p),
        force(logic.mkForall(e, equal(applied(truth, List(instance(at, s, p), e)),
          applied(truth, List(p, readBelow(at, s, e)))))))))))
      val form = assumed(isFormula(p))
      def readAt(environmentEquation: Kernel.Thm): Kernel.Thm =
        force(Conv.apTerm(applied(truth, List(p)), environmentEquation))
      def discharged(proved: Kernel.Thm): Kernel.Thm =
        force(rules.gen(e, proved).flatMap(rules.disch(isFormula(p), _)).flatMap(rules.genAll(_, List(s, p))))
      val avoid = Set(s, p, e)

      val base = {
        val unfolded = force(Conv.apTerm(truth, atZero(ins, s, p)).flatMap(Conv.apThm(_, e))) // = TRUE p e
        val nowhere = force(numbering.peano.fact(Peano.NotBelowZero))
        val pointwise = extensional(readBelow(zeroNumber, s, e), expanded(e), avoid) { m =>
          passed(force(rules.spec(m, nowhere)), sent(s, m), sent(e, m))
        }
        val toE = chained(pointwise, etaAt(g, e)) // readBelow 0 s e = e
        discharged(chained(unfolded, readAt(force(Conv.sym(toE)))))
      }
      onInstances(claim)(base) { (n, hypothesis) =>
        val successorN = applied(successorConstant, List(n))
        val q = instance(n, s, p)
        val belowForm = apply(instanceIsForm, List(n, s, p), form)
        val unfolded = force(Conv.apTerm(truth, atSuccessor(ins, n, s, p)).flatMap(Conv.apThm(_, e)))
        val substituted = force(rules.specAll(truthAtNumeral, List(n, sent(s, n), q))
          .flatMap(rules.mp(_, belowForm)).flatMap(rules.spec(e, _))) // = TRUE q e[n := s n]
        val updatedAtN = arguments(sides(substituted)._2)._2
        val inner = force(rules.spec(updatedAtN, apply(hypothesis, List(s, p), form))) // = TRUE p (...)
        val reached = arguments(sides(inner)._2)._2
        val lt = (a: Term, b: Term) => applied(below, List(a, b))
        val transitive = force(numbering.peano.fact(Peano.StrictTransitive))
        val toTop = force(rules.spec(n, force(numbering.peano.fact(Peano.BelowSuccessor)))) // n < SUC n
        val pointwise = extensional(reached, readBelow(successorN, s, e), avoid + n) { m =>
          val sm = sent(s, m)
          val em = sent(e, m)
          val rest = cond(equal(m, n), sent(s, n), em)
          split(lt(m, n))(
            isBelow => {
              val left = taken(isBelow, sm, rest)
              val stillBelow = apply(transitive, List(m, n, successorN), force(rules.conjIntro(isBelow, toTop)))
              same(left, taken(stillBelow, sm, em))
            },
            notBelow =>
              split(equal(m, n))(
                isTop => {
                  val left = chained(passed(notBelow, sm, rest), taken(isTop, sent(s, n), em))
                  val stillBelow = moved(x => lt(x, successorN), force(Conv.sym(isTop)), toTop)
                  val right = chained(taken(stillBelow, sm, em), force(Conv.apTerm(s, isTop)))
                  same(left, right)
                },
                notTop => {
                  val left = chained(passed(notBelow, sm, rest), passed(notTop, sent(s, n), em))
                  val atTop = lt(m, successorN)
                  val peeled = apply(force(numbering.peano.fact(Peano.BelowSuccessorCases)), List(n, m), assumed(atTop))
                  val absurd = force(rules.disjElim(peeled,
                    force(rules.notElim(notBelow, assumed(lt(m, n)))),
                    force(rules.notElim(notTop, assumed(equal(m, n))))))
                  val outside = force(rules.notIntro(atTop, absurd))
                  same(left, passed(outside, sm, em))
                }))
        }
        discharged(chained(unfolded, substituted, inner, readAt(pointwise)))
      }
    }

    /** `NUM_TRUE (INST n s p) s = NUM_TRUE p s`: [[InstanceTrue]] at `s`, whose reading of itself is itself. */
    private def truthAtItself(g: Grounding, instanceIsTrue: Kernel.Thm, n: Term, s: Term, p: Term, form: Kernel.Thm)
      : Kernel.Thm = {
      val conditions = new Conditions(g)
      import conditions.*
      val read = force(rules.spec(s, apply(instanceIsTrue, List(n, s, p), form)))
      val environment = arguments(sides(read)._2)._2
      val pointwise = extensional(environment, expanded(s), Set(n, s, p).flatMap(Term.freeVariables)) { m =>
        val sm = sent(s, m)
        val guard = applied(below, List(m, n))
        split(guard)(isBelow => taken(isBelow, sm, sm), notBelow => passed(notBelow, sm, sm))
      }
      chained(read, force(Conv.apTerm(applied(truth, List(p)), chained(pointwise, etaAt(g, s)))))
    }

    /** `!w. ~NUM_FREE_FORM w (INST n s p)` from `NUM_FORM p` and every free variable of `p` below `n`. */
    private def instanceClosed(
      instanceIsFree: Kernel.Thm, n: Term, s: Term, p: Term, form: Kernel.Thm, covered: Kernel.Thm
    ): Kernel.Thm = {
      val w = Conv.freshVariable("w", numbers, Set(n, s, p).flatMap(Term.freeVariables) ++
        covered.hypotheses.flatMap(Term.freeVariables) ++ form.hypotheses.flatMap(Term.freeVariables))
      val premise = freeForm(w, instance(n, s, p))
      val survived = force(rules.spec(w, apply(instanceIsFree, List(n, s, p), form))
        .flatMap(rules.mp(_, assumed(premise)))) // free w p /\ ~(w < n)
      val inRange = force(rules.spec(w, covered).flatMap(rules.mp(_, force(rules.conjElim1(survived)))))
      force(rules.notElim(force(rules.conjElim2(survived)), inRange)
        .flatMap(rules.notIntro(premise, _)).flatMap(rules.gen(w, _)))
    }

    /** `!w. NUM_FREE_FORM w p ==> w < n`: every free variable of `p` is one the instance replaces. */
    private def coveredBy(n: Term, p: Term): Term = {
      val w = Conv.freshVariable("w", numbers, Term.freeVariables(n) ++ Term.freeVariables(p))
      force(logic.mkForall(w, imp(freeForm(w, p), applied(below, List(w, n)))))
    }

    /** [[ProvesBoundedInstance]]: [[ProvesBounded]] at the instance, read back at `s`. */
    def provesBoundedInstance(
      g: Grounding,
      instanceIsForm: Kernel.Thm,
      instanceIsBounded: Kernel.Thm,
      instanceIsFree: Kernel.Thm,
      instanceIsTrue: Kernel.Thm,
      complete: Kernel.Thm
    ): Kernel.Thm = {
      val n = Term.variable("n", numbers)
      val s = instanceSource
      val p = Term.variable("p", numbers)
      val q = instance(n, s, p)
      val form = assumed(isFormula(p))
      val inClass = assumed(bounded(p))
      val covered = assumed(coveredBy(n, p))
      val decided = apply(complete, List(s, q), apply(instanceIsForm, List(n, s, p), form),
        apply(instanceIsBounded, List(n, s, p), form, inClass),
        instanceClosed(instanceIsFree, n, s, p, form, covered))
      val truthEquation = truthAtItself(g, instanceIsTrue, n, s, p, form) // TRUE q s = TRUE p s
      val holds = applied(truth, List(p, s))
      val proved = force(rules.mp(force(rules.conjElim1(decided)), fold(truthEquation, assumed(holds)))
        .flatMap(rules.disch(holds, _)))
      val fails = denial(holds)
      val refuted = force(rules.mp(force(rules.conjElim2(decided)),
        moved(denial, force(Conv.sym(truthEquation)), assumed(fails))).flatMap(rules.disch(fails, _)))
      force(rules.conjIntro(proved, refuted)
        .flatMap(rules.disch(coveredBy(n, p), _)).flatMap(rules.disch(bounded(p), _))
        .flatMap(rules.disch(isFormula(p), _)).flatMap(rules.genAll(_, List(n, s, p))))
    }

    /** [[ProvesSigmaInstance]]: [[ProvesSigma]] at the instance, read back at `s`. */
    def provesSigmaInstance(
      g: Grounding,
      sigmaIsForm: Kernel.Thm,
      instanceIsForm: Kernel.Thm,
      instanceIsSigma: Kernel.Thm,
      instanceIsFree: Kernel.Thm,
      instanceIsTrue: Kernel.Thm,
      sigmaComplete: Kernel.Thm
    ): Kernel.Thm = {
      val m = Term.variable("m", numbers)
      val n = Term.variable("n", numbers)
      val s = instanceSource
      val p = Term.variable("p", numbers)
      val q = instance(n, s, p)
      val inClass = assumed(sigma(m, p))
      val form = apply(sigmaIsForm, List(m, p), inClass)
      val covered = assumed(coveredBy(n, p))
      val holds = applied(truth, List(p, s))
      val instanceHolds = fold(truthAtItself(g, instanceIsTrue, n, s, p, form), assumed(holds))
      val proved = apply(sigmaComplete, List(m, s, q), apply(instanceIsSigma, List(m, n, s, p), inClass),
        instanceClosed(instanceIsFree, n, s, p, form, covered), instanceHolds)
      force(rules.disch(holds, proved).flatMap(rules.disch(coveredBy(n, p), _))
        .flatMap(rules.disch(sigma(m, p), _)).flatMap(rules.genAll(_, List(m, n, s, p))))
    }

    /* --------------------------------------------- completeness for the closed bounded formulas */

    /**
     * [[ProvesBounded]], by strong induction on the rank, one case per shape of a formula.
     *
     * The rank and not the code, because the universal's case goes to its instances and an
     * instance has a numeral where the universal has a variable. The environment is fixed: an
     * instance's truth at `e` is the body's at `e` with the index sent to the numeral's value,
     * which is the reading `NUM_TRUE_ALL_BELOW_NUMERAL` gives the universal at `e`.
     */
    def provesBounded(
      g: Grounding,
      bounding: Bounding,
      ranking: Ranking,
      trueEq: Kernel.Thm,
      falseEq: Kernel.Thm,
      parts: Kernel.Thm,
      truthAtNumeral: Kernel.Thm,
      boundedAt: Kernel.Thm,
      rankAt: Kernel.Thm,
      freeFormAt: Kernel.Thm,
      allBelowTruth: Kernel.Thm
    ): Kernel.Thm = {
      val propositions = new Propositions(g)
      import propositions.*
      val e = environment
      val negation = constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool))
      val atMost = constant(Peano.NonStrictOrder, Type.fun(numbers, property))
      val belowSuccessor = force(numbering.peano.fact(Peano.BelowSuccessor))
      val strictTransitive = force(numbering.peano.fact(Peano.StrictTransitive))
      val atMostThenBelow = force(numbering.peano.fact(Peano.AtMostThenBelow))
      val atMostSum = force(numbering.peano.fact(Peano.AtMostSum))
      val addCommutative = force(numbering.peano.fact(Peano.AddCommutative))
      val notForall = Kernel.instType(Map(Classical.TypeVariable -> numbers), force(g.classical.fact(Classical.NotForall)))
      def truthAt(s: Term): Term = applied(truth, List(s, e))
      def neg(s: Term): Term = code(6, s)
      def rank(s: Term): Term = applied(rankOf, List(s))
      def successor(s: Term): Term = applied(successorConstant, List(s))
      def sum(l: Term, r: Term): Term = applied(arithmeticSum, List(l, r))
      def lessThan(l: Term, r: Term): Term = applied(below, List(l, r))
      def decided(s: Term): Term = conj(imp(truthAt(s), provable(s)), imp(denial(truthAt(s)), provable(neg(s))))
      val w = Term.variable("w", numbers)
      def closed(s: Term): Term = force(logic.mkForall(w, denial(freeForm(w, s))))
      val n = Term.variable("n", numbers)
      val q = Term.variable("q", numbers)
      def claimFor(s: Term, at: Term): Term =
        imp(equal(rank(s), at), imp(isFormula(s), imp(bounded(s), imp(closed(s), decided(s)))))
      def claimAt(at: Term): Term = force(logic.mkForall(q, claimFor(q, at)))

      def cases(p: Term)(yes: Kernel.Thm => Kernel.Thm, no: Kernel.Thm => Kernel.Thm): Kernel.Thm =
        force(g.classical.cases(p, yes(assumed(p)), no(assumed(denial(p)))))
      def absurd(goal: Term, contradiction: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(goal, contradiction))
      def decidedFrom(subject: Term, whenTrue: Kernel.Thm => Kernel.Thm, whenFalse: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
        val t = truthAt(subject)
        val a = force(rules.disch(t, whenTrue(assumed(t))))
        val b = force(rules.disch(denial(t), whenFalse(assumed(denial(t)))))
        force(rules.conjIntro(a, b))
      }
      /** `PROV q` from `PROV (p ==> q)` and `PROV p`. */
      def detach(p: Term, r: Term, implication: Kernel.Thm, antecedent: Kernel.Thm): Kernel.Thm =
        apply(g.modusPonens, List(p, r), implication, antecedent)
      /** `~(r = l)` from `~(l = r)`. */
      def turned(denied: Kernel.Thm): Kernel.Thm = {
        val (l, r) = Term.destEq(logic.destNot(denied.conclusion)
          .getOrElse(throw new RefusedHere(NotOfForm("a negation", denied.conclusion))))
          .getOrElse(throw new RefusedHere(NotOfForm("a denied equation", denied.conclusion)))
        val flipped = equal(r, l)
        force(rules.notElim(denied, force(Conv.sym(assumed(flipped)))).flatMap(rules.notIntro(flipped, _)))
      }
      /**
       * `!f. ~(free f part)`, from `!f. ~(free f whole)` and `free f part ==> free f whole` at a
       * fresh `f`: a part of a closed formula, or an instance of a closed universal, is closed.
       */
      def nowhereFree(freeIn: (Term, Term) => Term, part: Term, wholeClosed: Kernel.Thm, avoid: Set[FVar])(
        lift: (FVar, Kernel.Thm) => Kernel.Thm
      ): Kernel.Thm = {
        val f = Conv.freshVariable("f", numbers, avoid ++ Term.freeVariables(part) ++
          Term.freeVariables(wholeClosed.conclusion) ++ wholeClosed.hypotheses.flatMap(Term.freeVariables))
        val premise = freeIn(f, part)
        val atWhole = lift(f, assumed(premise))
        force(rules.spec(f, wholeClosed).flatMap(rules.notElim(_, atWhole)).flatMap(rules.notIntro(premise, _))
          .flatMap(rules.gen(f, _)))
      }

      val z = Term.variable("z", numbers)
      val strong = force(numbering.peano.fact(Peano.StrongInduction))
      val predicate = force(LogicError.lift(Term.abs(n, claimAt(n))))
      val instance = force(rules.spec(predicate, strong).flatMap(theorem =>
        Conv.betaNormalise(theorem.conclusion).flatMap(reduced => LogicError.lift(Kernel.eqMp(reduced, theorem)))))
      val hypothesis = force(logic.mkForall(z, imp(lessThan(z, n), claimAt(z))))
      val earlier = assumed(hypothesis)
      val qRank = assumed(equal(rank(q), n))
      val qForm = assumed(isFormula(q))
      val qBounded = assumed(bounded(q))
      val qClosed = assumed(closed(q))
      /** `decided(part)`, from the hypothesis at the part's rank. */
      def atPart(part: Term, rankBelow: Kernel.Thm, form: Kernel.Thm, isBounded: Kernel.Thm, isClosed: Kernel.Thm)
        : Kernel.Thm =
        force(rules.spec(rank(part), earlier).flatMap(rules.mp(_, rankBelow)).flatMap(rules.spec(part, _))
          .flatMap(rules.mp(_, refl(rank(part)))).flatMap(rules.mp(_, form)).flatMap(rules.mp(_, isBounded))
          .flatMap(rules.mp(_, isClosed)))
      /** `rank part < n`, from `n = s` and `rank part < s`. */
      def belowN(nIs: Kernel.Thm, part: Term, belowS: Kernel.Thm): Kernel.Thm =
        moved(t => lessThan(rank(part), t), force(Conv.sym(nIs)), belowS)
      /** `rank l < SUC (rank l + rank r)` and the same for `rank r`. */
      def belowSum(l: Term, r: Term, left: Boolean): Kernel.Thm = {
        val total = sum(rank(l), rank(r))
        val atMostTotal =
          if (left) apply(atMostSum, List(rank(l), rank(r)))
          else moved(t => applied(atMost, List(rank(r), t)), apply(addCommutative, List(rank(r), rank(l))),
            apply(atMostSum, List(rank(r), rank(l))))
        val part = if (left) rank(l) else rank(r)
        apply(atMostThenBelow, List(part, total, successor(total)),
          force(rules.conjIntro(atMostTotal, apply(belowSuccessor, List(total)))))
      }

      val shapes = unfold(force(rules.spec(q, languageFact(Language.FormulaCases))), qForm)
      val taken0 = Set(q, n, z, e, w)

      val reached = opened(shapes, "a", taken0) { (a, withTag) =>
        opened(withTag, "b", taken0 + a) { (b, shaped) =>
          val qIsCode = force(rules.conjElim1(shaped))
          val alternatives = force(rules.conjElim2(shaped))
          def back(atShape: Kernel.Thm, qIsShape: Kernel.Thm): Kernel.Thm =
            moved(decided, force(Conv.sym(qIsShape)), atShape)
          def forth(template: Term => Term, held: Kernel.Thm, qIsShape: Kernel.Thm): Kernel.Thm =
            moved(template, qIsShape, held)
          val (equalityCase, rest1) = disjuncts(alternatives.conclusion)
          val (negationCase, rest2) = disjuncts(rest1)
          val (implicationCase, universalCase) = disjuncts(rest2)
          def pairCase(held: Kernel.Thm)(proceed: (FVar, FVar, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
            val tagIs = force(rules.conjElim1(held))
            opened(force(rules.conjElim2(held)), "u", taken0 + a + b) { (u, withLeft) =>
              opened(withLeft, "v", taken0 + a + b + u) { (v, pieces) =>
                val qIsShape = force(Conv.trans(qIsCode, codeCongruence(tagIs, force(rules.conjElim1(pieces)))))
                proceed(u, v, qIsShape, force(rules.conjElim2(pieces)))
              }
            }
          }
          /** Free in one side, so free in a pair of two by the clause `folding`. */
          def inEither(folding: Kernel.Thm, other: Term, held: Kernel.Thm, first: Boolean): Kernel.Thm = {
            val either = if (first) force(rules.disjIntro1(other, held)) else force(rules.disjIntro2(other, held))
            fold(folding, either)
          }

          // An equation between closed terms: the atomic case, already proved both ways.
          val asEquality = pairCase(assumed(equalityCase)) { (u, v, qIsShape, terms) =>
            val shape = code(5, pair(u, v))
            val shapeClosed = forth(closed, qClosed, qIsShape)
            def sideClosed(t: Term, first: Boolean): Kernel.Thm = {
              val everywhere = nowhereFree(freeTerm, t, shapeClosed, taken0 + a + b + u + v) { (f, held) =>
                inEither(apply(languageFact(Language.FormulaFreeEquality), List(f, u, v)),
                  if (first) freeTerm(f, v) else freeTerm(f, u), held, first)
              }
              fold(force(rules.spec(t, closedCases)), everywhere)
            }
            val uIsTerm = force(rules.conjElim1(terms))
            val vIsTerm = force(rules.conjElim2(terms))
            val uClosed = sideClosed(u, first = true)
            val vClosed = sideClosed(v, first = false)
            back(decidedFrom(shape,
              holds => apply(trueEq, List(e, u, v), uIsTerm, uClosed, vIsTerm, vClosed, holds),
              fails => apply(falseEq, List(e, u, v), uIsTerm, uClosed, vIsTerm, vClosed,
                fold(apply(trueNegation, List(e, shape)), fails))), qIsShape)
          }

          // A negation: the hypothesis at the body, and the double negation for the false one.
          val asNegation = {
            val held0 = assumed(negationCase)
            val shape = neg(b)
            val qIsShape = force(Conv.trans(qIsCode, codeCongruence(force(rules.conjElim1(held0)), refl(b))))
            val bForm = force(rules.conjElim2(held0))
            val bBounded = unfold(apply(bounding.negation, List(b)), forth(bounded, qBounded, qIsShape))
            val bClosed = nowhereFree(freeForm, b, forth(closed, qClosed, qIsShape), taken0 + a + b) { (f, held) =>
              fold(apply(languageFact(Language.FormulaFreeNegation), List(f, b)), held)
            }
            val nIs = chained(force(Conv.sym(qRank)), force(Conv.apTerm(rankOf, qIsShape)),
              apply(ranking.negation, List(b))) // n = SUC (rank b)
            val atBody = atPart(b, belowN(nIs, b, apply(belowSuccessor, List(rank(b)))), bForm, bBounded, bClosed)
            val bodyTrue = force(rules.conjElim1(atBody))
            val bodyFalse = force(rules.conjElim2(atBody))
            back(decidedFrom(shape,
              holds => force(rules.mp(bodyFalse, unfold(apply(trueNegation, List(e, b)), holds))),
              fails => {
                val notNot = unfold(force(Conv.apTerm(negation, apply(trueNegation, List(e, b)))), fails)
                val bodyHolds = force(rules.spec(truthAt(b), g.doubleNegation).flatMap(rules.mp(_, notNot)))
                val introduce = apply(deductionFact(Deduction.DoubleNegationIntroduction), List(b), bForm)
                detach(b, neg(neg(b)), introduce, force(rules.mp(bodyTrue, bodyHolds)))
              }), qIsShape)
          }

          // An implication: weakening, ex falso, or its refutation, by the truth of the two sides.
          val asImplication = pairCase(assumed(implicationCase)) { (u, v, qIsShape, forms) =>
            val shape = code(7, pair(u, v))
            val uForm = force(rules.conjElim1(forms))
            val vForm = force(rules.conjElim2(forms))
            val bothBounded = unfold(apply(bounding.implication, List(u, v)), forth(bounded, qBounded, qIsShape))
            val shapeClosed = forth(closed, qClosed, qIsShape)
            def sideClosed(t: Term, first: Boolean): Kernel.Thm =
              nowhereFree(freeForm, t, shapeClosed, taken0 + a + b + u + v) { (f, held) =>
                inEither(apply(languageFact(Language.FormulaFreeImplication), List(f, u, v)),
                  if (first) freeForm(f, v) else freeForm(f, u), held, first)
              }
            val nIs = chained(force(Conv.sym(qRank)), force(Conv.apTerm(rankOf, qIsShape)),
              apply(ranking.implication, List(u, v))) // n = SUC (rank u + rank v)
            val atU = atPart(u, belowN(nIs, u, belowSum(u, v, left = true)), uForm,
              force(rules.conjElim1(bothBounded)), sideClosed(u, first = true))
            val atV = atPart(v, belowN(nIs, v, belowSum(u, v, left = false)), vForm,
              force(rules.conjElim2(bothBounded)), sideClosed(v, first = false))
            val clause = apply(g.trueImplication, List(e, u, v))
            val tu = truthAt(u)
            val tv = truthAt(v)
            back(decidedFrom(shape,
              holds => {
                val arrow = unfold(clause, holds)
                cases(tv)(
                  vHolds => apply(deductionFact(Deduction.Weaken), List(u, v), uForm, vForm,
                    force(rules.mp(force(rules.conjElim1(atV)), vHolds))),
                  vFails => cases(tu)(
                    uHolds => absurd(provable(shape), force(rules.notElim(vFails, force(rules.mp(arrow, uHolds))))),
                    uFails => apply(deductionFact(Deduction.ImplicationOfDenial), List(u, v), uForm, vForm,
                      force(rules.mp(force(rules.conjElim2(atU)), uFails)))))
              },
              fails => {
                val notArrow = unfold(force(Conv.apTerm(negation, clause)), fails)
                val uHolds = cases(tu)(
                  yes => yes,
                  no => absurd(tu, force(rules.notElim(notArrow,
                    force(rules.disch(tu, absurd(tv, force(rules.notElim(no, assumed(tu))))))))))
                val vFails = cases(tv)(
                  yes => absurd(denial(tv), force(rules.notElim(notArrow, force(rules.disch(tu, yes))))),
                  no => no)
                apply(deductionFact(Deduction.DeniedImplication), List(u, v), uForm, vForm,
                  force(rules.mp(force(rules.conjElim1(atU)), uHolds)),
                  force(rules.mp(force(rules.conjElim2(atV)), vFails)))
              }), qIsShape)
          }

          // A universal: in the class only below a variable or a numeral, and closed only below a
          // numeral; then its truth is its instances', each closed and of a smaller rank.
          val asUniversal = pairCase(assumed(universalCase)) { (u, v, qIsShape, vIsForm) =>
            val shapeBounded = forth(bounded, qBounded, qIsShape)
            val inverted = apply(bounding.universal, List(u, v), shapeBounded)
            val avoid = taken0 + a + b + u + v
            opened(inverted, "wit", avoid) { (wit, atW) =>
              opened(atW, "c", avoid + wit) { (c, atC) =>
                opened(atC, "r", avoid + wit + c) { (r, isAllBelow) =>
                  val unfolding = apply(languageFact(Language.AllBelowCases), List(wit, u, c, r))
                  val whole = sides(unfolding)._2
                  val implication = arguments(arguments(whole)._2)._2
                  val less = arguments(arguments(implication)._2)._1
                  val shapes8 = chained(isAllBelow, unfolding)
                  val payloads = force(rules.conjElim2(
                    apply(codeInjective, List(tags(8), pair(u, v), tags(8), pair(u, implication)), shapes8)))
                  val vIs = force(rules.conjElim2(apply(pairInjective, List(u, v, u, implication), payloads)))
                  val rIsForm = force(rules.conjElim2(apply(parts, List(less, r), moved(isFormula, vIs, vIsForm))))

                  val allBelow = sides(isAllBelow)._2
                  val qIsAllBelow = chained(qIsShape, isAllBelow)
                  val clause = unfold(apply(bounding.allBelow, List(wit, u, c, r)), moved(bounded, isAllBelow, shapeBounded))
                  val apart = force(rules.conjElim1(clause)) // ~(wit = u)
                  val boundHeld = force(rules.conjElim1(force(rules.conjElim2(clause))))
                  val rBounded = force(rules.conjElim2(force(rules.conjElim2(clause))))
                  val allBelowClosed = forth(closed, qClosed, qIsAllBelow)
                  def freeClause(f: Term): Kernel.Thm = apply(languageFact(Language.AllBelowFree), List(f, wit, u, c, r))

                  // n = SUC (SUC (rank less + rank r)), and rank r is below it
                  val nIs = chained(force(Conv.sym(qRank)), force(Conv.apTerm(rankOf, chained(qIsAllBelow, unfolding))),
                    apply(ranking.universal, List(u, implication)),
                    force(Conv.apTerm(successorConstant, apply(ranking.implication, List(less, r)))))
                  val inner = belowSum(less, r, left = false)
                  val total = successor(sum(rank(less), rank(r)))
                  val rBelow = belowN(nIs, r, apply(strictTransitive, List(rank(r), total, successor(total)),
                    force(rules.conjIntro(inner, apply(belowSuccessor, List(total))))))

                  // A variable bound is free in the universal, which is closed: so the bound is a numeral.
                  val (variableHad, numeralHad) = disjuncts(boundHeld.conclusion)
                  val notVariable = opened(assumed(variableHad), "j", avoid + wit + c + r) { (j, held) =>
                    val cIs = force(rules.conjElim1(held)) // c = v_j
                    val uNotJ = turned(force(rules.conjElim1(force(rules.conjElim2(held)))))
                    val witNotJ = turned(force(rules.conjElim2(force(rules.conjElim2(held)))))
                    val atVariable = fold(apply(languageFact(Language.FreeVariable), List(j, j)), refl(j))
                    val boundFree = moved(t => freeTerm(j, t), force(Conv.sym(cIs)), atVariable)
                    val reading = sides(freeClause(j))._2
                    val (_, never, inside) = branches(reading)
                    val (firstHalf, secondHalf) = disjuncts(inside)
                    val (_, neverHere, termHere) = branches(firstHalf)
                    val firstHolds = fold(passedAt(witNotJ, neverHere, termHere), boundFree)
                    val atWhole = fold(chained(freeClause(j), passedAt(uNotJ, never, inside)),
                      force(rules.disjIntro1(secondHalf, firstHolds)))
                    force(rules.spec(j, allBelowClosed).flatMap(rules.notElim(_, atWhole)))
                  }
                  val asNumeral = force(rules.disjElim(boundHeld,
                    absurd(numeralHad, notVariable), assumed(numeralHad))) // ?count. c = NUM_NUMERAL count

                  opened(asNumeral, "count", avoid + wit + c + r) { (count, cIsNumeral) =>
                    val boundIs = force(Conv.apTerm(headOf(headOf(allBelow)), cIsNumeral).flatMap(Conv.apThm(_, r)))
                    val target = sides(boundIs)._2 // NUM_ALL_BELOW wit u (numeral count) r
                    val reading = apply(allBelowTruth, List(e, wit, u, count, r), apart)
                    val taken1 = avoid + wit + c + r + count
                    def instanceOf(m: Term): Term = applied(formulaSubstituting, List(u, numeral(m), r))
                    /** `NUM_TRUE (instance m) e = NUM_TRUE r e[u := m]`. */
                    def truthOfInstance(m: Term): Kernel.Thm =
                      force(rules.specAll(truthAtNumeral, List(u, m, r)).flatMap(rules.mp(_, rIsForm))
                        .flatMap(rules.spec(e, _)))
                    def instanceDecided(m: FVar): Kernel.Thm = {
                      val form = apply(languageFact(Language.FormulaSubstituteKeepsFormulas), List(u, numeral(m), r),
                        rIsForm, numeralTerm(m))
                      val isBounded = apply(boundedAt, List(u, m, r), rIsForm, rBounded)
                      val rankIs = apply(rankAt, List(u, m, r), rIsForm) // rank (instance m) = rank r
                      val rankBelow = moved(t => lessThan(t, n), force(Conv.sym(rankIs)), rBelow)
                      val isClosed = nowhereFree(freeForm, instanceOf(m), allBelowClosed, taken1 + m) {
                        (f, held) =>
                          val survived = force(rules.specAll(freeFormAt, List(u, m, r)).flatMap(rules.mp(_, rIsForm))
                            .flatMap(rules.spec(f, _)).flatMap(rules.mp(_, held))) // free f r /\ ~(f = u)
                          val uNotF = turned(force(rules.conjElim2(survived)))
                          val reading = sides(freeClause(f))._2
                          val (_, never, inside) = branches(reading)
                          val (firstHalf, _) = disjuncts(inside)
                          fold(chained(freeClause(f), passedAt(uNotF, never, inside)),
                            force(rules.disjIntro2(firstHalf, force(rules.conjElim1(survived)))))
                      }
                      atPart(instanceOf(m), rankBelow, form, isBounded, isClosed)
                    }

                    val atTarget = decidedFrom(target,
                      holds => {
                        val every = unfold(reading, holds)
                        val k = Conv.freshVariable("k", numbers, taken1)
                        val kBelow = lessThan(k, count)
                        val bodyTrue = force(rules.spec(k, every).flatMap(rules.mp(_, assumed(kBelow))))
                        val instanceTrue = fold(truthOfInstance(k), bodyTrue)
                        val proved = force(rules.mp(force(rules.conjElim1(instanceDecided(k))), instanceTrue))
                        val instances = force(rules.disch(kBelow, proved).flatMap(rules.gen(k, _)))
                        apply(deductionFact(Deduction.AllBelowNumeral), List(wit, u, count, r), apart, rIsForm, instances)
                      },
                      fails => {
                        val notEvery = unfold(force(Conv.apTerm(negation, reading)), fails)
                        val universalPredicate = sides(reading)._2 match {
                          case App(_, predicateTerm) => predicateTerm
                          case other => throw new RefusedHere(NotOfForm("a universal", other))
                        }
                        val some = force(rules.spec(universalPredicate, notForall).flatMap(theorem =>
                          Conv.betaNormalise(theorem.conclusion).flatMap(reduced =>
                            LogicError.lift(Kernel.eqMp(reduced, theorem)))).flatMap(rules.mp(_, notEvery)))
                        opened(some, "k", taken1) { (k, notBody) =>
                          val kBelow = lessThan(k, count)
                          val bodyTruth = applied(truth, List(r, updated(e, u, k)))
                          val kBelowHolds = cases(kBelow)(
                            yes => yes,
                            no => absurd(kBelow, force(rules.notElim(notBody,
                              force(rules.disch(kBelow, absurd(bodyTruth, force(rules.notElim(no, assumed(kBelow))))))))))
                          val bodyFails = cases(bodyTruth)(
                            yes => absurd(denial(bodyTruth), force(rules.notElim(notBody, force(rules.disch(kBelow, yes))))),
                            no => no)
                          val instanceFails = fold(force(Conv.apTerm(negation, truthOfInstance(k))), bodyFails)
                          val refuted = force(rules.mp(force(rules.conjElim2(instanceDecided(k))), instanceFails))
                          apply(deductionFact(Deduction.NotAllBelowNumeral), List(wit, u, count, k, r),
                            apart, rIsForm, kBelowHolds, refuted)
                        }
                      })
                    moved(decided, force(Conv.sym(chained(qIsAllBelow, boundIs))), atTarget)
                  }
                }
              }
            }
          }

          val lastTwo = force(rules.disjElim(assumed(rest2), asImplication, asUniversal))
          val lastThree = force(rules.disjElim(assumed(rest1), asNegation, lastTwo))
          force(rules.disjElim(alternatives, asEquality, lastThree))
        }
      }

      val step = force(rules.disch(closed(q), reached).flatMap(rules.disch(bounded(q), _))
        .flatMap(rules.disch(isFormula(q), _)).flatMap(rules.disch(equal(rank(q), n), _)).flatMap(rules.gen(q, _))
        .flatMap(rules.disch(hypothesis, _)).flatMap(rules.gen(n, _)))
      val everywhere = force(rules.mp(instance, step))
      val p = Term.variable("p", numbers)
      force(rules.spec(rank(p), everywhere).flatMap(rules.spec(p, _)).flatMap(rules.mp(_, refl(rank(p))))
        .flatMap(rules.genAll(_, List(e, p))))
    }
  }
}
