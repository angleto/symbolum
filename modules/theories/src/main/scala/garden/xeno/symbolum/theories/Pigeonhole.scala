package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A lower bound on resolution refutations of the pigeonhole principle, proved: every refutation
 * of `n + 1` pigeons in `n` holes derives a clause at least `n - 1` literals long.
 *
 * {{{
 *   !n k v s inputs m.
 *     NUM_LT ZERO n ==>
 *     (!j. NUM_LT j inputs ==> <clause j is a clause of the pigeonhole principle>) ==>
 *     RES_REFUTATION k v s inputs m ==>
 *     ?j. NUM_LE inputs j /\ NUM_LT j m /\ NUM_LE n (SUC (k j))
 * }}}
 *
 * `Resolving` names a refutation and its width and states Haken's theorem without proving it.
 * This is the first theorem over those names that says a refutation has to be **large** in some
 * measure, which is what the programme of Cook and Reckhow is made of, and it is a bound on width
 * and not on size. It is not Haken's theorem and it is not a step towards P != NP: the published
 * barriers say why no single technique of this kind can be, and the file claims nothing past the
 * statement above.
 *
 * == Why the clause has to be a derived one ==
 *
 * `Resolving.RES_WIDTH` is the largest clause below `m`, **the inputs included**, and the clause of
 * a pigeon already has `n` literals. So the sentence the card asking for this wrote, "a refutation
 * has width at least n/c", is true of any refutation that uses a pigeon clause at all, for a
 * reason that has nothing to do with resolution. What carries content is a clause the refutation
 * had to **derive**, which is `NUM_LE inputs j`, since a step below `inputs` is an input. The
 * measured difference is the whole reason for the conclusion's shape: without that conjunct the
 * theorem would be one step from `RES_WIDTH_BOUND`.
 *
 * == What it is worth, which is little ==
 *
 * **Moving the bound to a derived clause moves the objection one step and does not remove it.** A
 * resolvent with a pigeon clause as a parent keeps every literal of it but the pivot, so it already
 * has `n - 1`. And some derived step has a pigeon parent: otherwise every derived step descends from
 * hole clauses alone, which the all-false assignment satisfies, and `RES_STEP_SOUND` would carry
 * that assignment to the empty clause. So the conclusion follows from one step and the definition
 * of a justified step, for the reason the section above gives about `RES_WIDTH`: the inputs are as
 * wide as the bound. It is a theorem about this encoding and not about proof complexity. The
 * verification of Mycelium card `01520749` found this on 2026-09-25, and `docs/adr/0054` corrects the
 * sentence of `docs/adr/0048` that called the constant better than asked.
 *
 * A width bound says something only where the inputs are short, and that is
 * `ExpanderPigeonhole.RES_GPHP_WIDTH`: the principle over a bipartite graph of small degree, whose
 * bound comes from the graph's expansion rather than from the inputs.
 *
 * == The argument, which is the critical-assignment one ==
 *
 * A **critical assignment** for pigeon `p` puts every other pigeon in its own hole and leaves `p`
 * out; with `n + 1` pigeons and `n` holes that is a bijection, so it satisfies every hole clause and
 * every pigeon clause but `p`'s. It is given here by a function `f` from pigeons to holes, injective
 * and below `n` away from `p`, and the assignment is `\x. ?q. q <= n /\ ~(q = p) /\ x = q * n + f q`.
 * A pigeon is **bad** for a clause when some critical assignment for it falsifies the clause.
 *
 *   1. An input has at most one bad pigeon: the pigeon clause of `c` has only `c`, a hole clause
 *      has none, because a critical assignment never puts two pigeons in one hole.
 *   2. The empty clause has every pigeon bad, and a critical assignment exists for each.
 *   3. A resolvent's bad pigeons are among its parents', by `RES_STEP_SOUND` read at a critical
 *      assignment: whatever satisfies both parents satisfies the resolvent.
 *   4. So the **first** step with two bad pigeons is derived, and has exactly two, `p1` and `p2`.
 *   5. Take the critical assignment for `p1` that falsifies it, and any other pigeon `q`. Moving
 *      `q`'s hole to `p1` gives a critical assignment for `q`, which satisfies the clause because
 *      `q` is not bad; the two assignments differ on two variables, so the clause holds a literal on
 *      one of them. Those literals are distinct for distinct `q`, and there are `n - 1` such `q`.
 *
 * Step 5's counting is the pigeonhole principle on `num` itself, [[Pigeonhole.Injection]], which this
 * repository did not have and which is why it is published here.
 *
 * == What it found about this repository ==
 *
 * The card this answers asked that a limit met on the way be written down where it was met. Four:
 *
 *   - **There is no finite set and no cardinality.** "At most one bad pigeon" and "exactly two" are
 *     written as uniqueness and as two distinct witnesses, and the count in step 5 is an injection
 *     into an interval. It works because the argument never needs a size larger than two by name.
 *   - **The pigeonhole principle on `num` was missing**, and so was `SUC a <= SUC b` from
 *     `a <= b`, which is three facts about addition here. [[Pigeonhole.Injection]] is the first;
 *     it belongs in `Peano` and is here because moving a link's library is a piece of its own.
 *   - **A propositional step cannot read an equation between two booleans.** `Propositional` and
 *     `Intuitionistic` both treat `A = s` as an atom, so the step "the two assignments disagree at
 *     this variable" is four cases by hand in `Builder.literalForced`.
 *   - **`RES_WIDTH` counts the inputs**, which is the section above.
 *
 * == It is outside the chain ==
 *
 * `Conjugacy`'s standing: a function of the chain that proves facts about one investigation's object,
 * the pigeonhole principle as a family of clauses, which does not belong in the vocabulary `Ask` and
 * `Find` are typed in. It declares nothing, so it spends no axiom of its own; what it rests on is the
 * chain's. `PigeonholeSpec` is what builds it.
 *
 * Every step is written in direct style inside `Builder`, for the reason `Provability` gives: the
 * proof is a case analysis with independent branches, and a `for` comprehension over `Either` would
 * turn "which obligation failed" into "which binding came first".
 */
final class Pigeonhole private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Pigeonhole {

  /**
   * The pigeonhole principle on `num`: an injection from the first `a` numbers into the first `b`
   * gives `a <= b`.
   *
   * By induction on `a` with `b` and the function universally quantified inside, since the step
   * shrinks both: at `SUC a` into `SUC c` the function is folded to one on `a` into `c` by sending
   * whatever landed on `c` to where `a` went.
   */
  val Injection: String = "NUM_INJECTION_LE"

  /** The theorem this development exists for. See the class comment for the statement. */
  val DerivedWidth: String = "RES_PHP_DERIVED_WIDTH"

  /** Variable `p * n + h`, the pigeon `p` in the hole `h`, which is injective for `h < n`. */
  private def hole(pigeon: String, at: String): String = s"NUM_ADD (NUM_MUL $pigeon n) $at"

  /**
   * Clause `j` is a clause of the pigeonhole principle for `n + 1` pigeons and `n` holes, as a set
   * of literals: the pigeon clause of some `p <= n`, every literal `p` in some hole and every hole
   * present; or the hole clause of some `p < q <= n` at a hole `h`, both negative literals present
   * and nothing else.
   *
   * The same text as the hypothesis of Haken's statement in `ResolvingSpec`, which asserts that one
   * elaborates, so the lower bound here is about the family that statement is about.
   */
  val Clause: String =
    "(?p:num. NUM_LE p n /\\ " +
      s"(!i:num. NUM_LT i (k j) ==> ?h:num. NUM_LT h n /\\ v j i = ${hole("p", "h")} /\\ s j i = T) /\\ " +
      s"(!h:num. NUM_LT h n ==> ?i:num. NUM_LT i (k j) /\\ v j i = ${hole("p", "h")} /\\ s j i = T)) \\/ " +
      "(?p:num. ?q:num. ?h:num. NUM_LT p q /\\ NUM_LE q n /\\ NUM_LT h n /\\ " +
      s"(!i:num. NUM_LT i (k j) ==> (v j i = ${hole("p", "h")} \\/ v j i = ${hole("q", "h")}) /\\ s j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k j) /\\ v j i = ${hole("p", "h")} /\\ s j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k j) /\\ v j i = ${hole("q", "h")} /\\ s j i = F))"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    Injection ->
      ("!a:num. !b:num. !g:num->num. (!x:num. NUM_LT x a ==> NUM_LT (g x) b) ==> " +
        "(!x:num. !y:num. NUM_LT x a ==> NUM_LT y a ==> g x = g y ==> x = y) ==> NUM_LE a b"),
    DerivedWidth ->
      ("!n:num. !k:num->num. !v:num->num->num. !s:num->num->bool. !inputs:num. !m:num. " +
        "NUM_LT ZERO n ==> " +
        s"(!j:num. NUM_LT j inputs ==> $Clause) ==> " +
        "RES_REFUTATION k v s inputs m ==> " +
        "(?j:num. NUM_LE inputs j /\\ NUM_LT j m /\\ NUM_LE n (SUC (k j)))")
  )

  /** The development over the chain it is handed. It extends nothing. */
  def construct(chain: Chain): Either[LogicError, Pigeonhole] = {
    val signature = chain.widest
    try {
      val builder = new Builder(chain)
      val facts = Map(
        Injection -> builder.checked(Injection, builder.injection),
        DerivedWidth -> builder.checked(DerivedWidth, builder.derivedWidth)
      )
      Right(new Pigeonhole(signature.theory, signature.notation, chain.logic, facts))
    } catch { case refused: RefusedHere => Left(refused.error) }
  }

  /** The development over the standard chain. */
  lazy val standard: Pigeonhole =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /** Carry a refusal out of a derivation written in direct style. */
  private[theories] final class RefusedHere(val error: LogicError) extends RuntimeException(error.message)

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Fun: Type = Type.fun(Num, Num)

  /**
   * The free variables the derivation's texts use, with their types.
   *
   * A text that elaborates a name at another type, or a name not in this table, is refused rather
   * than carried on: a variable the parser typed differently from the one a theorem holds is a
   * different variable, and the mismatch would surface forty lines later as a refused `mp`.
   */
  private[theories] val Types: Map[String, Type] = {
    val numbers = List(
      "n", "inputs", "m", "j", "p", "q", "r", "c", "d", "h", "u", "x", "y", "t", "a", "b", "e", "o",
      "i", "pa", "pb", "p1", "p2", "w"
    )
    numbers.map(_ -> Num).toMap ++ Map(
      "k" -> Fun,
      "f" -> Fun,
      "g" -> Fun,
      "hh" -> Fun,
      "v" -> Type.fun(Num, Fun),
      "s" -> Type.fun(Num, Type.fun(Num, Type.Bool)),
      "P" -> Type.fun(Num, Type.Bool),
      "Q" -> Type.fun(Num, Type.fun(Num, Type.Bool))
    )
  }

  /* ------------------------------------------------------------------------- the texts */

  /** A function from pigeons to holes, as the text of its application to an argument. */
  private type Fn = String => String

  private[theories] val Written: Map[Type, String] = Map(
    Num -> "num",
    Fun -> "num->num",
    Type.fun(Num, Fun) -> "num->num->num",
    Type.fun(Num, Type.fun(Num, Type.Bool)) -> "num->num->bool",
    Type.fun(Num, Type.Bool) -> "num->bool"
  )

  private val Identifier = "(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])".r

  /**
   * Every occurrence of a name in `Types` written with its type, except where it is being bound.
   *
   * The texts here are short and many of their variables occur where nothing fixes a type, `g x =
   * g y` being the plain case, and a name elaborated at an open type is refused. Annotating each by
   * hand was the first version, and it failed at the first run in eleven places.
   */
  private def annotated(text: String): String = annotatedWith(Types, Written)(text)

  /**
   * [[annotated]] over a table of the caller's, which is what lets a development with variables of
   * its own reuse [[Builder]] rather than copy it.
   */
  private[theories] def annotatedWith(types: Map[String, Type], written: Map[Type, String])(text: String): String =
    Identifier.replaceAllIn(text, found => {
      val name = found.group(1)
      val rest = text.substring(found.end).dropWhile(_ == ' ')
      types.get(name).flatMap(written.get) match {
        case Some(written) if !rest.startsWith(":") =>
          scala.util.matching.Regex.quoteReplacement(s"($name:$written)")
        case _ => scala.util.matching.Regex.quoteReplacement(name)
      }
    })

  private def call(f: String): Fn = x => s"($f $x)"

  /** The variable of pigeon `q` in hole `h`. */
  private def enc(q: String, h: String): String = s"(${hole(q, h)})"

  /** The critical assignment for `p` given by `f`, read at `x`. */
  private def asg(p: String, f: Fn)(x: String): String =
    s"(?w0:num. NUM_LE w0 n /\\ ~(w0 = $p) /\\ $x = ${enc("w0", f("w0"))})"

  /** Clause `j` satisfied by the assignment `a`, written the way `RES_SAT` opens. */
  private def sat(a: String => String, j: String): String =
    s"(?i0:num. NUM_LT i0 (k $j) /\\ (${a(s"(v $j i0)")} = s $j i0))"

  /** `f` is a critical matching for `p`: below `n` and injective on the pigeons other than `p`. */
  private def matching(p: String, f: Fn): String =
    s"((!w1:num. NUM_LE w1 n /\\ ~(w1 = $p) ==> NUM_LT ${f("w1")} n) /\\ " +
      s"(!w1:num. !w2:num. NUM_LE w1 n /\\ ~(w1 = $p) /\\ NUM_LE w2 n /\\ ~(w2 = $p) /\\ " +
      s"${f("w1")} = ${f("w2")} ==> w1 = w2))"

  /** The half of `bad` after the pigeon's bound: some critical assignment falsifies clause `j`. */
  private def falsified(j: String, p: String): String =
    s"(?g0:num->num. ${matching(p, call("g0"))} /\\ ~${sat(asg(p, call("g0")), j)})"

  /** Pigeon `p` is bad for clause `j`. */
  private def bad(j: String, p: String): String = s"(NUM_LE $p n /\\ ${falsified(j, p)})"

  /** Clause `j` has two different bad pigeons, and is below `m`. */
  private def two(j: String): String =
    s"(NUM_LT $j m /\\ (?p1:num. ?p2:num. ~(p1 = p2) /\\ ${bad(j, "p1")} /\\ ${bad(j, "p2")}))"

  /** The pigeon clause of `c`, as the first disjunct of [[Pigeonhole.Clause]] opens at `c`. */
  private def pigeonClause(j: String, c: String): String =
    s"(NUM_LE $c n /\\ " +
      s"(!i:num. NUM_LT i (k $j) ==> ?h:num. NUM_LT h n /\\ v $j i = ${hole(c, "h")} /\\ s $j i = T) /\\ " +
      s"(!h:num. NUM_LT h n ==> ?i:num. NUM_LT i (k $j) /\\ v $j i = ${hole(c, "h")} /\\ s $j i = T))"

  /** The hole clause of `c < d` at `h`, as the second disjunct of [[Pigeonhole.Clause]] opens. */
  private def holeClause(j: String, c: String, d: String, h: String): String =
    s"(NUM_LT $c $d /\\ NUM_LE $d n /\\ NUM_LT $h n /\\ " +
      s"(!i:num. NUM_LT i (k $j) ==> (v $j i = ${hole(c, h)} \\/ v $j i = ${hole(d, h)}) /\\ s $j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k $j) /\\ v $j i = ${hole(c, h)} /\\ s $j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k $j) /\\ v $j i = ${hole(d, h)} /\\ s $j i = F))"

  /** How a resolvent's literals carry a parent's, as `RES_JUSTIFIED` opens. */
  private def carries(parent: String, j: String, polarity: String): String =
    s"(!i:num. NUM_LT i (k $parent) ==> ~(v $parent i = x /\\ s $parent i = $polarity) ==> " +
      s"(?w3:num. NUM_LT w3 (k $j) /\\ v $j w3 = v $parent i /\\ s $j w3 = s $parent i))"

  /** The literal `q` forces into a clause falsified by `p`'s assignment, read at a variable `o`. */
  private def forcedAt(o: String, q: String, p: String = "p"): String =
    s"($o = ${enc(q, s"(f $q)")} \\/ $o = ${enc(p, s"(f $q)")})"

  /** The critical matching for `p` that keeps order below `p` and moves everything above down one. */
  private def shifted(x: String): String = s"(COND (NUM_LT $x p) $x (PRE $x))"

  /** The matching for `q` got from `f` by moving `q`'s hole to `p`. */
  private def swapped(x: String): String = s"(COND ($x = p) (f q) (f $x))"

  /* --------------------------------------------------------------------- the builder */

  /**
   * The derivation, and the moves it is written in. Package-visible so that `PigeonholeSpec`
   * derives its non-vacuity witness with the same moves rather than a second copy of them.
   */
  private[theories] final class Builder(
    chain: Chain,
    types: Map[String, Type] = Types,
    written: Map[Type, String] = Written
  ) {
    private def annotated(text: String): String = annotatedWith(types, written)(text)

    val signature = chain.widest
    val theory = signature.theory
    val notation = signature.notation
    val logic = chain.logic
    val rules = logic.rules
    val classical = chain.classical
    val peano = chain.peano
    val propositional = Propositional.over(classical, logic)
    val intuitionistic = Intuitionistic(logic)

    /* --------------------------------------------------------------- the moves */

    def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    def refuse(what: String, term: Term): Nothing = throw new RefusedHere(NotOfForm(what, term))

    def typed(term: Term, holes: Set[String]): Term = {
      Term.freeVariables(term).foreach { variable =>
        if (!holes.contains(variable.name) && !types.get(variable.name).contains(variable.ty))
          refuse(s"the variable ${variable.name} at the type the derivation declares for it", variable)
      }
      term
    }

    def prop(text: String): Term = typed(force(Parser.proposition(theory, notation, annotated(text))), Set.empty)
    def term(text: String, ty: Type): Term = typed(force(Parser.term(theory, notation, annotated(text), ty)), Set.empty)
    def variable(name: String): FVar =
      Term.variable(name, types.getOrElse(name, refuse("a declared variable", Term.variable(name, Type.Bool))))

    def assumeT(statement: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(statement)))
    def assume(text: String): Kernel.Thm = assumeT(prop(text))

    def pf(name: String): Kernel.Thm = force(peano.fact(name))
    def nf(name: String): Kernel.Thm = force(chain.naturals.fact(name))
    def cf(name: String): Kernel.Thm = force(classical.fact(name))
    def rf(name: String): Kernel.Thm = force(chain.resolving.fact(name))

    def freeIn(theorem: Kernel.Thm): Set[FVar] =
      theorem.hypotheses.flatMap(Term.freeVariables).toSet ++ Term.freeVariables(theorem.conclusion)

    def reduced(theorem: Kernel.Thm): Kernel.Thm =
      force(Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

    /** Specialise the leading quantifiers at texts, each read at its binder's type, and reduce. */
    def spec(theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
      reduced(arguments.foldLeft(theorem) { (current, text) =>
        val predicate = logic.destForallPredicate(current.conclusion).getOrElse(refuse("a universal", current.conclusion))
        val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
        force(rules.spec(term(text, domain), current))
      })

    /** Replace free variables by texts, each read at the variable's type, and reduce. */
    def inst(theorem: Kernel.Thm, pairs: (String, String)*): Kernel.Thm = {
      val free = freeIn(theorem)
      val substitution: Map[FVar, Term] = pairs.map { case (name, text) =>
        val target = free.find(_.name == name).getOrElse(refuse(s"a theorem with $name free in it", theorem.conclusion))
        target -> term(text, target.ty)
      }.toMap
      reduced(force(LogicError.lift(Kernel.inst(substitution, theorem))))
    }

    def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
      premises.foldLeft(implication)((current, premise) => force(rules.mp(current, premise)))

    def conj(left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm = force(rules.conjIntro(left, right))
    def left(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim1(theorem))
    def right(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim2(theorem))

    /** `t1 ==> ... ==> tn ==> <conclusion>`, discharging the texts in the order written. */
    def discharged(theorem: Kernel.Thm, texts: String*): Kernel.Thm =
      texts.reverse.foldLeft(theorem)((current, text) => force(rules.disch(prop(text), current)))

    def generalised(theorem: Kernel.Thm, names: String*): Kernel.Thm =
      force(rules.genAll(theorem, names.toList.map(variable)))

    def sym(equation: Kernel.Thm): Kernel.Thm = force(Conv.sym(equation))
    def trans(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = force(Conv.trans(first, second))
    def congruent(fn: String, equation: Kernel.Thm): Kernel.Thm = {
      val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
      force(Conv.apTerm(term(fn, Type.fun(Term.typeOf(lhs), Num)), equation))
    }

    /**
     * `|- T[b]` from `|- a = b` and `|- T[a]`, where `T` is `template` with its hole written `zz`.
     *
     * Through the abstraction `\zz. T` and two root contractions, so nothing else in `T` moves.
     */
    def transport(equation: Kernel.Thm, template: String, theorem: Kernel.Thm): Kernel.Thm = {
      val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
      val zz = Term.variable("zz", Term.typeOf(lhs))
      // Every hole in this file is a number; a hole of another type is refused rather than guessed.
      if (Term.typeOf(lhs) != Num) refuse("an equation between numbers", equation.conclusion)
      val body = typed(force(Parser.proposition(theory, notation, annotated(template).replace("zz", "(zz:num)"))), Set("zz"))
      val lambda = force(LogicError.lift(Term.abs(zz, body)))
      val across = force(Conv.apTerm(lambda, equation))
      val (from, to) = Term.destEq(across.conclusion).getOrElse(refuse("an equation", across.conclusion))
      val opened = force(Conv.betaRoot(from))
      val closed = force(Conv.betaRoot(to))
      val joined = trans(trans(sym(opened), across), closed)
      val (start, _) = Term.destEq(joined.conclusion).getOrElse(refuse("an equation", joined.conclusion))
      if (start != theorem.conclusion) refuse("a proof of the template at the left side", theorem.conclusion)
      force(LogicError.lift(Kernel.eqMp(joined, theorem)))
    }

    /** Every free occurrence of the variable `x` replaced by `t`, from `|- x = t`. */
    def substituted(equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm = {
      val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
      val x = lhs match {
        case variable: FVar => variable
        case other => refuse("an equation whose left side is a variable", other)
      }
      val zz = Term.variable("zz", x.ty)
      val body = force(LogicError.lift(Term.substitute(Map(x -> zz), theorem.conclusion)))
      val lambda = force(LogicError.lift(Term.abs(zz, body)))
      val across = force(Conv.apTerm(lambda, equation))
      val (from, to) = Term.destEq(across.conclusion).getOrElse(refuse("an equation", across.conclusion))
      val joined = trans(trans(sym(force(Conv.betaRoot(from))), across), force(Conv.betaRoot(to)))
      force(LogicError.lift(Kernel.eqMp(joined, theorem)))
    }

    def absurd(negation: Kernel.Thm, positive: Kernel.Thm): Kernel.Thm = force(rules.notElim(negation, positive))
    def exFalso(statement: Term, falsity: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(statement, falsity))

    /** `|- ~(b = a)` from `|- ~(a = b)`. */
    def unequalSym(theorem: Kernel.Thm): Kernel.Thm = {
      val equation = logic.destNot(theorem.conclusion).getOrElse(refuse("a negation", theorem.conclusion))
      val (a, b) = Term.destEq(equation).getOrElse(refuse("an equation", equation))
      val flipped = force(LogicError.lift(Term.eq(b, a)))
      force(rules.notIntro(flipped, absurd(theorem, sym(assumeT(flipped)))))
    }

    /** `|- A = F` from `|- ~A`. */
    def falseEquation(theorem: Kernel.Thm): Kernel.Thm = {
      val statement = logic.destNot(theorem.conclusion).getOrElse(refuse("a negation", theorem.conclusion))
      val fromFalsity = exFalso(statement, assumeT(logic.falsity))
      val toFalsity = absurd(theorem, assumeT(statement))
      Kernel.deductAntisym(fromFalsity, toFalsity)
    }

    def truthEquation(theorem: Kernel.Thm): Kernel.Thm = force(rules.eqTruthIntro(theorem))

    /** A propositional consequence of the premises, the subterms read as atoms. */
    def taut(goal: Term, premises: Kernel.Thm*): Kernel.Thm = {
      val implication = premises.foldRight(goal)((premise, acc) => force(logic.mkImp(premise.conclusion, acc)))
      val proved = intuitionistic.prove(implication).orElse(propositional.prove(implication))
      mp(force(proved), premises*)
    }

    /** By the excluded middle on `statement`: each branch receives its assumption. */
    def cases(statement: Term)(positive: Kernel.Thm => Kernel.Thm, negative: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val denial = force(logic.mkNot(statement))
      force(classical.cases(statement, positive(assumeT(statement)), negative(assumeT(denial))))
    }

    /** `|- statement`, from falsity under its denial. */
    def byContradiction(statement: Term)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val denial = force(logic.mkNot(statement))
      force(classical.contradiction(statement, reach(assumeT(denial))))
    }

    /** `|- ~statement`, from falsity under the statement. */
    def refuted(statement: Term)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm =
      force(rules.notIntro(statement, reach(assumeT(statement))))

    def byDisjunction(disjunction: Kernel.Thm)(first: Kernel.Thm => Kernel.Thm, second: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val (a, b) = logic.destDisj(disjunction.conclusion).getOrElse(refuse("a disjunction", disjunction.conclusion))
      force(rules.disjElim(disjunction, first(assumeT(a)), second(assumeT(b))))
    }

    def disjoined(target: Term, proof: Kernel.Thm): Kernel.Thm = {
      val (a, b) = logic.destDisj(target).getOrElse(refuse("a disjunction", target))
      if (proof.conclusion == a) force(rules.disjIntro1(b, proof))
      else if (proof.conclusion == b) force(rules.disjIntro2(a, proof))
      else refuse("a proof of one of the two disjuncts", proof.conclusion)
    }

    /** Eliminates an existential into `reach`'s theorem, the witness being the variable `name`. */
    def opened(existential: Kernel.Thm, name: String)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion).getOrElse(refuse("an existential", existential.conclusion))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
      val witness = Term.variable(name, domain)
      if (freeIn(existential).contains(witness)) refuse(s"an existential in which $name is not already free", existential.conclusion)
      val applied = force(LogicError.lift(Term.app(predicate, witness)))
      val body = Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(refuse("an equation", applied))
      force(rules.existsElim(existential, witness, reach(assumeT(body))))
    }

    /** `|- ?x1 ... xn. body` from a proof of the body at the witnesses, each read at its type. */
    def witnessed(target: Term, witnesses: List[String], proof: Kernel.Thm): Kernel.Thm =
      witnessedBy(target, witnesses.map(text => (domain: Type) => term(text, domain)), proof)

    /** The same, with each witness built from the type its binder has. */
    def witnessedBy(target: Term, witnesses: List[Type => Term], proof: Kernel.Thm): Kernel.Thm =
      witnesses match {
        case Nil =>
          if (target == proof.conclusion) proof
          else {
            val normal = force(Conv.betaNormalise(target))
            val (_, reducedTarget) = Term.destEq(normal.conclusion).getOrElse(refuse("an equation", target))
            if (reducedTarget == proof.conclusion) force(LogicError.lift(Kernel.eqMp(sym(normal), proof)))
            else refuse("a proof of the body the existential opens to", proof.conclusion)
          }
        case first :: rest =>
          val predicate = logic.destExistsPredicate(target).getOrElse(refuse("an existential", target))
          val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
          val witness = first(domain)
          val applied = force(LogicError.lift(Term.app(predicate, witness)))
          val inner = Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(refuse("an equation", applied))
          force(rules.existsIntro(predicate, witness, witnessedBy(inner, rest, proof)))
      }

    /** `COND c y z = y` from `|- c`, at `num`. */
    def whenHolds(guard: Kernel.Thm, y: String, z: String): Kernel.Thm =
      mp(force(rules.specAll(Kernel.instType(Map(Classical.TypeVariable -> Num), cf(Classical.CondTrue)),
        List(guard.conclusion, term(y, Num), term(z, Num)))), guard)

    /** `COND c y z = z` from `|- ~c`, at `num`. */
    def whenFails(guard: Kernel.Thm, y: String, z: String): Kernel.Thm = {
      val statement = logic.destNot(guard.conclusion).getOrElse(refuse("a negation", guard.conclusion))
      mp(force(rules.specAll(Kernel.instType(Map(Classical.TypeVariable -> Num), cf(Classical.CondFalse)),
        List(statement, term(y, Num), term(z, Num)))), guard)
    }

    /** `|- C a1 ... an = <its body>`, reduced, for a definition of `Resolving`. */
    def unfolded(name: String, arguments: String*): Kernel.Thm = {
      val definition = force(chain.resolving.definition(name))
      val names = arguments.toList.map(variable)
      val equation = force(Conv.unfold(definition, names))
      val body = Term.destEq(equation.conclusion).map(_._2).getOrElse(refuse("an equation", equation.conclusion))
      trans(equation, force(Conv.betaNormalise(body)))
    }

    def openDefinition(name: String, theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
      force(LogicError.lift(Kernel.eqMp(unfolded(name, arguments*), theorem)))

    def checked(name: String, theorem: Kernel.Thm): Kernel.Thm = {
      val text = Statements.collectFirst { case (`name`, statement) => statement }.getOrElse(refuse(name, logic.falsity))
      val expected = force(Parser.proposition(theory, notation, text))
      if (theorem.conclusion == expected && theorem.hypotheses.isEmpty) theorem
      else refuse(s"$name as it is written", theorem.conclusion)
    }

    /* ----------------------------------------------------------- arithmetic */

    /** `|- NUM_LE a c ==> NUM_LE (SUC a) (SUC c)`, by adding one on the left and reading it back. */
    lazy val successorMonotone: Kernel.Thm = {
      val atMost = assume("NUM_LE a c")
      val added = mp(spec(pf(Peano.AddMonotone), "SUC ZERO", "a", "c"), atMost)
      def one(x: String): Kernel.Thm =
        trans(spec(pf(Peano.SuccessorPlus), "ZERO", x), congruent("SUC", spec(pf(Peano.ZeroPlus), x)))
      val onLeft = transport(one("a"), "NUM_LE zz (NUM_ADD (SUC ZERO) c)", added)
      val both = transport(one("c"), "NUM_LE (SUC a) zz", onLeft)
      discharged(both, "NUM_LE a c")
    }

    /** `|- NUM_LE (SUC a) (SUC c) ==> NUM_LE a c`. */
    lazy val successorCancels: Kernel.Thm = {
      val atMost = assume("NUM_LE (SUC a) (SUC c)")
      val below = mp(spec(pf(Peano.BelowThenAtMost), "a", "SUC a", "SUC c"), conj(spec(pf(Peano.BelowSuccessor), "a"), atMost))
      discharged(mp(spec(pf(Peano.AtMostBelowSuccessor), "c", "a"), below), "NUM_LE (SUC a) (SUC c)")
    }

    /** `|- NUM_LT p x ==> SUC (PRE x) = x`: a number above another is a successor. */
    lazy val predecessorBelow: Kernel.Thm = {
      val above = assume("NUM_LT p x")
      val split = spec(nf(Natural.ZeroOrSuccessor), "x")
      val result = byDisjunction(split)(
        zero => exFalso(prop("SUC (PRE x) = x"), absurd(spec(pf(Peano.NotBelowZero), "p"), transport(zero, "NUM_LT p zz", above))),
        successor =>
          opened(successor, "y") { equation =>
            val pre = trans(congruent("PRE", equation), spec(pf(Peano.PreAtSuccessor), "y"))
            trans(congruent("SUC", pre), sym(equation))
          }
      )
      discharged(result, "NUM_LT p x")
    }

    /* ---------------------------------------------------- the pigeonhole on num */

    def injectionPredicate(a: String): String =
      s"!b:num. !g:num->num. (!x:num. NUM_LT x $a ==> NUM_LT (g x) b) ==> " +
        s"(!x:num. !y:num. NUM_LT x $a ==> NUM_LT y $a ==> g x = g y ==> x = y) ==> NUM_LE $a b"

    /** [[Pigeonhole.Injection]], by induction on `a`. */
    lazy val injection: Kernel.Thm = {
      val induction = spec(nf(Natural.Induction), s"\\a:num. ${injectionPredicate("a")}")
      val base = {
        val range = "!x:num. NUM_LT x ZERO ==> NUM_LT (g x) b"
        val injective = "!x:num. !y:num. NUM_LT x ZERO ==> NUM_LT y ZERO ==> (g:num->num) x = g y ==> x = y"
        generalised(discharged(spec(pf(Peano.ZeroIsLeast), "b"), range, injective), "b", "g")
      }
      val step = generalised(discharged(injectionStep, injectionPredicate("a")), "a")
      mp(induction, conj(base, step))
    }

    /**
     * `Pred a ==> Pred (SUC a)` under the assumption `Pred a`.
     *
     * The function on `SUC a` into `b` makes `b` a successor `SUC c`, and folds to
     * `\x. COND (g x = c) (g a) (g x)` on `a` into `c`: whatever landed on `c` goes where `a` went,
     * which is not `c` because `g` is injective.
     */
    def injectionStep: Kernel.Thm = {
      val hypothesis = assume(injectionPredicate("a"))
      val rangeText = "!x:num. NUM_LT x (SUC a) ==> NUM_LT (g x) b"
      val injectiveText = "!x:num. !y:num. NUM_LT x (SUC a) ==> NUM_LT y (SUC a) ==> (g:num->num) x = g y ==> x = y"
      val range = assume(rangeText)
      val injective = assume(injectiveText)
      val aBelow = spec(pf(Peano.BelowSuccessor), "a")
      val atA = mp(spec(range, "a"), aBelow)
      val goal = prop("NUM_LE (SUC a) b")

      val split = spec(nf(Natural.ZeroOrSuccessor), "b")
      val result = byDisjunction(split)(
        zero => exFalso(goal, absurd(spec(pf(Peano.NotBelowZero), "g a"), transport(zero, "NUM_LT (g a) zz", atA))),
        successor =>
          opened(successor, "c") { bIsSuccessor =>
            def below(x: String): Kernel.Thm =
              mp(spec(pf(Peano.StrictTransitive), x, "a", "SUC a"), conj(assume(s"NUM_LT $x a"), aBelow))
            def underSuccessor(x: String): Kernel.Thm = transport(bIsSuccessor, s"NUM_LT (g $x) zz", mp(spec(range, x), below(x)))
            def same(x: String, y: String, xBelow: Kernel.Thm, yBelow: Kernel.Thm, equal: Kernel.Thm): Kernel.Thm =
              mp(spec(injective, x, y), xBelow, yBelow, equal)
            def selfBelow(xIsA: Kernel.Thm, x: String): Kernel.Thm =
              absurd(spec(pf(Peano.StrictIrreflexive), "a"), transport(xIsA, "NUM_LT zz a", assume(s"NUM_LT $x a")))

            // The folded function stays below `c`.
            val folded = "COND (g x = c) (g a) (g x)"
            val foldedRange = {
              val atX = underSuccessor("x")
              val result = cases(prop("g x = c"))(
                hit => {
                  val value = whenHolds(hit, "g a", "g x")
                  val aSplit = mp(spec(pf(Peano.BelowSuccessorCases), "c", "g a"), transport(bIsSuccessor, "NUM_LT (g a) zz", atA))
                  byDisjunction(aSplit)(
                    strictly => transport(sym(value), "NUM_LT zz c", strictly),
                    onC => {
                      val xIsA = same("x", "a", below("x"), aBelow, trans(hit, sym(onC)))
                      exFalso(prop(s"NUM_LT ($folded) c"), selfBelow(xIsA, "x"))
                    }
                  )
                },
                miss => {
                  val value = whenFails(miss, "g a", "g x")
                  val xSplit = mp(spec(pf(Peano.BelowSuccessorCases), "c", "g x"), atX)
                  byDisjunction(xSplit)(
                    strictly => transport(sym(value), "NUM_LT zz c", strictly),
                    onC => exFalso(prop(s"NUM_LT ($folded) c"), absurd(miss, onC))
                  )
                }
              )
              generalised(discharged(result, "NUM_LT x a"), "x")
            }

            // And is injective on `a`.
            val foldedInjective = {
              val equalText = s"COND (g x = c) (g a) (g x) = COND (g y = c) (g a) (g y)"
              val equal = assume(equalText)
              val xy = prop("(x:num) = y")
              val result = cases(prop("g x = c"))(
                xHit => {
                  val xValue = whenHolds(xHit, "g a", "g x")
                  cases(prop("g y = c"))(
                    yHit => same("x", "y", below("x"), below("y"), trans(xHit, sym(yHit))),
                    yMiss => {
                      val aIsY = trans(trans(sym(xValue), equal), whenFails(yMiss, "g a", "g y"))
                      val yIsA = sym(same("a", "y", aBelow, below("y"), aIsY))
                      exFalso(xy, selfBelow(yIsA, "y"))
                    }
                  )
                },
                xMiss => {
                  val xValue = whenFails(xMiss, "g a", "g x")
                  cases(prop("g y = c"))(
                    yHit => {
                      val xIsA = same("x", "a", below("x"), aBelow, trans(trans(sym(xValue), equal), whenHolds(yHit, "g a", "g y")))
                      exFalso(xy, selfBelow(xIsA, "x"))
                    },
                    yMiss => same("x", "y", below("x"), below("y"), trans(trans(sym(xValue), equal), whenFails(yMiss, "g a", "g y")))
                  )
                }
              )
              generalised(discharged(result, "NUM_LT x a", "NUM_LT y a", equalText), "x", "y")
            }

            val atC = mp(spec(hypothesis, "c", "\\w:num. COND (g w = c) (g a) (g w)"), foldedRange, foldedInjective)
            transport(sym(bIsSuccessor), "NUM_LE (SUC a) zz", mp(inst(successorMonotone), atC))
          }
      )
      generalised(discharged(result, rangeText, injectiveText), "b", "g")
    }

    /* ------------------------------------------------------ critical assignments */

    val A: String => String = asg("p", call("f"))

    /** `|- NUM_LT h n ==> NUM_LT u n ==> q * n + h = r * n + u ==> q = r /\ h = u`. */
    lazy val decoded: Kernel.Thm = {
      val equalText = s"${enc("q", "h")} = ${enc("r", "u")}"
      val equal = assume(equalText)
      val first = transport(spec(pf(Peano.MulCommutative), "q", "n"), s"NUM_ADD zz h = ${enc("r", "u")}", equal)
      val second = transport(spec(pf(Peano.MulCommutative), "r", "n"), "NUM_ADD (NUM_MUL n q) h = NUM_ADD zz u", first)
      val unique = spec(force(chain.modular.fact(Modular.DivisionUnique)), "n", "q", "h", "r", "u")
      val both = mp(unique, conj(second, conj(assume("NUM_LT h n"), assume("NUM_LT u n"))))
      discharged(both, "NUM_LT h n", "NUM_LT u n", equalText)
    }

    /** `|- M(p, f) ==> NUM_LT h n ==> A(q * n + h) ==> ~(q = p) /\ f q = h`. */
    lazy val assignedAt: Kernel.Thm = {
      val matched = assume(matching("p", call("f")))
      val holeBelow = assume("NUM_LT h n")
      val assigned = assume(A(enc("q", "h")))
      val result = opened(assigned, "t") { body =>
        val tAtMost = left(body)
        val tOther = left(right(body))
        val equal = right(right(body))
        val tBelow = mp(spec(left(matched), "t"), conj(tAtMost, tOther))
        val parts = mp(inst(decoded, "r" -> "t", "u" -> "f t"), holeBelow, tBelow, equal)
        val qIsT = left(parts)
        conj(substituted(sym(qIsT), tOther), trans(congruent("f", qIsT), sym(right(parts))))
      }
      discharged(result, matching("p", call("f")), "NUM_LT h n", A(enc("q", "h")))
    }

    /** `|- NUM_LE q n ==> ~(q = p) ==> A(q * n + f q)`. */
    lazy val assignedOwn: Kernel.Thm = {
      val proof = conj(assume("NUM_LE q n"), conj(assume("~((q:num) = p)"), Conv.refl(term(enc("q", "(f q)"), Num))))
      discharged(witnessed(prop(A(enc("q", "(f q)"))), List("q"), proof), "NUM_LE q n", "~((q:num) = p)")
    }

    /** `|- bad(j, p)` from its three parts, the witness of the matching being `witness`. */
    def badFrom(j: String, p: String, atMost: Kernel.Thm, matched: Kernel.Thm, unsatisfied: Kernel.Thm, witness: String): Kernel.Thm =
      conj(atMost, witnessed(prop(falsified(j, p)), List(witness), conj(matched, unsatisfied)))

    /** `|- A(v j i) = s j i ==> sat(A, j)` read at a given index, as a theorem. */
    def satisfiedAt(a: String => String, j: String, index: String, below: Kernel.Thm, equal: Kernel.Thm): Kernel.Thm =
      witnessed(prop(sat(a, j)), List(index), conj(below, equal))

    /** `|- pigeonClause(j, c) ==> bad(j, p) ==> p = c`: only the clause's own pigeon is bad for it. */
    lazy val pigeonOnlyOwn: Kernel.Thm = {
      val clause = assume(pigeonClause("j", "c"))
      val isBad = assume(bad("j", "p"))
      val result = byContradiction(prop("(p:num) = c")) { other =>
        opened(right(isBad), "f") { body =>
          val matched = left(body)
          val unsatisfied = right(body)
          val cAtMost = left(clause)
          val cOther = unequalSym(other)
          val cHole = mp(spec(left(matched), "c"), conj(cAtMost, cOther))
          val literal = mp(spec(right(right(clause)), "f c"), cHole)
          opened(literal, "i") { found =>
            val iBelow = left(found)
            val variableIs = left(right(found))
            val positive = right(right(found))
            val assigned = mp(inst(assignedOwn, "q" -> "c"), cAtMost, cOther)
            val atVariable = transport(sym(variableIs), A("zz"), assigned)
            val agrees = trans(truthEquation(atVariable), sym(positive))
            absurd(unsatisfied, satisfiedAt(A, "j", "i", iBelow, agrees))
          }
        }
      }
      discharged(result, pigeonClause("j", "c"), bad("j", "p"))
    }

    /** `|- holeClause(j, c, d, h) ==> ~bad(j, p)`: no pigeon is bad for a hole clause. */
    lazy val holeNoneBad: Kernel.Thm = {
      val clause = assume(holeClause("j", "c", "d", "h"))
      val cBelowD = left(clause)
      val dAtMost = left(right(clause))
      val holeBelow = left(right(right(clause)))
      val cLiteral = left(right(right(right(right(clause)))))
      val dLiteral = right(right(right(right(right(clause)))))
      val cAtMost = mp(spec(pf(Peano.Transitive), "c", "d", "n"), conj(mp(spec(pf(Peano.AtMostFromBelow), "c", "d"), cBelowD), dAtMost))

      val result = refuted(prop(bad("j", "p"))) { isBad =>
        opened(right(isBad), "f") { body =>
          val matched = left(body)
          val unsatisfied = right(body)
          def falseLiteral(literal: Kernel.Thm)(unassigned: Kernel.Thm): Kernel.Thm =
            opened(literal, "i") { found =>
              val atVariable = transport(sym(left(right(found))), s"~${A("zz")}", unassigned)
              val agrees = trans(falseEquation(atVariable), sym(right(right(found))))
              absurd(unsatisfied, satisfiedAt(A, "j", "i", left(found), agrees))
            }
          cases(prop(A(enc("c", "h"))))(
            cAssigned => {
              val cParts = mp(inst(assignedAt, "q" -> "c"), matched, holeBelow, cAssigned)
              cases(prop(A(enc("d", "h"))))(
                dAssigned => {
                  val dParts = mp(inst(assignedAt, "q" -> "d"), matched, holeBelow, dAssigned)
                  val sameHole = trans(right(cParts), sym(right(dParts)))
                  val injective = spec(right(matched), "c", "d")
                  val cIsD = mp(injective, conj(cAtMost, conj(left(cParts), conj(dAtMost, conj(left(dParts), sameHole)))))
                  absurd(spec(pf(Peano.StrictIrreflexive), "c"), transport(sym(cIsD), "NUM_LT c zz", cBelowD))
                },
                falseLiteral(dLiteral)
              )
            },
            falseLiteral(cLiteral)
          )
        }
      }
      discharged(result, holeClause("j", "c", "d", "h"))
    }

    /** `|- carries(pa) ==> carries(pb) ==> bad(j, p) ==> bad(pa, p) \/ bad(pb, p)`. */
    lazy val resolventBad: Kernel.Thm = {
      val carriesA = assume(carries("pa", "j", "T"))
      val carriesB = assume(carries("pb", "j", "F"))
      val isBad = assume(bad("j", "p"))
      val goal = prop(s"${bad("pa", "p")} \\/ ${bad("pb", "p")}")
      val result = opened(right(isBad), "f") { body =>
        val matched = left(body)
        val unsatisfied = right(body)
        byContradiction(goal) { neither =>
          def parentSatisfied(parent: String): Kernel.Thm =
            byContradiction(prop(sat(A, parent))) { unsatisfiedThere =>
              absurd(neither, disjoined(goal, badFrom(parent, "p", left(isBad), matched, unsatisfiedThere, "f")))
            }
          val step = spec(rf(Resolving.StepSound), s"\\w:num. ${A("w")}", "v pa", "s pa", "v pb", "s pb", "v j", "s j",
            "k pa", "k pb", "k j", "x")
          absurd(unsatisfied, mp(step, carriesA, carriesB, parentSatisfied("pa"), parentSatisfied("pb")))
        }
      }
      discharged(result, carries("pa", "j", "T"), carries("pb", "j", "F"), bad("j", "p"))
    }

    /** `|- k j = ZERO ==> NUM_LE p n ==> M(p, f) ==> bad(j, p)`: every critical assignment falsifies the empty clause. */
    lazy val emptyAllBad: Kernel.Thm = {
      val empty = assume("k j = ZERO")
      val atMost = assume("NUM_LE p n")
      val matched = assume(matching("p", call("f")))
      val nothing = mp(spec(rf(Resolving.EmptyUnsatisfiable), s"\\w:num. ${A("w")}", "v j", "s j", "k j"), empty)
      discharged(badFrom("j", "p", atMost, matched, nothing, "f"), "k j = ZERO", "NUM_LE p n", matching("p", call("f")))
    }

    /** `|- NUM_LE p n ==> M(p, \x. COND (NUM_LT x p) x (PRE x))`: every pigeon has a critical assignment. */
    lazy val matchingExists: Kernel.Thm = {
      val atMost = assume("NUM_LE p n")
      val order = pf(Peano.Trichotomy)

      def above(x: String, notBelow: Kernel.Thm, other: Kernel.Thm): Kernel.Thm =
        taut(prop(s"NUM_LT p $x"), spec(order, x, "p"), notBelow, other, spec(pf(Peano.StrictIrreflexive), x))
      // The trichotomy's middle disjunct is `x = p`; its denial arrives as `~(x = p)`.

      val range = {
        val both = assume("NUM_LE x n /\\ ~((x:num) = p)")
        val xAtMost = left(both)
        val xOther = right(both)
        val result = cases(prop("NUM_LT x p"))(
          lower => transport(sym(whenHolds(lower, "x", "PRE x")), "NUM_LT zz n",
            mp(spec(pf(Peano.BelowThenAtMost), "x", "p", "n"), conj(lower, atMost))),
          higher => {
            val successor = mp(inst(predecessorBelow), above("x", higher, xOther))
            val preBelow = transport(successor, "NUM_LT (PRE x) zz", spec(pf(Peano.BelowSuccessor), "PRE x"))
            transport(sym(whenFails(higher, "x", "PRE x")), "NUM_LT zz n",
              mp(spec(pf(Peano.BelowThenAtMost), "PRE x", "x", "n"), conj(preBelow, xAtMost)))
          }
        )
        generalised(discharged(result, "NUM_LE x n /\\ ~((x:num) = p)"), "x")
      }

      val injective = {
        val premise = s"NUM_LE x n /\\ ~((x:num) = p) /\\ NUM_LE y n /\\ ~((y:num) = p) /\\ ${shifted("x")} = ${shifted("y")}"
        val all = assume(premise)
        val xOther = left(right(all))
        val yOther = left(right(right(right(all))))
        val equal = right(right(right(right(all))))
        val xy = prop("(x:num) = y")
        def atLeast(z: String, higher: Kernel.Thm, other: Kernel.Thm): Kernel.Thm = {
          val successor = mp(inst(predecessorBelow, "x" -> z), above(z, higher, other))
          mp(spec(pf(Peano.AtMostBelowSuccessor), s"PRE $z", "p"), transport(sym(successor), "NUM_LT p zz", above(z, higher, other)))
        }
        def crossed(lowX: Kernel.Thm, valueIsPre: Kernel.Thm, z: String, higher: Kernel.Thm, other: Kernel.Thm): Kernel.Thm = {
          // `x < p`, `x = PRE z` and `p <= PRE z` cannot all hold.
          val pAtMostX = transport(sym(valueIsPre), "NUM_LE p zz", atLeast(z, higher, other))
          absurd(mp(spec(pf(Peano.BelowExcludesAtMost), "x", "p"), lowX), pAtMostX)
        }
        val result = cases(prop("NUM_LT x p"))(
          xLow => cases(prop("NUM_LT y p"))(
            yLow => trans(trans(sym(whenHolds(xLow, "x", "PRE x")), equal), whenHolds(yLow, "y", "PRE y")),
            yHigh => {
              val xIsPre = trans(trans(sym(whenHolds(xLow, "x", "PRE x")), equal), whenFails(yHigh, "y", "PRE y"))
              exFalso(xy, crossed(xLow, xIsPre, "y", yHigh, yOther))
            }
          ),
          xHigh => cases(prop("NUM_LT y p"))(
            yLow => {
              val yIsPre = trans(trans(sym(whenHolds(yLow, "y", "PRE y")), sym(equal)), whenFails(xHigh, "x", "PRE x"))
              val pAtMostY = transport(sym(yIsPre), "NUM_LE p zz", atLeast("x", xHigh, xOther))
              exFalso(xy, absurd(mp(spec(pf(Peano.BelowExcludesAtMost), "y", "p"), yLow), pAtMostY))
            },
            yHigh => {
              val pres = trans(trans(sym(whenFails(xHigh, "x", "PRE x")), equal), whenFails(yHigh, "y", "PRE y"))
              val xBack = mp(inst(predecessorBelow), above("x", xHigh, xOther))
              val yBack = mp(inst(predecessorBelow, "x" -> "y"), above("y", yHigh, yOther))
              trans(trans(sym(xBack), congruent("SUC", pres)), yBack)
            }
          )
        )
        generalised(discharged(result, premise), "x", "y")
      }
      val statement = prop(matching("p", shifted))
      val proof = conj(range, injective)
      if (proof.conclusion != statement) refuse("the shifted matching as it is written", proof.conclusion)
      discharged(proof, "NUM_LE p n")
    }

    /** `|- M(p, f) ==> NUM_LE q n ==> ~(q = p) ==> M(q, \x. COND (x = p) (f q) (f x))`. */
    lazy val swappedMatching: Kernel.Thm = {
      val matched = assume(matching("p", call("f")))
      val qAtMost = assume("NUM_LE q n")
      val qOther = assume("~((q:num) = p)")
      val qHole = mp(spec(left(matched), "q"), conj(qAtMost, qOther))

      val range = {
        val both = assume("NUM_LE x n /\\ ~((x:num) = q)")
        val result = cases(prop("(x:num) = p"))(
          isP => transport(sym(whenHolds(isP, "f q", "f x")), "NUM_LT zz n", qHole),
          other => transport(sym(whenFails(other, "f q", "f x")), "NUM_LT zz n",
            mp(spec(left(matched), "x"), conj(left(both), other)))
        )
        generalised(discharged(result, "NUM_LE x n /\\ ~((x:num) = q)"), "x")
      }

      val injective = {
        val premise = s"NUM_LE x n /\\ ~((x:num) = q) /\\ NUM_LE y n /\\ ~((y:num) = q) /\\ ${swapped("x")} = ${swapped("y")}"
        val all = assume(premise)
        val xAtMost = left(all)
        val xNotQ = left(right(all))
        val yAtMost = left(right(right(all)))
        val yNotQ = left(right(right(right(all))))
        val equal = right(right(right(right(all))))
        val xy = prop("(x:num) = y")
        def unique(a: String, b: String, aAtMost: Kernel.Thm, aOther: Kernel.Thm, bAtMost: Kernel.Thm, bOther: Kernel.Thm, same: Kernel.Thm) =
          mp(spec(right(matched), a, b), conj(aAtMost, conj(aOther, conj(bAtMost, conj(bOther, same)))))
        val result = cases(prop("(x:num) = p"))(
          xIsP => cases(prop("(y:num) = p"))(
            yIsP => trans(xIsP, sym(yIsP)),
            yOther => {
              val same = trans(trans(sym(whenHolds(xIsP, "f q", "f x")), equal), whenFails(yOther, "f q", "f y"))
              exFalso(xy, absurd(yNotQ, sym(unique("q", "y", qAtMost, qOther, yAtMost, yOther, same))))
            }
          ),
          xOther => cases(prop("(y:num) = p"))(
            yIsP => {
              val same = trans(trans(sym(whenFails(xOther, "f q", "f x")), equal), whenHolds(yIsP, "f q", "f y"))
              exFalso(xy, absurd(xNotQ, unique("x", "q", xAtMost, xOther, qAtMost, qOther, same)))
            },
            yOther => {
              val same = trans(trans(sym(whenFails(xOther, "f q", "f x")), equal), whenFails(yOther, "f q", "f y"))
              unique("x", "y", xAtMost, xOther, yAtMost, yOther, same)
            }
          )
        )
        generalised(discharged(result, premise), "x", "y")
      }
      val proof = conj(range, injective)
      if (proof.conclusion != prop(matching("q", swapped))) refuse("the swapped matching as it is written", proof.conclusion)
      discharged(proof, matching("p", call("f")), "NUM_LE q n", "~((q:num) = p)")
    }

    val B: String => String = asg("q", swapped)

    /** `|- A(x) ==> ~B(x) ==> x = q * n + f q`: `p`'s assignment and not `q`'s means `q`'s own variable. */
    lazy val onlyFirst: Kernel.Thm = {
      val first = assume(A("x"))
      val notSecond = assume(s"~${B("x")}")
      val goal = prop(s"x = ${enc("q", "(f q)")}")
      val result = opened(first, "t") { body =>
        cases(prop("(t:num) = q"))(
          isQ => substituted(isQ, right(right(body))),
          other => {
            val value = whenFails(left(right(body)), "f q", "f t")
            val atT = transport(sym(value), s"x = ${enc("t", "zz")}", right(right(body)))
            exFalso(goal, absurd(notSecond, witnessed(prop(B("x")), List("t"), conj(left(body), conj(other, atT)))))
          }
        )
      }
      discharged(result, A("x"), s"~${B("x")}")
    }

    /** `|- ~A(x) ==> B(x) ==> x = p * n + f q`: `q`'s assignment and not `p`'s means `p` in `q`'s hole. */
    lazy val onlySecond: Kernel.Thm = {
      val notFirst = assume(s"~${A("x")}")
      val second = assume(B("x"))
      val goal = prop(s"x = ${enc("p", "(f q)")}")
      val result = opened(second, "t") { body =>
        cases(prop("(t:num) = p"))(
          isP => {
            val atFq = transport(whenHolds(isP, "f q", "f t"), s"x = ${enc("t", "zz")}", right(right(body)))
            substituted(isP, atFq)
          },
          other => {
            val atFt = transport(whenFails(other, "f q", "f t"), s"x = ${enc("t", "zz")}", right(right(body)))
            exFalso(goal, absurd(notFirst, witnessed(prop(A("x")), List("t"), conj(left(body), conj(other, atFt)))))
          }
        )
      }
      discharged(result, s"~${A("x")}", B("x"))
    }

    /**
     * `|- NUM_LE p n ==> M(p, f) ==> ~sat(A, j) ==> NUM_LE q n ==> ~(q = p) ==> ~bad(j, q) ==>
     *     ?i. NUM_LT i (k j) /\ forced(v j i, q)`.
     *
     * `q`'s assignment satisfies the clause somewhere and `p`'s satisfies it nowhere, so they disagree
     * at that literal's variable, and `onlyFirst` and `onlySecond` say which variables those are.
     * The disagreement is four cases by hand: both procedures read `A = s` as an atom.
     */
    lazy val literalForced: Kernel.Thm = {
      val atMost = assume("NUM_LE p n")
      val matched = assume(matching("p", call("f")))
      val unsatisfied = assume(s"~${sat(A, "j")}")
      val qAtMost = assume("NUM_LE q n")
      val qOther = assume("~((q:num) = p)")
      val notBad = assume(s"~${bad("j", "q")}")
      val moved = mp(swappedMatching, matched, qAtMost, qOther)
      val lambda = "\\w:num. COND (w = p) (f q) (f w)"
      val satisfiedB = byContradiction(prop(sat(B, "j"))) { unsatisfiedB =>
        absurd(notBad, badFrom("j", "q", qAtMost, moved, unsatisfiedB, lambda))
      }
      val goal = prop(s"?i:num. NUM_LT i (k j) /\\ ${forcedAt("(v j i)", "q")}")
      val result = opened(satisfiedB, "i") { found =>
        val iBelow = left(found)
        val secondAgrees = right(found)
        val x = "(v j i)"
        val firstDisagrees = refuted(prop(s"${A(x)} = s j i")) { agrees =>
          absurd(unsatisfied, satisfiedAt(A, "j", "i", iBelow, agrees))
        }
        def conclude(literal: Kernel.Thm): Kernel.Thm =
          witnessed(goal, List("i"), conj(iBelow, disjoined(prop(forcedAt(x, "q")), literal)))
        cases(prop(A(x)))(
          first => cases(prop(B(x)))(
            second => exFalso(goal, absurd(firstDisagrees, trans(trans(truthEquation(first), sym(truthEquation(second))), secondAgrees))),
            notSecond => conclude(mp(inst(onlyFirst, "x" -> x), first, notSecond))
          ),
          notFirst => cases(prop(B(x)))(
            second => conclude(mp(inst(onlySecond, "x" -> x), notFirst, second)),
            notSecond => exFalso(goal, absurd(firstDisagrees, trans(trans(falseEquation(notFirst), sym(falseEquation(notSecond))), secondAgrees)))
          )
        )
      }
      discharged(result, "NUM_LE p n", matching("p", call("f")), s"~${sat(A, "j")}", "NUM_LE q n", "~((q:num) = p)",
        s"~${bad("j", "q")}")
    }

    /** `|- M(p, f) ==> NUM_LE q n ==> ~(q = p) ==> NUM_LE r n ==> ~(r = p) ==> forced(o, q) ==> forced(o, r) ==> q = r`. */
    lazy val forcedInjective: Kernel.Thm = {
      val matched = assume(matching("p", call("f")))
      val qAtMost = assume("NUM_LE q n")
      val qOther = assume("~((q:num) = p)")
      val rAtMost = assume("NUM_LE r n")
      val rOther = assume("~((r:num) = p)")
      val qHole = mp(spec(left(matched), "q"), conj(qAtMost, qOther))
      val rHole = mp(spec(left(matched), "r"), conj(rAtMost, rOther))
      val goal = prop("(q:num) = r")
      def parts(first: String, second: String, equal: Kernel.Thm): Kernel.Thm =
        mp(inst(decoded, "q" -> first, "r" -> second, "h" -> "f q", "u" -> "f r"), qHole, rHole, equal)
      val result = byDisjunction(assume(forcedAt("o", "q")))(
        qOwn => byDisjunction(assume(forcedAt("o", "r")))(
          rOwn => left(parts("q", "r", trans(sym(qOwn), rOwn))),
          rMoved => exFalso(goal, absurd(qOther, left(parts("q", "p", trans(sym(qOwn), rMoved)))))
        ),
        qMoved => byDisjunction(assume(forcedAt("o", "r")))(
          rOwn => exFalso(goal, absurd(rOther, sym(left(parts("p", "r", trans(sym(qMoved), rOwn)))))),
          rMoved => {
            val sameHole = right(parts("p", "p", trans(sym(qMoved), rMoved)))
            mp(spec(right(matched), "q", "r"), conj(qAtMost, conj(qOther, conj(rAtMost, conj(rOther, sameHole)))))
          }
        )
      )
      discharged(result, matching("p", call("f")), "NUM_LE q n", "~((q:num) = p)", "NUM_LE r n", "~((r:num) = p)",
        forcedAt("o", "q"), forcedAt("o", "r"))
    }

    /** `|- (!q. P q ==> ?i. Q q i) ==> ?hh. !q. P q ==> Q q (hh q)`, by choice. */
    lazy val skolem: Kernel.Thm = {
      val premiseText = "!q:num. P q ==> ?i:num. Q q i"
      val premise = assume(premiseText)
      val holds = assume("P q")
      val exists = mp(spec(premise, "q"), holds)
      // `Q q (select (\i. Q q i))`, the witness named by choice and reduced once.
      val chosen = reduced(force(classical.axiom(Classical.Choice).flatMap(Classical.witnessFrom(logic, _, exists))))
      val every = generalised(discharged(chosen, "P q"), "q")
      val select = chosen.conclusion match {
        case App(_, choice) => choice
        case other => refuse("an application to the chosen witness", other)
      }
      val function = force(LogicError.lift(Term.abs(variable("q"), select)))
      val target = prop("?hh:num->num. !q:num. P q ==> Q q (hh q)")
      discharged(witnessedBy(target, List(_ => function), every), premiseText)
    }

    /** What the counting function is at a pigeon, with what the case that decided it knows. */
    sealed trait Value
    final case class First(isFirst: Kernel.Thm, value: Kernel.Thm) extends Value
    final case class Second(isSecond: Kernel.Thm, value: Kernel.Thm) extends Value
    final case class Other(value: Kernel.Thm, below: Kernel.Thm, forced: Kernel.Thm, notFirst: Kernel.Thm) extends Value

    /* ---------------------------------------------------------------- the theorem */

    /** [[Pigeonhole.DerivedWidth]]. */
    lazy val derivedWidth: Kernel.Thm = {
      val positiveText = "NUM_LT ZERO n"
      val inputsText = s"!j:num. NUM_LT j inputs ==> $Clause"
      val refutationText = "RES_REFUTATION k v s inputs m"
      val positive = assume(positiveText)
      val inputs = assume(inputsText)
      val refutation = assume(refutationText)
      val halves = openDefinition(Resolving.Refutation, refutation, "k", "v", "s", "inputs", "m")
      val justified = left(halves)
      val reachesEmpty = right(halves)
      val goal = prop("?j:num. NUM_LE inputs j /\\ NUM_LT j m /\\ NUM_LE n (SUC (k j))")

      // Two pigeons, 0 and 1, have critical assignments; that is where `0 < n` is spent.
      val zeroAtMost = spec(pf(Peano.ZeroIsLeast), "n")
      val oneAtMost = byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "n"))(
        zero => exFalso(prop("NUM_LE (SUC ZERO) n"),
          absurd(spec(pf(Peano.StrictIrreflexive), "ZERO"), transport(zero, "NUM_LT ZERO zz", positive))),
        successor => opened(successor, "y") { nIsSuccessor =>
          val above = mp(inst(successorMonotone, "a" -> "ZERO", "c" -> "y"), spec(pf(Peano.ZeroIsLeast), "y"))
          transport(sym(nIsSuccessor), "NUM_LE (SUC ZERO) zz", above)
        }
      )
      val zeroOne = unequalSym(spec(nf(Natural.SuccessorNotZero), "ZERO"))

      val least = opened(reachesEmpty, "e") { empty =>
        val eBelow = left(empty)
        val eEmpty = right(empty)
        def emptyBad(pigeon: String, atMost: Kernel.Thm): Kernel.Thm = {
          val matched = mp(inst(matchingExists, "p" -> pigeon), atMost)
          val function = s"\\w:num. COND (NUM_LT w ($pigeon)) w (PRE w)"
          mp(inst(emptyAllBad, "j" -> "e", "p" -> pigeon, "f" -> function), eEmpty, atMost, matched)
        }
        val twoAtE = conj(eBelow, witnessed(prop(s"?p1:num. ?p2:num. ~(p1 = p2) /\\ ${bad("e", "p1")} /\\ ${bad("e", "p2")}"),
          List("ZERO", "SUC ZERO"), conj(zeroOne, conj(emptyBad("ZERO", zeroAtMost), emptyBad("SUC ZERO", oneAtMost)))))
        val instance = spec(pf(Peano.LeastNumber), s"\\w:num. ${two("w")}")
        val (someTwo, _) = logic.destImp(instance.conclusion).getOrElse(refuse("an implication", instance.conclusion))
        mp(instance, witnessed(someTwo, List("e"), twoAtE))
      }

      val result = opened(least, "j") { body =>
        val jTwo = left(body)
        val minimal = right(body)
        val jBelow = left(jTwo)
        opened(right(jTwo), "p1") { afterFirst =>
          opened(afterFirst, "p2") { pair =>
            val distinct = left(pair)
            val badFirst = left(right(pair))
            val badSecond = right(right(pair))

            // Not an input: an input has at most one bad pigeon.
            val notInput = refuted(prop("NUM_LT j inputs")) { isInput =>
              val clause = mp(spec(inputs, "j"), isInput)
              byDisjunction(clause)(
                pigeon => opened(pigeon, "c") { own =>
                  val first = mp(inst(pigeonOnlyOwn, "p" -> "p1"), own, badFirst)
                  val second = mp(inst(pigeonOnlyOwn, "p" -> "p2"), own, badSecond)
                  absurd(distinct, trans(first, sym(second)))
                },
                holes => opened(holes, "c") { afterC =>
                  opened(afterC, "d") { afterD =>
                    opened(afterD, "h") { holeParts =>
                      absurd(mp(inst(holeNoneBad, "p" -> "p1"), holeParts), badFirst)
                    }
                  }
                }
              )
            }
            val inputsAtMost = mp(spec(pf(Peano.AtMostFromNotBelow), "j", "inputs"), notInput)

            val justification = openDefinition(Resolving.JustifiedName, mp(spec(justified, "j"), jBelow), "k", "v", "s", "inputs", "j")
            val width = byDisjunction(justification)(
              isInput => exFalso(prop("NUM_LE n (SUC (k j))"), absurd(notInput, isInput)),
              resolvent => opened(resolvent, "pa") { afterA =>
                opened(afterA, "pb") { afterB =>
                  opened(afterB, "x") { step =>
                    wide(jBelow, minimal, distinct, badFirst, badSecond, step)
                  }
                }
              }
            )
            witnessed(goal, List("j"), conj(inputsAtMost, conj(jBelow, width)))
          }
        }
      }
      generalised(discharged(result, positiveText, inputsText, refutationText), "n", "k", "v", "s", "inputs", "m")
    }

    /**
     * `NUM_LE n (SUC (k j))` at the first clause with two bad pigeons, `p1` and `p2`, derived from
     * `pa` and `pb`.
     */
    def wide(
      jBelow: Kernel.Thm,
      minimal: Kernel.Thm,
      distinct: Kernel.Thm,
      badFirst: Kernel.Thm,
      badSecond: Kernel.Thm,
      step: Kernel.Thm
    ): Kernel.Thm = {
      val paBelow = left(step)
      val pbBelow = left(right(step))
      val carriesA = left(right(right(step)))
      val carriesB = right(right(right(step)))

      /** `|- bad(parent, r) ==> bad(parent, t) ==> r = t`, since a parent is below the first clause with two. */
      def atMostOne(parent: String, parentBelow: Kernel.Thm, r: String, t: String): Kernel.Thm = {
        val notTwo = mp(spec(minimal, parent), parentBelow)
        val parentUnderM = mp(spec(pf(Peano.StrictTransitive), parent, "j", "m"), conj(parentBelow, jBelow))
        val first = assume(bad(parent, r))
        val second = assume(bad(parent, t))
        val same = byContradiction(prop(s"($r:num) = $t")) { differ =>
          absurd(notTwo, conj(parentUnderM,
            witnessed(prop(s"?p1:num. ?p2:num. ~(p1 = p2) /\\ ${bad(parent, "p1")} /\\ ${bad(parent, "p2")}"),
              List(r, t), conj(differ, conj(first, second)))))
        }
        discharged(same, bad(parent, r), bad(parent, t))
      }
      def split(pigeon: String, isBad: Kernel.Thm): Kernel.Thm =
        mp(inst(resolventBad, "p" -> pigeon), carriesA, carriesB, isBad)

      // A third bad pigeon is one of the two: each parent holds at most one.
      val third = {
        val isBad = assume(bad("j", "q"))
        val uniques = for {
          (parent, below) <- List(("pa", paBelow), ("pb", pbBelow))
          (r, t) <- List(("p1", "p2"), ("q", "p1"), ("q", "p2"))
        } yield atMostOne(parent, below, r, t)
        val answer = taut(prop("(q:num) = p1 \\/ (q:num) = p2"),
          (List(split("p1", badFirst), split("p2", badSecond), split("q", isBad), distinct) ++ uniques)*)
        discharged(answer, bad("j", "q"))
      }

      opened(right(badFirst), "f") { body =>
        val matched = left(body)
        val unsatisfied = right(body)
        val firstAtMost = left(badFirst)
        val forcedHere = inst(literalForced, "p" -> "p1")
        val everyOther = {
          val premise = "NUM_LE q n /\\ ~((q:num) = p1) /\\ ~((q:num) = p2)"
          val all = assume(premise)
          val notBad = refuted(prop(bad("j", "q"))) { isBad =>
            byDisjunction(mp(third, isBad))(
              isFirst => absurd(left(right(all)), isFirst),
              isSecond => absurd(right(right(all)), isSecond)
            )
          }
          val found = mp(forcedHere, firstAtMost, matched, unsatisfied, left(all), left(right(all)), notBad)
          generalised(discharged(found, premise), "q")
        }
        val chosen = mp(inst(skolem,
          "P" -> "\\q:num. NUM_LE q n /\\ ~(q = p1) /\\ ~(q = p2)",
          "Q" -> s"\\q:num. \\i:num. NUM_LT i (k j) /\\ ${forcedAt("(v j i)", "q", "p1")}"
        ), everyOther)

        opened(chosen, "hh") { property =>
          val g = "COND (x = p1) (k j) (COND (x = p2) (SUC (k j)) (hh x))"
          val kBelow = spec(pf(Peano.BelowSuccessor), "k j")
          val successorBelow = spec(pf(Peano.BelowSuccessor), "SUC (k j)")
          val kBelowTwo = mp(spec(pf(Peano.StrictTransitive), "k j", "SUC (k j)", "SUC (SUC (k j))"), conj(kBelow, successorBelow))

          def at(z: String): String = g.replace("x", z)
          def classify(z: String, atMost: Kernel.Thm)(reach: Value => Kernel.Thm): Kernel.Thm =
            cases(prop(s"($z:num) = p1"))(
              isFirst => reach(First(isFirst, whenHolds(isFirst, "k j", s"COND ($z = p2) (SUC (k j)) (hh $z)"))),
              notFirst => {
                val outer = whenFails(notFirst, "k j", s"COND ($z = p2) (SUC (k j)) (hh $z)")
                cases(prop(s"($z:num) = p2"))(
                  isSecond => reach(Second(isSecond, trans(outer, whenHolds(isSecond, "SUC (k j)", s"hh $z")))),
                  notSecond => {
                    val known = mp(spec(property, z), conj(atMost, conj(notFirst, notSecond)))
                    reach(Other(trans(outer, whenFails(notSecond, "SUC (k j)", s"hh $z")), left(known), right(known), notFirst))
                  }
                )
              }
            )

          val range = {
            val xAtMost = mp(spec(pf(Peano.AtMostBelowSuccessor), "n", "x"), assume("NUM_LT x (SUC n)"))
            val result = classify("x", xAtMost) {
              case First(_, value) => transport(sym(value), "NUM_LT zz (SUC (SUC (k j)))", kBelowTwo)
              case Second(_, value) => transport(sym(value), "NUM_LT zz (SUC (SUC (k j)))", successorBelow)
              case Other(value, below, _, _) =>
                val chain1 = mp(spec(pf(Peano.StrictTransitive), "hh x", "k j", "SUC (SUC (k j))"), conj(below, kBelowTwo))
                transport(sym(value), "NUM_LT zz (SUC (SUC (k j)))", chain1)
            }
            generalised(discharged(result, "NUM_LT x (SUC n)"), "x")
          }

          val injective = {
            val xAtMost = mp(spec(pf(Peano.AtMostBelowSuccessor), "n", "x"), assume("NUM_LT x (SUC n)"))
            val yAtMost = mp(spec(pf(Peano.AtMostBelowSuccessor), "n", "y"), assume("NUM_LT y (SUC n)"))
            val equalText = s"${at("x")} = ${at("y")}"
            val equal = assume(equalText)
            val xy = prop("(x:num) = y")
            def never(statement: Kernel.Thm): Kernel.Thm = exFalso(xy, statement)
            def notSelf(equation: Kernel.Thm): Kernel.Thm =
              // `k j = SUC (k j)` is false.
              absurd(spec(pf(Peano.SuccessorNotSelf), "k j"), sym(equation))
            def notBelowSelf(term: String, below: Kernel.Thm): Kernel.Thm =
              absurd(spec(pf(Peano.StrictIrreflexive), term), below)
            def aboveThenBelow(value: Kernel.Thm, below: Kernel.Thm): Kernel.Thm = {
              // `SUC (k j) = hh z` and `hh z < k j` give `k j < k j`.
              val successorUnder = transport(sym(value), "NUM_LT zz (k j)", below)
              notBelowSelf("k j", mp(spec(pf(Peano.StrictTransitive), "k j", "SUC (k j)", "k j"), conj(kBelow, successorUnder)))
            }
            val result = classify("x", xAtMost) { xValue =>
              classify("y", yAtMost) { yValue =>
                val same = (value: Kernel.Thm, other: Kernel.Thm) => trans(trans(sym(value), equal), other)
                (xValue, yValue) match {
                  case (First(xIs, _), First(yIs, _)) => trans(xIs, sym(yIs))
                  case (Second(xIs, _), Second(yIs, _)) => trans(xIs, sym(yIs))
                  case (First(_, xv), Second(_, yv)) => never(notSelf(same(xv, yv)))
                  case (Second(_, xv), First(_, yv)) => never(notSelf(sym(same(xv, yv))))
                  case (First(_, xv), Other(yv, yBelow, _, _)) =>
                    never(notBelowSelf("k j", transport(sym(same(xv, yv)), "NUM_LT zz (k j)", yBelow)))
                  case (Other(xv, xBelow, _, _), First(_, yv)) =>
                    never(notBelowSelf("k j", transport(same(xv, yv), "NUM_LT zz (k j)", xBelow)))
                  case (Second(_, xv), Other(yv, yBelow, _, _)) => never(aboveThenBelow(same(xv, yv), yBelow))
                  case (Other(xv, xBelow, _, _), Second(_, yv)) => never(aboveThenBelow(sym(same(xv, yv)), xBelow))
                  case (Other(xv, _, xForced, xOther), Other(yv, _, yForced, yOther)) =>
                    // The same index, so the same literal: `forcedInjective` at that literal's variable.
                    val sameIndex = same(xv, yv)
                    val yAtX = transport(sym(sameIndex), forcedAt("(v j zz)", "y", "p1"), yForced)
                    val unique = inst(forcedInjective, "p" -> "p1", "q" -> "x", "r" -> "y", "o" -> "v j (hh x)")
                    mp(unique, matched, xAtMost, xOther, yAtMost, yOther, xForced, yAtX)
                }
              }
            }
            generalised(discharged(result, "NUM_LT x (SUC n)", "NUM_LT y (SUC n)", equalText), "x", "y")
          }

          val bound = mp(spec(injection, "SUC n", "SUC (SUC (k j))", s"\\x:num. $g"), range, injective)
          mp(inst(successorCancels, "a" -> "n", "c" -> "SUC (k j)"), bound)
        }
      }
    }
  }
}
