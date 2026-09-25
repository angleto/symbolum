package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Every function continuous on `[a, b]` has a gauge integral there.
 *
 * `Integral` defines the integral and proves the fundamental theorem for a derivative, and until
 * this nothing said that a continuous function has an integral at all, so `integral f a b` of one
 * was a `select` over a predicate nothing was known to satisfy. This is the existence, and it is
 * two arguments, neither of which compares two divisions directly.
 *
 * == A Cauchy criterion that glues ==
 *
 * `C u w` says some gauge, positive everywhere, makes any two fine sums over `[u, w]` differ by at
 * most `e * (w - u)`. It glues, and that is where the one idea is. Two gauges good on `[u, v]` and
 * on `[v, w]` are combined into one that is at most `abs (x - v)` away from `v`; then a piece fine
 * for it that contains `v` has `v` as its tag, because any other tag is closer to `v` than the piece
 * is long, and such a piece splits at `v` into two pieces tagged `v` whose sums add up exactly. So a
 * fine sum over `[u, w]` is a sum over `[u, v]` plus one over `[v, w]`, with no error, which is what
 * comparing two divisions without a common refinement needs. Near a point `C` holds for a constant
 * gauge, by continuity at that point alone: every fine sum over a short interval around `x` is
 * within half the tolerance of `f x` times the length. `Continuity.INTERVAL_GLUING` does the rest,
 * and neither uniform continuity nor any sequence of gauges is used.
 *
 * == One supremum ==
 *
 * The integral is the least upper bound of `t - e * (b - a)` over every `e > 0`, every gauge good for
 * `e` on `[a, b]`, and every sum fine for it. Two such quantities are compared through a third sum,
 * fine for the pointwise minimum of the two gauges, which `FINE_SUM_EXISTS` supplies, so a sum fine
 * for a good gauge is within `e * (b - a)` of the supremum from both sides. `COMPLETENESS` is spent
 * there once; the tolerance is shared with `Continuity.portion`, so no quotient with a symbolic
 * denominator appears.
 *
 * Every step is written in direct style inside `Builder`, for the reason `Provability` gives.
 */
private[theories] object Integrability {

  /** `CONTINUOUS_HAS_INTEGRAL` and `CONTINUOUS_INTEGRAL`, by the names `Integral` publishes them under. */
  def prove(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    continuity: Continuity,
    gluing: Kernel.Thm,
    piece: Kernel.Thm,
    join: Kernel.Thm,
    induction: Kernel.Thm,
    exists: Kernel.Thm,
    gauge: Kernel.Thm,
    hasDefinition: Kernel.Thm,
    unique: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
    try {
      val builder = new Builder(steps, reals, magnitude, classical, continuity, gluing, piece, join, induction, exists, gauge,
        hasDefinition, unique)
      Right((builder.hasIntegral, builder.integralIsOne))
    } catch { case refused: RefusedHere => Left(refused.error) }

  private final class RefusedHere(val error: LogicError) extends RuntimeException(error.message)

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)

  /** The variables every text below uses, with their types, so a text is read at the types meant. */
  private val Types: Map[String, Type] =
    List("a", "b", "c", "d", "e", "i", "k", "m", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "s1", "s2",
      "t1", "t2", "e1", "e2", "y1").map(_ -> Reals).toMap ++
      List("f", "g", "g1", "g2", "h").map(_ -> Functions).toMap

  private val Written: Map[Type, String] = Map(Reals -> "real", Functions -> "real->real")

  private val Identifier = "(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])".r

  /** Every occurrence of a name in `Types` written with its type, except where it is being bound. */
  private def annotated(text: String): String =
    Identifier.replaceAllIn(text, found => {
      val name = found.group(1)
      val rest = text.substring(found.end).dropWhile(_ == ' ')
      Types.get(name).flatMap(Written.get) match {
        case Some(written) if !rest.startsWith(":") =>
          scala.util.matching.Regex.quoteReplacement(s"($name:$written)")
        case _ => scala.util.matching.Regex.quoteReplacement(name)
      }
    })

  /* ------------------------------------------------------------------------- the texts */

  /** Some gauge positive everywhere keeps any two fine sums over `[u, w]` within `e * (w - u)`. */
  private def good(g: String, u: String, w: String, e: String = "e"): String =
    s"((!x:real. 0 < $g x) /\\ (!s:real. !t:real. fine_sum f $g $u $w s ==> fine_sum f $g $u $w t ==> " +
      s"abs (s - t) <= $e * ($w - $u)))"

  private def cauchy(u: String, w: String, e: String = "e"): String = s"(?g:real -> real. ${good("g", u, w, e)})"

  private final class Builder(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    continuity: Continuity,
    gluing: Kernel.Thm,
    piece: Kernel.Thm,
    join: Kernel.Thm,
    induction: Kernel.Thm,
    exists: Kernel.Thm,
    gauge: Kernel.Thm,
    hasDefinition: Kernel.Thm,
    unique: Kernel.Thm
  ) {
    private val logic = steps.logic
    private val rules = logic.rules
    private val theory = steps.theory
    private val notation = steps.notation

    /* --------------------------------------------------------------- the moves */

    private def force[T](result: Either[LogicError, T]): T = result.fold(error => throw new RefusedHere(error), identity)
    private def refuse(what: String, term: Term): Nothing = throw new RefusedHere(NotOfForm(what, term))

    private def typed(term: Term, holes: Set[String]): Term = {
      Term.freeVariables(term).foreach { variable =>
        if (!holes.contains(variable.name) && !Types.get(variable.name).contains(variable.ty))
          refuse(s"the variable ${variable.name} at the type the derivation declares for it", variable)
      }
      term
    }

    private def prop(text: String): Term = typed(force(Parser.proposition(theory, notation, annotated(text))), Set.empty)
    private def term(text: String, ty: Type): Term = typed(force(Parser.term(theory, notation, annotated(text), ty)), Set.empty)
    private def real(text: String): Term = term(text, Reals)
    private def variable(name: String): FVar = Term.variable(name, Types.getOrElse(name, refuse("a declared variable", Term.variable(name, Reals))))
    private def assumeT(statement: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(statement)))
    private def assume(text: String): Kernel.Thm = assumeT(prop(text))

    private def reduced(theorem: Kernel.Thm): Kernel.Thm =
      force(Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

    /** Specialise the leading quantifiers at texts, each read at its binder's type, and reduce. */
    private def spec(theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
      reduced(arguments.foldLeft(theorem) { (current, text) =>
        val predicate = logic.destForallPredicate(current.conclusion).getOrElse(refuse("a universal", current.conclusion))
        val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
        force(rules.spec(term(text, domain), current))
      })

    private def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
      premises.foldLeft(implication)((current, premise) => force(rules.mp(current, premise)))
    private def conj(parts: Kernel.Thm*): Kernel.Thm = parts.reduceRight((a, b) => force(rules.conjIntro(a, b)))
    private def left(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim1(theorem))
    private def right(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim2(theorem))
    private def discharged(theorem: Kernel.Thm, texts: String*): Kernel.Thm =
      texts.reverse.foldLeft(theorem)((current, text) => force(rules.disch(prop(text), current)))
    private def generalised(theorem: Kernel.Thm, names: String*): Kernel.Thm =
      force(rules.genAll(theorem, names.toList.map(variable)))
    private def sym(equation: Kernel.Thm): Kernel.Thm = force(Conv.sym(equation))
    private def trans(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = force(Conv.trans(first, second))
    private def absurd(negation: Kernel.Thm, positive: Kernel.Thm): Kernel.Thm = force(rules.notElim(negation, positive))
    private def exFalso(statement: Term, falsity: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(statement, falsity))

    /** A closed arithmetic fact, specialised at texts and detached against premises. */
    private def arithmetic(fact: String, arguments: String*)(premises: Kernel.Thm*): Kernel.Thm =
      mp(spec(force(steps.lemma(fact)), arguments*), premises*)

    private def mag(name: String, arguments: String*): Kernel.Thm = spec(force(magnitude.fact(name)), arguments*)

    /** `|- T[b]` from `|- a = b` and `|- T[a]`, the hole in `template` written `zz`, a real. */
    private def transport(equation: Kernel.Thm, template: String, theorem: Kernel.Thm): Kernel.Thm = {
      val zz = Term.variable("zz", Reals)
      val body = typed(force(Parser.proposition(theory, notation, annotated(template).replace("zz", "(zz:real)"))), Set("zz"))
      val lambda = force(LogicError.lift(Term.abs(zz, body)))
      val across = force(Conv.apTerm(lambda, equation))
      val (from, to) = Term.destEq(across.conclusion).getOrElse(refuse("an equation", across.conclusion))
      val joined = trans(trans(sym(force(Conv.betaRoot(from))), across), force(Conv.betaRoot(to)))
      force(LogicError.lift(Kernel.eqMp(joined, theorem)))
    }

    private def cases(statement: Term)(positive: Kernel.Thm => Kernel.Thm, negative: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val denial = force(logic.mkNot(statement))
      force(classical.cases(statement, positive(assumeT(statement)), negative(assumeT(denial))))
    }

    private def byDisjunction(disjunction: Kernel.Thm)(first: Kernel.Thm => Kernel.Thm, second: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val (a, b) = logic.destDisj(disjunction.conclusion).getOrElse(refuse("a disjunction", disjunction.conclusion))
      force(rules.disjElim(disjunction, first(assumeT(a)), second(assumeT(b))))
    }

    /** By `p <= q` or `q <= p`, from the order's totality, which is an axiom and costs nothing classical. */
    private def byOrder(p: String, q: String)(below: Kernel.Thm => Kernel.Thm, above: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val trichotomy = spec(force(reals.axiom("LT_TOTAL")), p, q)
      byDisjunction(trichotomy)(
        strict => below(arithmetic("!p:real q:real. p < q ==> p <= q", p, q)(strict)),
        rest => byDisjunction(rest)(
          equal => below(arithmetic("!p:real q:real. p = q ==> p <= q", p, q)(equal)),
          reverse => above(arithmetic("!p:real q:real. q < p ==> q <= p", p, q)(reverse))
        )
      )
    }

    private def opened(existential: Kernel.Thm, name: String)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion).getOrElse(refuse("an existential", existential.conclusion))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
      val witness = Term.variable(name, domain)
      val applied = force(LogicError.lift(Term.app(predicate, witness)))
      val body = Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(refuse("an equation", applied))
      force(rules.existsElim(existential, witness, reach(assumeT(body))))
    }

    /** `|- ?x1 ... xn. body` from the body at the witnesses, each read at its binder's type. */
    private def witnessed(target: Term, witnesses: List[Type => Term], proof: Kernel.Thm): Kernel.Thm =
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
          force(rules.existsIntro(predicate, witness, witnessed(inner, rest, proof)))
      }

    private def at(texts: String*): List[Type => Term] = texts.toList.map(text => (ty: Type) => term(text, ty))

    /** `|- t <= c` and `|- -(t) <= c` from `|- abs (t) <= c`, or the same with `<`. */
    private def sides(t: String, c: String, bound: Kernel.Thm, strict: Boolean): (Kernel.Thm, Kernel.Thm) = {
      val op = if (strict) "<" else "<="
      val up = arithmetic(s"!m:real a:real c:real. a <= m ==> m $op c ==> a $op c", s"abs ($t)", t, c)(mag(Magnitude.AbsAbove, t), bound)
      val down = arithmetic(s"!m:real a:real c:real. -a <= m ==> m $op c ==> -a $op c", s"abs ($t)", t, c)(
        mag(Magnitude.AbsAboveNegation, t), bound)
      (up, down)
    }

    /** `|- abs (t) <= c` (or `<`) from both sides, by the two cases of `abs`. */
    private def joined(t: String, c: String, up: Kernel.Thm, down: Kernel.Thm, strict: Boolean): Kernel.Thm = {
      val op = if (strict) "<" else "<="
      val m = s"abs ($t)"
      byDisjunction(mag(Magnitude.AbsCases, t))(
        plain => arithmetic(s"!m:real a:real c:real. m = a ==> a $op c ==> m $op c", m, t, c)(plain, up),
        negated => arithmetic(s"!m:real a:real c:real. m = -a ==> -a $op c ==> m $op c", m, t, c)(negated, down)
      )
    }

    /** The induction over fine sums for gauge `g`, at the property `\u v s. body`, with its two premises and conclusion. */
    private def inducting(g: String, body: String): (Term, Term, Kernel.Thm) = {
      val property = term(s"\\u:real. \\v:real. \\s:real. $body", Type.fun(Reals, Type.fun(Reals, Type.fun(Reals, Type.Bool))))
      val instance = reduced(force(rules.specAll(induction, List(term("f", Functions), term(g, Functions), property))))
      val (base, rest) = logic.destImp(instance.conclusion).getOrElse(refuse("an implication", instance.conclusion))
      val (step, _) = logic.destImp(rest).getOrElse(refuse("an implication", rest))
      (base, step, instance)
    }

    private def checked(proof: Kernel.Thm, expected: Term, what: String): Kernel.Thm =
      if (proof.conclusion == expected) proof else refuse(what, proof.conclusion)

    /* ------------------------------------------------------------ fine sums are ordered */

    /** `|- fine_sum f g u v s ==> u <= v`. */
    private lazy val ordered: Kernel.Thm = {
      val (baseTerm, stepTerm, instance) = inducting("g", "u <= v")
      val base = {
        val condition = assume("u <= x /\\ x <= v /\\ v - u < g x")
        generalised(discharged(arithmetic("!u:real x:real v:real. u <= x ==> x <= v ==> u <= v", "u", "x", "v")(
          left(condition), left(right(condition))), "u <= x /\\ x <= v /\\ v - u < g x"), "u", "v", "x")
      }
      val step = generalised(discharged(
        arithmetic("!u:real v:real w:real. u <= v ==> v <= w ==> u <= w", "u", "v", "w")(assume("u <= v"), assume("v <= w")),
        "u <= v", "v <= w"), "u", "v", "w", "s", "t")
      val all = mp(instance, checked(base, baseTerm, "the base"), checked(step, stepTerm, "the step"))
      generalised(spec(all, "u", "v", "s"), "f", "g", "u", "v", "s")
    }

    /* ---------------------------------------------------------- splitting at a point */

    private val Splits = "!x:real. ~(x = c) ==> h x <= abs (x - c)"
    private def splitBody(u: String, v: String, s: String): String =
      s"fine_sum f h $u $v ($s) /\\ ($u <= c ==> c <= $v ==> " +
        s"(?s1:real. ?s2:real. fine_sum f h $u c s1 /\\ fine_sum f h c $v s2 /\\ ($s) = s1 + s2))"

    /**
     * `|- Splits ==> fine_sum f h u v s ==> u <= c ==> c <= v ==> ?s1 s2. <a sum over [u, c]> /\ <one over [c, v]> /\ s = s1 + s2`.
     *
     * A piece containing `c` is tagged `c`: any other tag is at least the piece's length from `c`,
     * and inside the piece it is at most that far. So it splits into two pieces tagged `c`.
     */
    private lazy val split: Kernel.Thm = {
      val splits = assume(Splits)
      val (baseTerm, stepTerm, instance) = inducting("h", splitBody("u", "v", "s"))
      val target = prop(s"?s1:real. ?s2:real. fine_sum f h u c s1 /\\ fine_sum f h c v s2 /\\ f x * (v - u) = s1 + s2")

      val base = {
        val conditionText = "u <= x /\\ x <= v /\\ v - u < h x"
        val condition = assume(conditionText)
        val ux = left(condition)
        val xv = left(right(condition))
        val short = right(right(condition))
        val whole = spec(piece, "f", "h", "u", "v", "x")
        val fine = mp(whole, condition)
        val halves = {
          val uc = assume("u <= c")
          val cv = assume("c <= v")
          val found = cases(prop("x = c"))(
            isC => {
              val shortAtC = transport(isC, "v - u < h zz", short)
              val first = mp(spec(piece, "f", "h", "u", "c", "c"), conj(uc,
                arithmetic("!c:real. c <= c", "c")(),
                arithmetic("!u:real c:real v:real H:real. c <= v ==> v - u < H ==> c - u < H", "u", "c", "v", "h c")(cv, shortAtC)))
              val second = mp(spec(piece, "f", "h", "c", "v", "c"), conj(
                arithmetic("!c:real. c <= c", "c")(), cv,
                arithmetic("!u:real c:real v:real H:real. u <= c ==> v - u < H ==> v - c < H", "u", "c", "v", "h c")(uc, shortAtC)))
              val sumAtC = arithmetic("!p:real u:real c:real v:real. p * (v - u) = p * (c - u) + p * (v - c)", "f c", "u", "c", "v")()
              val sum = transport(sym(isC), "f zz * (v - u) = f c * (c - u) + f c * (v - c)", sumAtC)
              witnessed(target, at("f c * (c - u)", "f c * (v - c)"), conj(first, second, sum))
            },
            other => {
              val far = mp(spec(splits, "x"), other)
              val (xc, cx) = (
                arithmetic("!x:real c:real u:real v:real. u <= c ==> x <= v ==> x - c <= v - u", "x", "c", "u", "v")(uc, xv),
                arithmetic("!x:real c:real u:real v:real. u <= x ==> c <= v ==> -(x - c) <= v - u", "x", "c", "u", "v")(ux, cv))
              val near = joined("x - c", "v - u", xc, cx, strict = false)
              val contradiction = arithmetic("!A:real B:real H:real. A < H ==> H <= B ==> B <= A ==> F", "v - u", "abs (x - c)", "h x")(
                short, far, near)
              exFalso(target, contradiction)
            }
          )
          discharged(found, "u <= c", "c <= v")
        }
        val proof = checked(conj(fine, halves), prop(splitBody("u", "v", "f x * (v - u)")), "the split of a piece")
        generalised(discharged(proof, conditionText), "u", "v", "x")
      }

      val step = {
        val first = assume(splitBody("u", "v", "s"))
        val second = assume(splitBody("v", "w", "t"))
        val fine = mp(spec(join, "f", "h", "u", "v", "w", "s", "t"), left(first), left(second))
        val goal = prop(s"?s1:real. ?s2:real. fine_sum f h u c s1 /\\ fine_sum f h c w s2 /\\ s + t = s1 + s2")
        val halves = {
          val uc = assume("u <= c")
          val cw = assume("c <= w")
          val found = byOrder("c", "v")(
            cv => opened(mp(right(first), uc, cv), "s1") { afterFirst =>
              opened(afterFirst, "s2") { parts =>
                val rest = mp(spec(join, "f", "h", "c", "v", "w", "s2", "t"), left(right(parts)), left(second))
                val sum = arithmetic("!s:real t:real p:real q:real. s = p + q ==> s + t = p + (q + t)", "s", "t", "s1", "s2")(right(right(parts)))
                witnessed(goal, at("s1", "s2 + t"), conj(left(parts), rest, sum))
              }
            },
            vc => opened(mp(right(second), vc, cw), "s1") { afterFirst =>
              opened(afterFirst, "s2") { parts =>
                val before = mp(spec(join, "f", "h", "u", "v", "c", "s", "s1"), left(first), left(parts))
                val sum = arithmetic("!s:real t:real p:real q:real. t = p + q ==> s + t = (s + p) + q", "s", "t", "s1", "s2")(right(right(parts)))
                witnessed(goal, at("s + s1", "s2"), conj(before, left(right(parts)), sum))
              }
            }
          )
          discharged(found, "u <= c", "c <= w")
        }
        val proof = checked(conj(fine, halves), prop(splitBody("u", "w", "s + t")), "the split of a join")
        generalised(discharged(proof, splitBody("u", "v", "s"), splitBody("v", "w", "t")), "u", "v", "w", "s", "t")
      }

      val all = mp(instance, checked(base, baseTerm, "the base"), checked(step, stepTerm, "the step"))
      val atSum = spec(all, "u", "v", "s")
      val fineSum = assume("fine_sum f h u v s")
      val result = mp(right(mp(atSum, fineSum)), assume("u <= c"), assume("c <= v"))
      generalised(discharged(result, Splits, "fine_sum f h u v s", "u <= c", "c <= v"), "f", "h", "c", "u", "v", "s")
    }

    /* ------------------------------------------------------ near a point, one value */

    private def nearBody(u: String, v: String, s: String): String =
      s"$u <= $v /\\ (m <= $u ==> $v <= r ==> abs ($s - f x * ($v - $u)) <= k * ($v - $u))"

    private val Close = "!y:real. abs (y - x) < d ==> abs (f y - f x) < k"

    /**
     * `|- Close ==> m <= x ==> x <= r ==> r - m < d ==> fine_sum f (\y. d) m r s ==> abs (s - f x * (r - m)) <= k * (r - m)`.
     *
     * Every tag of a division of a short interval around `x` is within `d` of it, so every piece's
     * value is within `k` of `f x` per unit of length, and the pieces add. The interval is `[m, r]`
     * because the induction binds `u`, `v` and `w` for the piece.
     */
    private lazy val nearOnePoint: Kernel.Thm = {
      val hypotheses = List(Close, "m <= x", "x <= r", "r - m < d")
      val close = assume(Close)
      val mx = assume("m <= x")
      val xr = assume("x <= r")
      val shortInterval = assume("r - m < d")
      val (baseTerm, stepTerm, instance) = inducting("\\y:real. d", nearBody("u", "v", "s"))

      val base = {
        val conditionText = "u <= y /\\ y <= v /\\ v - u < d"
        val condition = assume(conditionText)
        val uy = left(condition)
        val yv = left(right(condition))
        val order = arithmetic("!u:real y:real v:real. u <= y ==> y <= v ==> u <= v", "u", "y", "v")(uy, yv)
        val bounded = {
          val mu = assume("m <= u")
          val vr = assume("v <= r")
          val up = arithmetic("!y:real x:real v:real r:real m:real d:real. y <= v ==> v <= r ==> m <= x ==> r - m < d ==> y - x < d",
            "y", "x", "v", "r", "m", "d")(yv, vr, mx, shortInterval)
          val down = arithmetic("!y:real x:real u:real r:real m:real d:real. m <= u ==> u <= y ==> x <= r ==> r - m < d ==> -(y - x) < d",
            "y", "x", "u", "r", "m", "d")(mu, uy, xr, shortInterval)
          val near = joined("y - x", "d", up, down, strict = true)
          val value = mp(spec(close, "y"), near)
          val (valueUp, valueDown) = sides("f y - f x", "k", value, strict = true)
          val length = arithmetic("!u:real v:real. u <= v ==> 0 <= v - u", "u", "v")(order)
          val scaledUp = arithmetic("!A:real B:real K:real D:real. A - B < K ==> 0 <= D ==> A * D - B * D <= K * D",
            "f y", "f x", "k", "v - u")(valueUp, length)
          val scaledDown = arithmetic("!A:real B:real K:real D:real. -(A - B) < K ==> 0 <= D ==> -(A * D - B * D) <= K * D",
            "f y", "f x", "k", "v - u")(valueDown, length)
          discharged(joined("f y * (v - u) - f x * (v - u)", "k * (v - u)", scaledUp, scaledDown, strict = false), "m <= u", "v <= r")
        }
        val proof = checked(conj(order, bounded), prop(nearBody("u", "v", "f y * (v - u)")), "the value of a piece")
        generalised(discharged(proof, conditionText), "u", "v", "y")
      }

      val step = {
        val first = assume(nearBody("u", "v", "s"))
        val second = assume(nearBody("v", "w", "t"))
        val order = arithmetic("!u:real v:real w:real. u <= v ==> v <= w ==> u <= w", "u", "v", "w")(left(first), left(second))
        val bounded = {
          val mu = assume("m <= u")
          val wr = assume("w <= r")
          val vr = arithmetic("!v:real w:real r:real. v <= w ==> w <= r ==> v <= r", "v", "w", "r")(left(second), wr)
          val mv = arithmetic("!m:real u:real v:real. m <= u ==> u <= v ==> m <= v", "m", "u", "v")(mu, left(first))
          val one = mp(right(first), mu, vr)
          val two = mp(right(second), mv, wr)
          val (oneUp, oneDown) = sides("s - f x * (v - u)", "k * (v - u)", one, strict = false)
          val (twoUp, twoDown) = sides("t - f x * (w - v)", "k * (w - v)", two, strict = false)
          val up = arithmetic(
            "!s:real t:real Q:real u:real v:real w:real k:real. s - Q * (v - u) <= k * (v - u) ==> t - Q * (w - v) <= k * (w - v) ==> " +
              "(s + t) - Q * (w - u) <= k * (w - u)", "s", "t", "f x", "u", "v", "w", "k")(oneUp, twoUp)
          val down = arithmetic(
            "!s:real t:real Q:real u:real v:real w:real k:real. -(s - Q * (v - u)) <= k * (v - u) ==> -(t - Q * (w - v)) <= k * (w - v) ==> " +
              "-((s + t) - Q * (w - u)) <= k * (w - u)", "s", "t", "f x", "u", "v", "w", "k")(oneDown, twoDown)
          discharged(joined("(s + t) - f x * (w - u)", "k * (w - u)", up, down, strict = false), "m <= u", "w <= r")
        }
        val proof = checked(conj(order, bounded), prop(nearBody("u", "w", "s + t")), "the value of a join")
        generalised(discharged(proof, nearBody("u", "v", "s"), nearBody("v", "w", "t")), "u", "v", "w", "s", "t")
      }

      val all = mp(instance, checked(base, baseTerm, "the base"), checked(step, stepTerm, "the step"))
      val atInterval = mp(spec(all, "m", "r", "s"), assume("fine_sum f (\\y:real. d) m r s"))
      val result = mp(right(atInterval), arithmetic("!m:real. m <= m", "m")(), arithmetic("!r:real. r <= r", "r")())
      generalised(discharged(result, (hypotheses :+ "fine_sum f (\\y:real. d) m r s")*), "f", "x", "d", "k", "m", "r", "s")
    }

    /* ------------------------------------------------------- the criterion glues */

    private def condAt(ty: Type, name: String): Kernel.Thm =
      Kernel.instType(Map(Classical.TypeVariable -> ty), force(classical.fact(name)))

    /** `COND c y z = y` from `|- c`, or `= z` from `|- ~c`, at `real`. */
    private def whenHolds(guard: Kernel.Thm, y: String, z: String): Kernel.Thm =
      mp(force(rules.specAll(condAt(Reals, Classical.CondTrue), List(guard.conclusion, real(y), real(z)))), guard)
    private def whenFails(guard: Kernel.Thm, y: String, z: String): Kernel.Thm = {
      val statement = logic.destNot(guard.conclusion).getOrElse(refuse("a negation", guard.conclusion))
      mp(force(rules.specAll(condAt(Reals, Classical.CondFalse), List(statement, real(y), real(z)))), guard)
    }

    private val JointAt = (x: String) => s"COND ($x = v) (min (g1 v) (g2 v)) (min (min (g1 $x) (g2 $x)) (abs ($x - v)))"

    /**
     * `|- u <= v /\ v <= w /\ C u v /\ C v w ==> C u w`, the gauge being `JointAt`, at most `abs (x - v)` away from `v`.
     */
    private lazy val glued: Kernel.Thm = {
      val premiseText = s"u <= v /\\ v <= w /\\ ${cauchy("u", "v")} /\\ ${cauchy("v", "w")}"
      val premise = assume(premiseText)
      val uv = left(premise)
      val vw = left(right(premise))
      val result = opened(left(right(right(premise))), "g1") { first =>
        opened(right(right(right(premise))), "g2") { second =>
          val g1Positive = left(first)
          val g2Positive = left(second)

          val positive = {
            val value = JointAt("x")
            val found = cases(prop("x = v"))(
              isV => {
                val least = force(Continuity.minimumOf(steps, magnitude, annotated("g1 v"), annotated("g2 v"), spec(g1Positive, "v"), spec(g2Positive, "v")))
                transport(sym(whenHolds(isV, "min (g1 v) (g2 v)", "min (min (g1 x) (g2 x)) (abs (x - v))")), "0 < zz", least)
              },
              other => {
                val both = force(Continuity.minimumOf(steps, magnitude, annotated("g1 x"), annotated("g2 x"), spec(g1Positive, "x"), spec(g2Positive, "x")))
                val apart = byDisjunction(spec(force(reals.axiom("LT_TOTAL")), "x", "v"))(
                  below => arithmetic("!m:real a:real. -a <= m ==> a < 0 ==> 0 < m", "abs (x - v)", "x - v")(
                    mag(Magnitude.AbsAboveNegation, "x - v"), arithmetic("!x:real v:real. x < v ==> x - v < 0", "x", "v")(below)),
                  rest => byDisjunction(rest)(
                    equal => exFalso(prop("0 < abs (x - v)"), absurd(other, equal)),
                    above => arithmetic("!m:real a:real. a <= m ==> 0 < a ==> 0 < m", "abs (x - v)", "x - v")(
                      mag(Magnitude.AbsAbove, "x - v"), arithmetic("!x:real v:real. v < x ==> 0 < x - v", "x", "v")(above))
                  )
                )
                val least = force(Continuity.minimumOf(steps, magnitude, annotated("min (g1 x) (g2 x)"), annotated("abs (x - v)"), both, apart))
                transport(sym(whenFails(other, "min (g1 v) (g2 v)", "min (min (g1 x) (g2 x)) (abs (x - v))")), "0 < zz", least)
              }
            )
            generalised(found, "x")
          }

          def under(g: String, first: Boolean): Kernel.Thm = {
            val (minAtV, minAtX) =
              if (first) (Magnitude.MinBelowLeft, Magnitude.MinBelowLeft) else (Magnitude.MinBelowRight, Magnitude.MinBelowRight)
            val found = cases(prop("x = v"))(
              isV => {
                val atV = mag(minAtV, "g1 v", "g2 v")
                val same = force(Conv.apTerm(term(g, Functions), sym(isV)))
                val toX = transport(same, s"min (g1 v) (g2 v) <= zz", atV)
                transport(sym(whenHolds(isV, "min (g1 v) (g2 v)", "min (min (g1 x) (g2 x)) (abs (x - v))")), s"zz <= $g x", toX)
              },
              other => {
                val outer = mag(Magnitude.MinBelowLeft, "min (g1 x) (g2 x)", "abs (x - v)")
                val inner = mag(minAtX, "g1 x", "g2 x")
                val chained = arithmetic("!p:real q:real r:real. p <= q ==> q <= r ==> p <= r",
                  "min (min (g1 x) (g2 x)) (abs (x - v))", "min (g1 x) (g2 x)", s"$g x")(outer, inner)
                transport(sym(whenFails(other, "min (g1 v) (g2 v)", "min (min (g1 x) (g2 x)) (abs (x - v))")), s"zz <= $g x", chained)
              }
            )
            generalised(found, "x")
          }
          val underFirst = under("g1", first = true)
          val underSecond = under("g2", first = false)
          val splits = {
            val other = assume("~(x = v)")
            val value = whenFails(other, "min (g1 v) (g2 v)", "min (min (g1 x) (g2 x)) (abs (x - v))")
            val bound = mag(Magnitude.MinBelowRight, "min (g1 x) (g2 x)", "abs (x - v)")
            generalised(discharged(transport(sym(value), "zz <= abs (x - v)", bound), "~(x = v)"), "x")
          }

          val joint = s"\\x:real. ${JointAt("x")}"
          val sFine = assume(s"fine_sum f ($joint) u w s")
          val tFine = assume(s"fine_sum f ($joint) u w t")
          val splitAt = (sum: String, fine: Kernel.Thm) =>
            mp(spec(split, "f", joint, "v", "u", "w", sum), splits, fine, uv, vw)
          val close = opened(splitAt("s", sFine), "s1") { sAfter =>
            opened(sAfter, "s2") { sParts =>
              opened(splitAt("t", tFine), "t1") { tAfter =>
                opened(tAfter, "t2") { tParts =>
                  def narrowed(g: String, below: Kernel.Thm, lo: String, hi: String, sum: String, fine: Kernel.Thm): Kernel.Thm =
                    mp(spec(gauge, "f", joint, g, lo, hi, sum), below, fine)
                  val firstClose = mp(spec(right(first), "s1", "t1"),
                    narrowed("g1", underFirst, "u", "v", "s1", left(sParts)), narrowed("g1", underFirst, "u", "v", "t1", left(tParts)))
                  val secondClose = mp(spec(right(second), "s2", "t2"),
                    narrowed("g2", underSecond, "v", "w", "s2", left(right(sParts))), narrowed("g2", underSecond, "v", "w", "t2", left(right(tParts))))
                  val (aUp, aDown) = sides("s1 - t1", "e * (v - u)", firstClose, strict = false)
                  val (bUp, bDown) = sides("s2 - t2", "e * (w - v)", secondClose, strict = false)
                  val lemmaUp = "!s:real t:real p:real q:real y:real z:real e:real u:real v:real w:real. s = p + q ==> t = y + z ==> " +
                    "p - y <= e * (v - u) ==> q - z <= e * (w - v) ==> s - t <= e * (w - u)"
                  val lemmaDown = "!s:real t:real p:real q:real y:real z:real e:real u:real v:real w:real. s = p + q ==> t = y + z ==> " +
                    "-(p - y) <= e * (v - u) ==> -(q - z) <= e * (w - v) ==> -(s - t) <= e * (w - u)"
                  val args = List("s", "t", "s1", "s2", "t1", "t2", "e", "u", "v", "w")
                  val up = arithmetic(lemmaUp, args*)(right(right(sParts)), right(right(tParts)), aUp, bUp)
                  val down = arithmetic(lemmaDown, args*)(right(right(sParts)), right(right(tParts)), aDown, bDown)
                  joined("s - t", "e * (w - u)", up, down, strict = false)
                }
              }
            }
          }
          val everyPair = generalised(discharged(close, s"fine_sum f ($joint) u w s", s"fine_sum f ($joint) u w t"), "s", "t")
          witnessed(prop(cauchy("u", "w")), List((ty: Type) => term(joint, ty)), conj(positive, everyPair))
        }
      }
      generalised(discharged(result, premiseText), "u", "v", "w")
    }

    /* ------------------------------------------------------ the criterion near a point */

    /** `|- 0 < e ==> <every x in [a, b] continuous> ==> <the local premise of the gluing at C>`. */
    private def local(localTerm: Term): Kernel.Thm = {
      val positive = assume("0 < e")
      val everywhere = assume(Everywhere)
      val pointText = "a <= x /\\ x <= b"
      val point = assume(pointText)
      val continuous = mp(spec(everywhere, "x"), point)
      val definition = force(continuity.definition(Continuity.Continuous))
      val unfolded = reduced(force(LogicError.lift(Kernel.eqMp(
        force(Conv.unfold(definition, List(term("f", Functions), real("x")))), continuous))))
      val half = arithmetic("!e:real. 0 < e ==> 0 < e / 2", "e")(positive)
      val near = mp(spec(unfolded, "e / 2"), half)
      val (_, afterPoint) = logic.destImp(force(Logic.stripForall(localTerm))._2).getOrElse(refuse("an implication", localTerm))
      val result = opened(near, "d") { radius =>
        val dPositive = left(radius)
        val close = right(radius)
        val intervalText = "a <= u /\\ u <= x /\\ x <= w /\\ w <= b /\\ w - u < d"
        val interval = assume(intervalText)
        val ux = left(right(interval))
        val xw = left(right(right(interval)))
        val short = right(right(right(right(interval))))
        val constant = "\\y:real. d"
        val sFine = assume(s"fine_sum f ($constant) u w s")
        val tFine = assume(s"fine_sum f ($constant) u w t")
        def value(sum: String, fine: Kernel.Thm): Kernel.Thm =
          mp(spec(nearOnePoint, "f", "x", "d", "e / 2", "u", "w", sum), close, ux, xw, short, fine)
        val (sUp, _) = sides("s - f x * (w - u)", "e / 2 * (w - u)", value("s", sFine), strict = false)
        val (_, sDown) = sides("s - f x * (w - u)", "e / 2 * (w - u)", value("s", sFine), strict = false)
        val (tUp, tDown) = sides("t - f x * (w - u)", "e / 2 * (w - u)", value("t", tFine), strict = false)
        val up = arithmetic("!s:real t:real Q:real E:real L:real. s - Q <= E / 2 * L ==> -(t - Q) <= E / 2 * L ==> s - t <= E * L",
          "s", "t", "f x * (w - u)", "e", "w - u")(sUp, tDown)
        val down = arithmetic("!s:real t:real Q:real E:real L:real. -(s - Q) <= E / 2 * L ==> t - Q <= E / 2 * L ==> -(s - t) <= E * L",
          "s", "t", "f x * (w - u)", "e", "w - u")(sDown, tUp)
        val pair = joined("s - t", "e * (w - u)", up, down, strict = false)
        val everyPair = generalised(discharged(pair, s"fine_sum f ($constant) u w s", s"fine_sum f ($constant) u w t"), "s", "t")
        val gaugePositive = generalised(dPositive, "y1")
        val criterion = witnessed(prop(cauchy("u", "w")), List((ty: Type) => term(constant, ty)), conj(gaugePositive, everyPair))
        val everyInterval = generalised(discharged(criterion, intervalText), "u", "w")
        witnessed(afterPoint, at("d"), conj(dPositive, everyInterval))
      }
      generalised(discharged(result, pointText), "x")
    }

    private val Everywhere = "!x:real. a <= x /\\ x <= b ==> continuous f x"

    /** `|- 0 < e ==> a <= b ==> Everywhere ==> C a b`. */
    private lazy val criterion: Kernel.Thm = {
      val relation = term(s"\\u:real. \\w:real. ${cauchy("u", "w")}", Type.fun(Reals, Type.fun(Reals, Type.Bool)))
      val instance = reduced(force(rules.specAll(gluing, List(relation, real("a"), real("b")))))
      val (orderedTerm, rest) = logic.destImp(instance.conclusion).getOrElse(refuse("an implication", instance.conclusion))
      val (glueTerm, rest2) = logic.destImp(rest).getOrElse(refuse("an implication", rest))
      val (localTerm, _) = logic.destImp(rest2).getOrElse(refuse("an implication", rest2))
      val result = mp(instance, assumeT(orderedTerm), checked(glued, glueTerm, "the gluing premise"),
        checked(local(localTerm), localTerm, "the local premise"))
      generalised(discharged(result, "0 < e", "a <= b", Everywhere), "e")
    }

    /* ----------------------------------------------------------------- one supremum */

    private def member(y: String): String =
      s"(?e2:real. ?g2:real -> real. ?t2:real. 0 < e2 /\\ ${good("g2", "a", "b", "e2")} /\\ fine_sum f g2 a b t2 /\\ " +
        s"$y = t2 - e2 * (b - a))"

    /**
     * `|- a <= b ==> good e g ==> fine_sum f g a b t ==> good e1 g1 ==> fine_sum f g1 a b t1 ==> t1 - e1 * (b - a) <= t + e * (b - a)`:
     * two sums of two good gauges, compared through a third fine for the smaller gauge.
     */
    private lazy val compared: Kernel.Thm = {
      val texts = List("a <= b", good("g", "a", "b"), "fine_sum f g a b t", good("g1", "a", "b", "e1"), "fine_sum f g1 a b t1")
      val ordered = assume(texts(0))
      val first = assume(texts(1))
      val tFine = assume(texts(2))
      val second = assume(texts(3))
      val t1Fine = assume(texts(4))
      val smaller = "\\x:real. min (g x) (g1 x)"
      val positive = {
        val least = force(Continuity.minimumOf(steps, magnitude, annotated("g x"), annotated("g1 x"), spec(left(first), "x"), spec(left(second), "x")))
        generalised(discharged(least, "a <= x /\\ x <= b"), "x")
      }
      val cousin = mp(spec(exists, "f", smaller, "a", "b"), ordered, positive)
      val result = opened(cousin, "r") { rFine =>
        val forG = mp(spec(gauge, "f", smaller, "g", "a", "b", "r"), generalised(mag(Magnitude.MinBelowLeft, "g x", "g1 x"), "x"), rFine)
        val forG1 = mp(spec(gauge, "f", smaller, "g1", "a", "b", "r"), generalised(mag(Magnitude.MinBelowRight, "g x", "g1 x"), "x"), rFine)
        val near = mp(spec(right(first), "t", "r"), tFine, forG)
        val near1 = mp(spec(right(second), "t1", "r"), t1Fine, forG1)
        val (_, down) = sides("t - r", "e * (b - a)", near, strict = false)
        val (up1, _) = sides("t1 - r", "e1 * (b - a)", near1, strict = false)
        arithmetic("!t:real r:real t1:real E:real E1:real. -(t - r) <= E ==> t1 - r <= E1 ==> t1 - E1 <= t + E",
          "t", "r", "t1", "e * (b - a)", "e1 * (b - a)")(down, up1)
      }
      generalised(discharged(result, texts*), "e", "g", "t", "e1", "g1", "t1")
    }

    /** `Integral`'s `CONTINUOUS_HAS_INTEGRAL`. */
    lazy val hasIntegral: Kernel.Thm = {
      val ordered = assume("a <= b")
      val everywhere = assume(Everywhere)
      def criterionAt(tolerance: String, positive: Kernel.Thm): Kernel.Thm = mp(spec(criterion, tolerance), positive, ordered, everywhere)
      val setText = s"\\y:real. ${member("y")}"
      val completeness = spec(force(reals.axiom("COMPLETENESS")), setText)

      // Something is in the set: at tolerance one, a good gauge and a sum fine for it.
      val one = arithmetic("0 < (1:real)")()
      val result = opened(criterionAt("1", one), "g") { goodOne =>
        val positiveOnInterval = generalised(discharged(spec(left(goodOne), "x"), "a <= x /\\ x <= b"), "x")
        opened(mp(spec(exists, "f", "g", "a", "b"), ordered, positiveOnInterval), "t") { tFine =>
          val (someTerm, _) = logic.destImp(completeness.conclusion).getOrElse(refuse("an implication", completeness.conclusion))
          val (nonEmptyTerm, boundedTerm) = logic.destConj(someTerm).getOrElse(refuse("a conjunction", someTerm))
          val inSet = witnessed(prop(member("t - 1 * (b - a)")), at("1", "g", "t"),
            conj(one, goodOne, tFine, arithmetic("!p:real. p = p", "t - 1 * (b - a)")()))
          val nonEmpty = witnessed(nonEmptyTerm, at("t - 1 * (b - a)"), inSet)

          /** `|- !y. <y in the set> ==> y <= s + e * (b - a)`, for a sum `s` fine for a gauge `h` good at `e`. */
          def upperBound(s: String, h: String, e: String, goodH: Kernel.Thm, sFine: Kernel.Thm): Kernel.Thm = {
            val inside = assume(member("y"))
            val found = opened(inside, "e1") { afterE =>
              opened(afterE, "g1") { afterG =>
                opened(afterG, "t1") { parts =>
                  val renamed = s"(!x:real. 0 < g1 x) /\\ (!s:real. !t:real. fine_sum f g1 a b s ==> fine_sum f g1 a b t ==> abs (s - t) <= e1 * (b - a))"
                  val goodG1 = checked(left(right(parts)), prop(renamed), "the member's gauge")
                  val below = mp(spec(compared, e, h, s, "e1", "g1", "t1"), ordered, goodH, sFine, goodG1, left(right(right(parts))))
                  transport(sym(right(right(right(parts)))), s"zz <= $s + $e * (b - a)", below)
                }
              }
            }
            generalised(discharged(found, member("y")), "y")
          }
          val bounded = witnessed(boundedTerm, at("t + 1 * (b - a)"), upperBound("t", "g", "1", goodOne, tFine))
          val supremum = mp(completeness, conj(nonEmpty, bounded))

          opened(supremum, "i") { least =>
            val isUpper = left(least)
            val isLeast = right(least)
            val hasTerm = prop("has_integral f a b i")
            val equation = force(Conv.unfold(hasDefinition, List(term("f", Functions), real("a"), real("b"), real("i"))))
            val (_, body) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
            val normal = force(Conv.betaNormalise(body))
            val (_, target) = Term.destEq(normal.conclusion).getOrElse(refuse("an equation", body))

            val ePositive = assume("0 < e")
            val length = arithmetic("!a:real b:real. a <= b ==> 0 <= b - a", "a", "b")(ordered)
            val share = force(Continuity.portion(steps, reals, annotated("b - a"), length, 2, ePositive))
            val tolerance = share.term
            val withGauge = opened(criterionAt(tolerance, share.positive), "h") { goodH =>
              val sFine = assume("fine_sum f h a b s")
              val low = mp(spec(isUpper, s"s - $tolerance * (b - a)"),
                witnessed(prop(member(s"s - $tolerance * (b - a)")), at(tolerance, "h", "s"),
                  conj(share.positive, checked(goodH, prop(good("h", "a", "b", tolerance)), "the gauge at the share"), sFine,
                    arithmetic("!p:real. p = p", s"s - $tolerance * (b - a)")())))
              val high = mp(spec(isLeast, s"s + $tolerance * (b - a)"), upperBound("s", "h", tolerance, goodH, sFine))
              val small = arithmetic("!P:real T:real e:real. 0 <= P ==> 0 < T ==> 2 * (P + 1) * T = e ==> T * P < e",
                "b - a", tolerance, "e")(length, share.positive, share.equation)
              val up = arithmetic("!s:real i:real T:real e:real. i <= s + T ==> T < e ==> -(s - i) < e",
                "s", "i", s"$tolerance * (b - a)", "e")(high, small)
              val down = arithmetic("!s:real i:real T:real e:real. s - T <= i ==> T < e ==> s - i < e",
                "s", "i", s"$tolerance * (b - a)", "e")(low, small)
              val within = generalised(discharged(joined("s - i", "e", down, up, strict = true), "fine_sum f h a b s"), "s")
              val gaugePositive = left(goodH)
              witnessed(prop("?g:real -> real. (!x:real. 0 < g x) /\\ (!s:real. fine_sum f g a b s ==> abs (s - i) < e)"),
                at("h"), conj(gaugePositive, within))
            }
            val statement = checked(generalised(discharged(withGauge, "0 < e"), "e"), target, "the integral's statement")
            val has = force(LogicError.lift(Kernel.eqMp(sym(trans(equation, normal)), statement)))
            witnessed(prop("?i:real. has_integral f a b i"), at("i"), checked(has, hasTerm, "has_integral"))
          }
        }
      }
      generalised(discharged(result, "a <= b", Everywhere), "f", "a", "b")
    }

    /** `Integral`'s `CONTINUOUS_INTEGRAL`: the integral is one, so `integral` names it. */
    lazy val integralIsOne: Kernel.Thm = {
      val existing = mp(spec(hasIntegral, "f", "a", "b"), assume("a <= b"), assume(Everywhere))
      val result = opened(existing, "i") { has =>
        val equal = mp(spec(unique, "f", "a", "b", "i"), assume("a <= b"), has)
        transport(sym(equal), "has_integral f a b zz", has)
      }
      generalised(discharged(result, "a <= b", Everywhere), "f", "a", "b")
    }
  }
}
