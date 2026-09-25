package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * Matching a pattern against a term.
 *
 * Two groups. A pattern variable under a binder must not bind to something the binder owns: the
 * substitution would carry an index out of the lambda that gives it meaning, and the term that came
 * back would have no type. Everything above that is the ordinary behaviour making the rest usable.
 *
 * The second group is the Miller fragment, added 2026-09-11, and every case in it is a **boundary**
 * rather than an example: applied to a bound variable it answers, applied to anything else it
 * refuses, and the refusals are what keep the answer unique. A matcher that guessed among several
 * answers would be worse than one that stops, which is the rule this repository states for tactics
 * and holds here for the same reason.
 */
class MatchingSpec extends AnyFlatSpec with Matchers {


  /**
   * Abstraction, forced.
   *
   * `Term.abs` refuses a body that is not locally closed, since 2026-09-10, so it returns a
   * refusal like `app` and `eq` do. Every body below is built out of variables and constants a
   * line or two above and none of them can be open, so forcing here is reading the signature and
   * not ignoring it. A test that meant to hand it an open body says so by calling `Term.abs`
   * directly and looking at the `Left`.
   */
  private def lam(variable: FVar, body: Term): Term =
    Term.abs(variable, body).fold(error => fail(s"unexpected refusal: $error"), identity)

  private val alpha = TyVar("A")
  private val fn = Type.fun(alpha, alpha)

  private val p = Term.variable("p", alpha)
  private val q = Term.variable("q", alpha)
  private val r = Term.variable("r", alpha)
  private val f = Term.variable("f", fn)
  private val g = Term.variable("g", fn)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  /**
   * What a match decided, as a pair, so that a case deciding no type reads as the map it always was.
   *
   * `Matching.matchTerm` answers with a term substitution and a type substitution since 2026-09-12.
   * Both halves are asserted at every case below rather than the first alone: an empty type
   * substitution is the claim that the pattern's types were the target's already, and it is a claim
   * worth making where it is true.
   */
  private def answer(
    variables: Set[FVar],
    pattern: Term,
    target: Term
  ): Option[(Map[FVar, Term], Map[String, Type])] =
    Matching.matchTerm(variables, pattern, target).map(found => (found.terms, found.types))

  /**
   * The pattern with the answer substituted in, reduced, which is what the answer claims to be.
   *
   * The types first and the terms after, in that order, because the term substitution's keys carry
   * the pattern's own types: substituting the terms into a pattern whose types have moved would
   * find none of them.
   */
  private def filled(answer: Matching.Instantiation, pattern: Term): Term =
    normal(
      force(
        Term.substitute(
          answer.terms.map { case (variable, value) => answer.at(variable) -> value },
          Term.substituteTypes(answer.types, pattern)
        )
      )
    )

  private def normal(term: Term): Term = {
    val theorem = force(Conv.betaNormalise(term))
    Term.destEq(theorem.conclusion).map(_._2).getOrElse(fail(s"not an equation: $theorem"))
  }

  "A pattern variable" should "bind to whatever it is matched against" in {
    answer(Set(p), p, q) shouldBe Some((Map(p -> q), Map.empty))
  }

  it should "not bind to a term of another type" in {
    // The pattern variable is at `bool` here and was at `A` until 2026-09-12, when the matcher
    // started solving for type variables as well: `p:A` against a boolean is no longer a type
    // disagreement, it is `A := bool`, which the case below pins as the answer it now is. What is
    // being asserted here is the case that stayed a refusal, which is a **ground** type meeting a
    // different one.
    answer(Set(Term.variable("p", Type.Bool)), Term.variable("p", Type.Bool), q) shouldBe None
  }

  it should "bind at any type when its own type is a variable, and say which" in {
    val boolean = Term.variable("b", Type.Bool)

    answer(Set(p), p, boolean) shouldBe Some((Map(p -> boolean), Map("A" -> Type.Bool)))
  }

  it should "solve a type variable one way over the whole pattern" in {
    // `(p = q) /\ (r = s)` with all four at `A`, against a conjunction whose first equation is
    // between booleans and whose second is between predicates on booleans. The first conjunct reads
    // `A := bool` and the second needs `A := bool -> bool`. A matcher solving each occurrence on its
    // own would answer, and no single substitution would turn the pattern into the target.
    val logic = Logic.standard
    val predicate = Type.fun(Type.Bool, Type.Bool)
    val s = Term.variable("s", alpha)

    def equation(ty: Type, left: Term, right: Term): Term =
      force(Term.appAll(Term.equalityAt(ty), List(left, right)))

    val pattern = force(logic.mkConj(equation(alpha, p, q), equation(alpha, r, s)))
    val target = force(
      logic.mkConj(
        equation(Type.Bool, Term.variable("u", Type.Bool), Term.variable("v", Type.Bool)),
        equation(predicate, Term.variable("h", predicate), Term.variable("k", predicate))
      )
    )

    answer(Set(p, q, r, s), pattern, target) shouldBe None
  }

  it should "bind to the same term at every occurrence or not at all" in {
    val pattern = force(Term.app(force(Term.app(Term.variable("h", Type.fun(alpha, fn)), p)), p))
    val matching = force(Term.app(force(Term.app(Term.variable("h", Type.fun(alpha, fn)), q)), q))
    val differing = force(Term.app(force(Term.app(Term.variable("h", Type.fun(alpha, fn)), q)), r))

    answer(Set(p), pattern, matching) shouldBe Some((Map(p -> q), Map.empty))
    answer(Set(p), pattern, differing) shouldBe None
  }

  "A variable that is not a pattern variable" should "match only itself" in {
    val pattern = force(Term.app(f, p))

    answer(Set(p), pattern, force(Term.app(f, q))) shouldBe Some((Map(p -> q), Map.empty))
    answer(Set(p), pattern, force(Term.app(g, q))) shouldBe None
  }

  "A constant" should "match only the same constant at the same type" in {
    val logic = Logic.standard
    val truth = logic.truth
    val falsity = logic.falsity

    answer(Set.empty, truth, truth) shouldBe Some((Map.empty, Map.empty))
    answer(Set.empty, truth, falsity) shouldBe None
  }

  it should "match the same constant at an instance of its type, and say which" in {
    // The mechanism the fourteen polymorphic lemmas of `Product` and `Word` broke on. Equality is
    // the one polymorphic constant this module has, and `Const("=", A -> A -> bool)` and
    // `Const("=", bool -> bool -> bool)` are different terms: the walk failed on the head before it
    // reached an argument, so a lemma stated over `'a` matched nothing at any concrete type.
    val left = Term.variable("u", Type.Bool)
    val right = Term.variable("v", Type.Bool)
    val pattern = force(Term.appAll(Term.equalityAt(alpha), List(p, q)))
    val target = force(Term.appAll(Term.equalityAt(Type.Bool), List(left, right)))

    answer(Set(p, q), pattern, target) shouldBe
      Some((Map(p -> left, q -> right), Map("A" -> Type.Bool)))
  }

  it should "refuse an answer two of whose variables become one at the instance" in {
    // `h x:'A x:'B` against `h u v`, where `h` is at `bool -> bool -> bool`. Both type variables
    // solve to `bool`, and the two pattern variables are then one variable named `x` at one type
    // with two different values. `Kernel.instType` identifying them is sound and says so; an answer
    // that quietly kept one of the two would not be, so the match is refused instead.
    val a = Term.variable("x", alpha)
    val b = Term.variable("x", TyVar("B"))
    val head = Term.variable("h", Type.fun(alpha, Type.fun(TyVar("B"), Type.Bool)))
    val target =
      Term.variable("h", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))

    val pattern = force(Term.appAll(head, List(a, b)))
    val filled = force(
      Term.appAll(target, List(Term.variable("u", Type.Bool), Term.variable("v", Type.Bool)))
    )

    answer(Set(a, b), pattern, filled) shouldBe None

    // And the same shape answers where the two agree, which is one decision made twice rather than
    // two decisions that cannot both be kept.
    val agreeing = force(
      Term.appAll(target, List(Term.variable("u", Type.Bool), Term.variable("u", Type.Bool)))
    )

    answer(Set(a, b), pattern, agreeing) should not be None
  }

  "A match that decided a type" should "instantiate a theorem at both halves of what it decided" in {
    // What every consumer does with the answer, in one step: `Kernel.instType` and then
    // `Kernel.inst`, with the term substitution's keys carried to the instance. Done the other way
    // round, or with the keys left at the pattern's types, the substitution matches nothing and the
    // theorem comes back unchanged, which is a wrong answer rather than a refusal.
    val theorem = Kernel.refl(p)
    val boolean = Term.variable("b", Type.Bool)
    val found = Matching.matchTerm(Set(p), p, boolean).getOrElse(fail("expected a match"))

    force(found.instance(theorem)).conclusion shouldBe force(Term.eq(boolean, boolean))
  }

  "Matching under a binder" should "line the two bodies up by position" in {
    val pattern = lam(q, force(Term.app(f, q)))
    val target = lam(r, force(Term.app(g, r)))

    // The bound variable is an index on both sides, so `f` is the only thing left to bind.
    answer(Set(f), pattern, target) shouldBe Some((Map(f -> g), Map.empty))
  }

  it should "refuse to bind a pattern variable to a variable the binder owns" in {
    // `\x. p` against `\x. x`: binding p to the bound variable would take an index out of the
    // lambda that gives it meaning, and the substituted term would have no type at all.
    val pattern = lam(q, p)
    val target = lam(q, q)

    answer(Set(p), pattern, target) shouldBe None
  }

  it should "still bind a pattern variable to something from outside the binder" in {
    val pattern = lam(q, p)
    val target = lam(q, r)

    answer(Set(p), pattern, target) shouldBe Some((Map(p -> r), Map.empty))
  }

  /* ------------------------------------------------------------- the Miller fragment */

  "A pattern variable applied to a bound variable" should "bind to the abstraction over it" in {
    // `\x. P x` against `\x. f (f x)`. The first-order walk has no answer, because `P` would have
    // to become `f` and then `x` would have to become `f x`, and `x` is not a pattern variable.
    // The Miller answer is unique and this is it.
    val predicate = Term.variable("P", fn)
    val pattern = lam(q, force(Term.app(predicate, q)))
    val target = lam(q, force(Term.app(f, force(Term.app(f, q)))))

    val found = Matching.matchTerm(Set(predicate), pattern, target)

    found shouldBe defined
    found.get.terms(predicate) shouldBe lam(q, force(Term.app(f, force(Term.app(f, q)))))
  }

  it should "bind to a constant function when the target does not use the variable" in {
    // Still a Miller pattern, still one answer, and the answer ignores its argument. Worth pinning
    // because "the target does not mention it" is the case a reader expects to be a refusal.
    val predicate = Term.variable("P", fn)
    val pattern = lam(q, force(Term.app(predicate, q)))
    val target = lam(q, r)

    answer(Set(predicate), pattern, target) shouldBe Some((Map(predicate -> lam(q, r)), Map.empty))
  }

  it should "yield to the first-order answer wherever there is one" in {
    // `\x. F x` against `\x. g x` has both: `F := g` and `F := \x. g x`, eta-equal and not the
    // same term. Everything written before 2026-09-11 was written against the first, so the first
    // is what comes back and the fragment is an addition rather than a change.
    val pattern = lam(q, force(Term.app(f, q)))
    val target = lam(q, force(Term.app(g, q)))

    answer(Set(f), pattern, target) shouldBe Some((Map(f -> g), Map.empty))
  }

  it should "refuse an argument that is not a bound variable" in {
    // `F p` against `g q` with `p` free: outside the fragment, and outside it there is more than
    // one answer. The first-order walk still has its own, which is the `Some` here: what is being
    // asserted is that nothing invented a second one.
    val pattern = force(Term.app(f, p))

    answer(Set(f, p), pattern, force(Term.app(g, q))) shouldBe Some((Map(f -> g, p -> q), Map.empty))
  }

  it should "answer a repeated argument through the inner application, and answer it correctly" in {
    // `\x. F x x` against `\x. g2 (h x) x`. Written to have no answer, and it has one: the walk
    // reaches `F x` against `g2 (h x)`, which IS a Miller pattern, and takes
    // `F := \x. g2 (h x)`, whose double application is the target. The refusal of a repeated
    // argument is real and applies to the outer problem; the decomposition gets underneath it.
    //
    // The assertion moved with the finding. What is worth pinning is not that a shape is refused,
    // which was my expectation and was wrong, but that whatever comes back **reconstructs the
    // target**, which is the property the whole file is about and is checked below over every case.
    val binary = Term.variable("F", Type.fun(alpha, fn))
    val g2 = Term.variable("g2", Type.fun(alpha, fn))
    val h = Term.variable("h", fn)
    val pattern = lam(q, force(Term.appAll(binary, List(q, q))))
    val target = lam(q, force(Term.appAll(g2, List(force(Term.app(h, q)), q))))

    val found = Matching.matchTerm(Set(binary), pattern, target)

    found shouldBe defined
    filled(found.get, pattern) shouldBe normal(target)
  }

  it should "keep answering a repeated argument first order, where that route reaches it" in {
    val binary = Term.variable("F", Type.fun(alpha, fn))
    val h = Term.variable("h", Type.fun(alpha, fn))
    val pattern = lam(q, force(Term.appAll(binary, List(q, q))))
    val target = lam(q, force(Term.appAll(h, List(q, q))))

    answer(Set(binary), pattern, target) shouldBe Some((Map(binary -> h), Map.empty))
  }

  "Every answer this matcher gives" should "turn the pattern into the target" in {
    // The property the file exists for, and the one an example cannot carry: a matcher that
    // answers wrongly costs a rewrite that rewrites to something else. It is cheap to check
    // because matching is one-way, so the check is substitution and beta, with no search in it.
    //
    // The cases are the ones above, gathered rather than restated, plus the higher-order shapes,
    // which are where a wrong answer became possible on 2026-09-11.
    val predicate = Term.variable("P", fn)
    val binary = Term.variable("F", Type.fun(alpha, fn))
    val g2 = Term.variable("g2", Type.fun(alpha, fn))
    val h = Term.variable("h", fn)

    val cases: Vector[(Set[FVar], Term, Term)] = Vector(
      (Set(p), p, q),
      (Set(p), force(Term.app(f, p)), force(Term.app(f, q))),
      (Set(f), lam(q, force(Term.app(f, q))), lam(q, force(Term.app(g, q)))),
      (Set(p), lam(q, p), lam(q, r)),
      (Set(predicate),
        lam(q, force(Term.app(predicate, q))),
        lam(q, force(Term.app(f, force(Term.app(f, q)))))),
      (Set(predicate), lam(q, force(Term.app(predicate, q))), lam(q, r)),
      (Set(binary),
        lam(q, force(Term.appAll(binary, List(q, q)))),
        lam(q, force(Term.appAll(g2, List(force(Term.app(h, q)), q)))))
    )

    val answered = cases.flatMap { case (variables, pattern, target) =>
      Matching.matchTerm(variables, pattern, target).map((pattern, target, _))
    }

    answered.size shouldBe cases.size

    answered.foreach { case (pattern, target, answer) =>
      withClue(s"matching $pattern against $target gave $answer\n") {
        filled(answer, pattern) shouldBe normal(target)
      }
    }
  }

  it should "refuse a target that uses a binder the variable was not applied to" in {
    // `\x. \y. P x` against `\x. \y. f y`. An answer would have to let `P` see `y`, which it was
    // not given, and the abstraction would carry a variable out of the binder that owns it.
    val predicate = Term.variable("P", fn)
    val pattern = lam(q, lam(r, force(Term.app(predicate, q))))
    val target = lam(q, lam(r, force(Term.app(f, r))))

    answer(Set(predicate), pattern, target) shouldBe None
  }

  /* --------------------------------------------- a variable an earlier occurrence decided */

  /**
   * `\x. h (P x) (P (s x))`: the first occurrence of `P` is a Miller pattern and decides it, and
   * the second is applied to `s x`, which is not a binder.
   *
   * Until 2026-09-25 the second occurrence reached the Miller case, which does not look at what is
   * decided, and every pair of this shape was refused, instances included. The cases below are
   * the ones the change has to keep apart: an instance, a pair that is not one, a variable still
   * unsolved inside the argument, the same at a polymorphic pattern where it stays refused, and a
   * decided term that mentions the pattern's own variable, which is the input that would make the
   * check recurse forever if it were written the obvious way.
   */
  private val ground = TyApp("g", Nil)
  private val predicate = Term.variable("P", Type.fun(ground, Type.Bool))
  private val successor = Term.variable("s", Type.fun(ground, ground))
  private val pair = Term.variable("h", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))
  private val x = Term.variable("x", ground)
  private val c = Term.variable("c", ground)

  private def both(first: Term, second: Term): Term = force(Term.appAll(pair, List(first, second)))
  private def at(function: Term, argument: Term): Term = force(Term.app(function, argument))
  private def equal(left: Term, right: Term): Term = force(Term.eq(left, right))

  /** `\x. h (P x) (P (s x))`, over whatever `P` and `s` are handed in. */
  private def step(p: FVar, s: FVar, over: FVar): Term =
    lam(over, both(at(p, over), at(p, at(s, over))))

  "A variable an earlier occurrence decided" should "be checked where it recurs, and give the instance" in {
    val target = lam(x, both(equal(x, c), equal(at(successor, x), c)))
    val found = Matching.matchTerm(Set(predicate), step(predicate, successor, x), target)

    found.map(_.terms) shouldBe Some(Map(predicate -> lam(x, equal(x, c))))
    found.map(_.types) shouldBe Some(Map.empty)
    filled(found.get, step(predicate, successor, x)) shouldBe target
  }

  it should "refuse a pair that is not an instance, and call it a miss rather than the fragment's limit" in {
    // `P` decided as `\x. x = c`, and the second place holds `x = c` where `s x = c` was owed.
    val target = lam(x, both(equal(x, c), equal(x, c)))

    Matching.matchTerm(Set(predicate), step(predicate, successor, x), target) shouldBe None
    Matching.why(Set(predicate), step(predicate, successor, x), target) shouldBe None
  }

  it should "solve a variable still unsolved inside the argument" in {
    // `\x. h (P x) (P (s m))` against `\x. h (x = c) (s d = c)`: once `P` is known, the second
    // place is `s m = c` against `s d = c`, which is first order and decides `m`.
    val m = Term.variable("m", ground)
    val d = Term.variable("d", ground)
    val pattern = lam(x, both(at(predicate, x), at(predicate, at(successor, m))))
    val target = lam(x, both(equal(x, c), equal(at(successor, d), c)))

    answer(Set(predicate, m), pattern, target) shouldBe
      Some((Map(predicate -> lam(x, equal(x, c)), m -> d), Map.empty))
  }

  it should "decide the types too, where the argument holds nothing unsolved" in {
    // The same step over a type variable, against a target at `g`: the decided term is at `g` and
    // the argument at `A`, so the argument is put at the target's types before it is applied. `s`
    // is not a pattern variable here, which is what "nothing unsolved" means: it is compared by
    // name and a type match, as the case below this one would need it solved and cannot.
    val overA = Term.variable("x", alpha)
    val polymorphic = Term.variable("P", Type.fun(alpha, Type.Bool))
    val next = Term.variable("s", fn)
    val target = lam(x, both(equal(x, c), equal(at(successor, x), c)))

    val found = Matching.matchTerm(Set(polymorphic), step(polymorphic, next, overA), target)

    found.map(_.types) shouldBe Some(Map("A" -> ground))
    filled(found.get, step(polymorphic, next, overA)) shouldBe target
  }

  it should "stay refused at a polymorphic pattern whose argument holds an unsolved variable, and say so" in {
    // The one case the check does not reach, and the refusal is the fragment's: the argument is at
    // the pattern's types and cannot be put at the target's while `m` is unknown.
    val overA = Term.variable("x", alpha)
    val polymorphic = Term.variable("P", Type.fun(alpha, Type.Bool))
    val m = Term.variable("m", alpha)
    val pattern = lam(overA, both(at(polymorphic, overA), at(polymorphic, at(f, m))))
    val target = lam(x, both(equal(x, c), equal(at(successor, c), c)))

    Matching.matchTerm(Set(polymorphic, m, f), pattern, target) shouldBe None
    Matching.why(Set(polymorphic, m, f), pattern, target) shouldBe
      Some(Matching.Refusal.ArgumentIsNotABinder(polymorphic))
  }

  /**
   * The decided route recurses: `F (F x)` hands `F x` back to the walk, which meets the decided
   * `F` a second time inside its own argument. Nothing above has a decided variable inside the
   * argument of its own recurrence, and the property the file exists for, that an answer turns the
   * pattern into the target, was asserted over the shapes that predate this route and not over it.
   *
   * `\x. h (F x = c) (F (F x) = c)` against `\x. h (k x x = c) (k (k x x) (k x x) = c)`: the first
   * place is a Miller pattern and decides `F := \x. k x x`, since `k x` holds the binder and so
   * cannot be bound first order; the second is then decided twice over. Beside it the pair where
   * the outer argument is not the decided term applied, which must be refused as a miss.
   *
   * Written by the verification of card eb258a45 on 2026-09-25 against `87175842`. What it catches
   * is an answer the decided route gives that the substitution does not bear out, which no case
   * above can see because none of them nests the variable.
   */
  it should "turn the pattern into the target where the decided variable recurs inside its own argument" in {
    val twice = Term.variable("F", Type.fun(ground, ground))
    val k = Term.variable("k", Type.fun(ground, Type.fun(ground, ground)))
    def kk(left: Term, right: Term): Term = force(Term.appAll(k, List(left, right)))

    val pattern = lam(x, both(equal(at(twice, x), c), equal(at(twice, at(twice, x)), c)))
    val target = lam(x, both(equal(kk(x, x), c), equal(kk(kk(x, x), kk(x, x)), c)))

    val found = Matching.matchTerm(Set(twice), pattern, target)
    found.map(_.terms) shouldBe Some(Map(twice -> lam(x, kk(x, x))))
    filled(found.get, pattern) shouldBe target

    val notAnInstance = lam(x, both(equal(kk(x, x), c), equal(kk(kk(x, x), x), c)))
    Matching.matchTerm(Set(twice), pattern, notAnInstance) shouldBe None
    Matching.why(Set(twice), pattern, notAnInstance) shouldBe None
  }

  it should "stop where the decided term mentions the pattern's own variable" in {
    // The target uses `P` itself, so the first place decides `P := P`. The second place is then
    // `P (s x)` against `P (t x)`, and handing `P (s x)` back to the walk would arrive here again
    // with nothing changed. It has to come back refused, and come back at all.
    val other = Term.variable("t", Type.fun(ground, ground))
    val target = lam(x, both(at(predicate, x), at(predicate, at(other, x))))

    Matching.matchTerm(Set(predicate), step(predicate, successor, x), target) shouldBe None
  }

  /* ------------------------------------------------- which condition a refusal met */

  /**
   * `Matching.why` is the half `None` cannot carry, and each case below is one of the conditions
   * `Matching.Refusal` names.
   *
   * What it is for is measuring this matcher: a caller looking at a tactic that did not fire cannot
   * tell an ordinary miss from a question the fragment turned down, and until this landed the only
   * way to tell was to instrument the file and run the suite. `docs/adr/0030` is the census taken
   * that way, and these are the cases it counted, so the next one costs a call.
   */
  "A refused match" should "name the condition of the fragment it met" in {
    val predicate = Term.variable("P", fn)

    // Applied to something that is not a binder: `\x. P (f x)` against `\x. g x`.
    val notABinder = lam(q, force(Term.app(predicate, force(Term.app(f, q)))))
    Matching.why(Set(predicate), notABinder, lam(q, force(Term.app(g, q)))) shouldBe
      Some(Matching.Refusal.ArgumentIsNotABinder(predicate))

    // The target using a binder the variable was not applied to, which is the case above this.
    val escaping = lam(q, lam(r, force(Term.app(predicate, q))))
    Matching.why(Set(predicate), escaping, lam(q, lam(r, force(Term.app(f, r))))) shouldBe
      Some(Matching.Refusal.TargetSeesAnotherBinder(predicate))
  }

  it should "name the condition under a binder over a type variable, as it does under a ground one" in {
    // `\x:A. P (s x)` against `\x:g. s x = c`. Until 2026-09-25 `why` opened both binders with
    // one variable at the target's type, which cannot be substituted into a binder over `A`, so
    // this came back `None`, "not refused by the fragment", while `matchTerm` refused it at exactly
    // this condition. Found by the case "stay refused at a polymorphic pattern" below, whose first
    // red was this and not what it was written for.
    val overA = Term.variable("x", alpha)
    val polymorphic = Term.variable("P", Type.fun(alpha, Type.Bool))
    val pattern = lam(overA, at(polymorphic, at(Term.variable("s", fn), overA)))
    val target = lam(x, equal(at(successor, x), c))

    Matching.matchTerm(Set(polymorphic), pattern, target) shouldBe None
    Matching.why(Set(polymorphic), pattern, target) shouldBe
      Some(Matching.Refusal.ArgumentIsNotABinder(polymorphic))
  }

  it should "call a first-order miss what it is, rather than a limit of the fragment" in {
    // **The distinction the census turned on.** With no binder open, a pattern variable applied to
    // anything is a first-order problem, and over the whole corpus that is where almost every
    // refusal of this shape comes from: 4377 of 4627 on `tactics/test`, and 278 of 278 on the
    // miniF2F corpus, measured 2026-09-18 and written down in `docs/adr/0030`. Reporting those as
    // the fragment's boundary would have said the boundary is met thousands of times a run.
    val binary = Term.variable("F", Type.fun(alpha, fn))
    val pattern = force(Term.appAll(binary, List(p, q)))

    Matching.why(Set(binary), pattern, force(Term.appAll(g, List(p)))) shouldBe
      Some(Matching.Refusal.NoBinderInScope(binary))
  }

  it should "say which refusals are the fragment's boundary, so a caller can tell a limit from a miss" in {
    // The reading `Rules.specTo` spends: three of the four are the fragment turning a question
    // down, and the fourth is a first-order miss. All four, so that the one answering `false` is
    // seen answering it rather than assumed to.
    val predicate = Term.variable("P", fn)

    Matching.Refusal.NoBinderInScope(predicate).isTheFragmentsBoundary shouldBe false
    Matching.Refusal.ArgumentIsNotABinder(predicate).isTheFragmentsBoundary shouldBe true
    Matching.Refusal.BinderAppliedTwice(predicate).isTheFragmentsBoundary shouldBe true
    Matching.Refusal.TargetSeesAnotherBinder(predicate).isTheFragmentsBoundary shouldBe true
  }

  it should "answer nothing where the match succeeded, so a caller cannot read a limit into one" in {
    // The control that keeps the cases above from being a report on every call: a pair the
    // fragment answers has no refusal to name, and neither has a pair that simply does not match
    // for the ordinary reason.
    val predicate = Term.variable("P", fn)
    val pattern = lam(q, force(Term.app(predicate, q)))

    Matching.why(Set(predicate), pattern, lam(q, force(Term.app(f, q)))) shouldBe None
    Matching.why(Set(f), f, g) shouldBe None
  }
}
