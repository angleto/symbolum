package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The chain, the induction driver and the congruence lemma: three suggestions from a consumer.
 *
 * All three came from somebody using this on a development rather than reading it, which is where
 * the useful suggestions have come from twice now. The card is b15f7217 and it carries the
 * measurement behind each one, including the two it withdrew.
 */
class ChainSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard

  /* ------------------------------------------------------------------ the order */

  "The chain" should "put the naturals under the reals, which is the order that works" in {
    // The property this exists for. A tactic is built over a `RealTheory`, so the reals have to be
    // the later of the two or every tactic reads a signature with no `num` in it. Asserted by
    // asking `Ring` a goal that mentions both types rather than by reading the construction.
    chain.reals.theory.typeOperators.keySet should contain(Natural.TypeName)
    chain.series.theory.typeOperators.keySet should contain(Real.TypeName)

    val goal = force(chain.series.proposition("!f:num->real. !n:num. Sum f n + 0 = Sum f n"))
    force(chain.ring.prove(goal))
  }

  it should "hold one signature, so a fact of any stage is a fact about the same constants" in {
    val everywhere = force(chain.series.fact(Series.AtZero))
    val ordered = force(chain.order.zeroLessOne)

    chain.series.show(everywhere.conclusion) shouldBe "!f:num -> real. Sum f 0 = 0"
    chain.reals.show(ordered.conclusion) shouldBe "0 < 1"
    // The classical logic's two and infinity, and nothing else: the sixteen of the field are
    // theorems about the cuts since `docs/adr/0053`. It was nineteen from eta's landing on
    // 2026-09-10 until then.
    chain.series.theory.axioms.toSet shouldBe chain.naturals.theory.axioms.toSet
    chain.series.theory.axioms should have size 3

    // And the same three at each stage, the construction below the reals included, which is the
    // claim `docs/adr/0006` makes about `defineType` and the one `Kernel.defineConstant` makes about
    // a definition. Asserted at each stage, because a conservative extension that stopped being one
    // would do it at exactly one of them and the total would not say which. Until `docs/adr/0053`
    // this was two lists, nineteen above the reals and three below them.
    Vector(
      chain.pure.theory,
      chain.product.theory,
      chain.fractions.integers.theory,
      chain.fractions.theory,
      chain.cuts.theory,
      chain.reals.theory,
      chain.divisibility.theory,
      chain.modular.theory,
      chain.word.theory,
      chain.matrix.theory
    ).foreach(theory => theory.axioms.toSet shouldBe chain.naturals.theory.axioms.toSet)
  }

  it should "hold the five that were beside it, so that one signature can state a claim about any" in {
    // The whole of what being **in** the chain buys, asserted as the thing a caller does rather
    // than as a field being present. Each of these was unstatable before 2026-09-12, not because
    // the constant did not exist but because it existed in a theory nothing else extended, and
    // `docs/adr/0008` is why a second copy is a different constant rather than the same one.
    force(chain.widest.proposition("!a:real. !n:num. Divides a a /\\ NUM_DIVIDES n n"))
    force(chain.widest.proposition("!m:num. !n:num. NUM_CONG (NUM_GCD m n) m m"))
    force(
      chain.widest.proposition(
        "!f:num->real. !p:prod(num,num). Sum f (FST p) = Sum f (FST (PAIR (FST p) (SND p)))"
      )
    )
    force(chain.widest.proposition("!w:word(real). !f:num->real. Sum f (WORD_LENGTH w) = 0"))

    // `Bounded` is the fifth and declares nothing, so there is no constant of its own to state a
    // claim about. What it contributes is a driver, and that it is reachable from the chain at all
    // is the assertion here.
    chain.bounded.limit shouldBe Bounded.Instances
  }

  it should "read `abs` as the constant and not as a variable of that name, which is how it failed" in {
    // `Magnitude` was outside the chain until 2026-09-13, and what that cost is not what a reader
    // would expect. `max`, `min`, `abs` and `sgn` were not constants of the widest signature, so a
    // goal naming one did not fail: an unknown letter-initial name parses as a FREE VARIABLE, so
    // the claim was well typed, about an arbitrary function, and had nothing to do with the
    // absolute value. Nothing refused. It is the same trap the `peano` field comment records for
    // `NUM_LE ZERO n`, still live a day after that one was closed.
    //
    // **Asserted on the term and not on the printed form**, because the printed form is identical
    // in the two cases: `Sum f n = abs x` is what a reader sees whether `abs` is the constant or a
    // variable somebody invented. A test that compared the printing would have passed on the
    // broken tree, which is the failure this repository calls answering the adjacent question.
    def named(term: Term): (Set[String], Set[String]) = term match {
      case Const(name, _) => (Set(name), Set.empty)
      case FVar(name, _) => (Set.empty, Set(name))
      case App(fn, argument) =>
        val (leftConstants, leftVariables) = named(fn)
        val (rightConstants, rightVariables) = named(argument)
        (leftConstants ++ rightConstants, leftVariables ++ rightVariables)
      case Abs(_, body) => named(body)
      case _ => (Set.empty, Set.empty)
    }

    val claim = force(chain.widest.proposition("Sum (f:num -> real) (n:num) = abs (x:real)"))
    val (constants, variables) = named(claim)

    constants should contain("abs")
    variables should not contain "abs"
    Vector("max", "min", "sgn").foreach(name =>
      chain.widest.theory.constants.keySet should contain(name)
    )

    // And the paired half, without which the assertion above says only that the parser has some
    // constants: a name the signature genuinely does not have still reads as a variable, so what
    // changed is `abs` and not the reading of unknown names.
    val unknown = force(chain.widest.proposition("Sum (f:num -> real) (n:num) = zork (x:real)"))
    named(unknown)._2 should contain("zork")
    named(unknown)._1 should not contain "zork"
  }

  it should "hold a conditional, at every type, and pay no axiom for it" in {
    // The chain had no conditional constant at all until 2026-09-12, so a function defined by cases
    // had nothing to write its cases with. It is defined in `Classical` rather than in one of the
    // developments, which is the only place it can go if everything is to reach it: a constant
    // defined in a development is unavailable to every link **below** it, and anything at all can
    // be defined by cases.
    //
    // The assertion is the pair. A definition is conservative, so the axioms do not move, and the
    // constant is in the widest signature, so a claim can name it at any type the chain has.
    chain.widest.theory.axioms.toSet shouldBe chain.naturals.theory.axioms.toSet

    // And the type operators counted, not merely searched for, which until 2026-09-13 nothing here
    // did: this suite asserted memberships (`contain`), the difference between two adjacent
    // theories (`WordSpec`, `MatrixSpec`) and one arity (`NaturalSpec`), so a new link at the top
    // of the chain declaring a type operator would have passed in silence. A declared operator is
    // conservative and costs no axiom, which is why the count above cannot see it, and it is still
    // part of what a claim may be written in: `docs/architecture.md` says why a type nobody
    // declares is uninterpreted and why that is not the same as harmless.
    //
    // The arity is asserted with the name because an arity is exactly as silent as a name.
    // `Kernel.defineType` takes it from the type variables of the predicate it is given, ordered, so
    // a predicate written with one variable more produces an operator of the same name at a
    // different arity and nothing anywhere says so; a check on the names alone passes. `word` takes
    // one argument, `prod` and `fun` take two, and every other operator below takes none.
    //
    // Both are measured rather than recalled: the names off `Chain.widest`, the arities off the
    // declarations themselves, in `Real` and `Natural` and in the `TyApp` each carved type is
    // applied with). The consumer repository's certified artifact prints these names in its
    // header and has read them unchanged across nine commits of this one, which means that until
    // this line existed a build outside this repository was the only witness to half of what the
    // signature is, and nothing at all was a witness to the arities.
    chain.widest.theory.typeOperators shouldBe Map(
      "bool" -> 0,
      "fun" -> 2,
      "ind" -> 0,
      // The type carved on 2026-09-18, and the arity is the interesting half: `int` is a
      // quotient of `prod(num,num)`, so a reader who expected the carrier's parameters to travel
      // with it would look for two. They do not. `Kernel.defineType` carves a type out of a
      // **closed** predicate, and `INT_SAME` names both of its components, so nothing about the
      // carrier is left free for the new operator to be parameterised by.
      "int" -> 0,
      "num" -> 0,
      "prod" -> 2,
      // The rationals and the cuts, in the chain since phase 5 put the construction of the reals
      // below them on 2026-09-26. Both carved from closed predicates, so of arity nought.
      "rat" -> 0,
      "real" -> 0,
      "word" -> 1
    )

    chain.widest.theory.definitions.keySet should contain(Classical.Conditional)
    chain.widest.theory.axioms.size shouldBe Classical.Axioms.size + Natural.Axioms.size

    force(chain.widest.proposition("!x:real. COND (x < 0) (0 - x) x = COND (0 < x) x (0 - x)"))
    force(chain.widest.proposition("!m:num. !n:num. COND (NUM_LE m n) m n = m"))
    force(
      chain.widest.proposition("!f:num->real. !n:num. COND (Sum f n = 0) f (\\i:num. 0) = f")
    )

    // And the equations reach the chain, which is what makes the constant usable rather than only
    // sayable: they are stated over a type variable in `Classical` and instantiate at `real` here.
    val atReal = Kernel.instType(
      Map(Classical.TypeVariable -> TyApp(Real.TypeName, Nil)),
      force(chain.classical.fact(Classical.CondTrue))
    )

    chain.widest.show(atReal.conclusion) shouldBe
      "!p:bool. !x:real. !y:real. p ==> COND p x y = x"
  }

  it should "put the arithmetic of the naturals under the sums, which is what a summand needs" in {
    // The second ordering question, settled on 2026-09-11 after being settled the wrong way round
    // earlier the same day. `Peano` and `Series` each extend the reals for their own constants, so
    // one has to be built over the other; putting `Peano` on top makes every constant **nameable**
    // in a goal and still leaves `NUM_ADD` unusable **inside** a `Sum`, because `Sum` was defined
    // over a theory that had no addition in it. A constant declared after a definition cannot
    // appear in it.
    //
    // Asserted by reading a proposition rather than by reading the construction, because that is
    // the property: the statement is a statement.
    // `Word` for a few hours of 2026-09-12, then `Matrix`, then `Rotation`, `Magnitude` on
    // 2026-09-13, `Coding` later the same day, then `Numbering`, `Language`, `Transcendental`, and
    // `Inductive` on 2026-09-16 — nine in five days, which is the rate that makes the second
    // assertion the one worth reading. The field names whichever development is the
    // last extension, and that is the property; which one it is today is not. So the assertion
    // below is written twice: once naming today's, which has to be edited when the order changes,
    // and once as the property itself, which does not and is what a reader should take from the
    // line.
    //
    // `Coding` is the first of them whose prerequisites sit elsewhere: it draws its facts from
    // `Modular`, several links down in `Chain.construct`, and extends the last theory anyway.
    // `Numbering` is the second and is further still from what it needs: everything it proves is
    // `Peano`'s arithmetic, below `Modular` in the same order, and it extends `Coding` because that
    // is where the chain's end is. That is the distinction `Rotation.construct` records and the
    // one that makes this assertion worth having twice, because the obvious place to put a
    // development is beside what it needs, and the obvious place is a side branch where a
    // constant is unreachable from everything.
    //
    // `Inductive` on 2026-09-16 is the third of that kind and the limiting case of it: its
    // prerequisites are not elsewhere, they are EMPTY. `MONOTONE` and `INDUCTIVE` are polymorphic
    // and mention nothing this chain built, so there is no development it would naturally sit
    // beside, and the only thing deciding where it goes is that a constant has to be declared into
    // the last theory to be reachable. The two orders `Rotation.construct` distinguishes are not
    // merely different here; one of them is empty.
    // **And it moved again on 2026-09-16**, to `Forward`, which is the second development built
    // on `Inductive` and the one the rewriting work was for. The note above about `Inductive` not
    // having a development to sit beside does not transfer to this one: the right forward closure
    // is about words, so `Concatenation` is exactly where it would naturally sit, and what puts it
    // at the end instead is the rule that names this whole section -- a constant is reachable only
    // from the last theory. Which link is last is read here and written nowhere else.
    // **And again on 2026-09-18**, to `Integer`, a new type operator, which is the sixth entry
    // in this paragraph's own list and the reason the list is here rather than a sentence naming
    // the current one. `docs/adr/0033` decides that the integers arrive as a prerequisite of two
    // blocked formalisations rather than as stage four of the construction of the reals, and what
    // puts this link at the end is the rule the paragraph above names and nothing about its
    // subject: a constant is reachable only from the last theory.
    // **And again the same day**, to `Inclusion`, which is the seventh entry and the first one that
    // is not a new subject: it is the piece of `Integer` that mentions a real, split out because
    // `docs/adr/0033` rests phase 5's move of that development on its saying nothing about one.
    // Seven entries in five days is the measurement this paragraph exists to be instead of a
    // sentence naming whichever link is current.
    // **And again on 2026-09-23**, to `Listing`, the eighth entry, and the first one that adds no
    // type where a reader of the card would have expected one: `docs/adr/0038` decides that a list
    // is an orientation on `word` rather than a carrier of its own, so what puts this link at the
    // end is the same rule as every entry above it and nothing about its subject. The assertion
    // two paragraphs down that the type operators do not move is what carries that decision here.
    // **And again the same day**, to `Folding`, the ninth entry, and the first one whose subject is
    // a CONSUMER of the link below it rather than a subject of its own: `LIST_FOLD` is defined by
    // `LIST_RECURSION`, and a development that spent that theorem beside the chain would declare
    // its constant where nothing above can see it.
    // **And again on 2026-09-24**, to `Root`, the tenth entry: the square root, which needs the
    // reals and their order and nothing since, and is at the end for the same rule and nothing
    // about its subject.
    // **And again the same day**, to `Continuity`, the eleventh: continuity at a point and the
    // intermediate value theorem, which need the reals, their order and their magnitude.
    // **And again on 2026-09-25**, to `Resolving`, the twelfth, and the first entry that was a
    // development before it was a link: it sat beside the chain declaring nothing for ten days, and
    // what moved it is that a statement about every refutation is written with its four constants.
    // It needs the naturals and nothing since, and is at the end for the same rule.
    // **And again the same day**, to `Derivative`, the thirteenth: the derivative at a point and
    // Rolle's theorem, which reads `continuous` and nothing `Resolving` declares, and is at the end
    // for the same rule and nothing about its subject.
    // **And again the same day**, to `Integral`, the fourteenth: the gauge integral and the
    // fundamental theorem, which names `derivative` and so sits above it.
    // **And again on 2026-09-27**, to `Circle`, the fifteenth: `pi` and `acos`, which read the
    // derivative's monotonicity and nothing the integral declares, and are at the end for the same
    // rule and nothing about their subject.
    chain.widest shouldBe chain.circle
    chain.widest.theory.constants.keySet shouldBe chain.circle.theory.constants.keySet
    Vector(
      chain.series, chain.peano, chain.modular, chain.product, chain.word, chain.matrix,
      chain.rotation, chain.magnitude, chain.coding, chain.numbering, chain.provability, chain.limit,
      chain.transcendental, chain.concatenation, chain.inductive, chain.integers, chain.inclusion,
      chain.listing, chain.folding, chain.root, chain.continuity, chain.resolving, chain.derivative,
      chain.integral
    ).foreach(earlier =>
      chain.widest.theory.constants.keySet should contain allElementsOf earlier.theory.constants.keySet
    )
    // The property that argument is about, which is `Peano` under `Series` and is unchanged: the
    // two are still adjacent and still that way round. What moved on 2026-09-12 is only what sits
    // on top of the pair, so the proposition below is read through the signature that is last
    // rather than through `Series` by name.
    chain.series.theory.constants.keySet should contain(Peano.Addition)

    force(
      chain.widest.proposition(
        "!f:num->real. !m:num. !n:num. Sum (\\i:num. f (NUM_ADD m i)) n = Sum f (NUM_ADD m n) - Sum f m"
      )
    )

    // And the other direction stays: `Peano` needs nothing from `Series`, so its own theory does
    // not declare `Sum`. If that ever became false the two would be mutually dependent and neither
    // order would work.
    chain.peano.theory.constants.keySet should not contain Series.SumName
  }

  it should "cost what a chain costs, once, which is not the argument for having it" in {
    // The card proposed this for the order and explicitly not for speed, having measured it first
    // and withdrawn the speed argument. Kept so that nobody re-proposes it as a cache: if this ever
    // became slow enough to matter, that would be a different finding.
    //
    // **Reported and not asserted, since 2026-09-11.** The bound was ten seconds against a reading
    // of a few hundred milliseconds, thirty times looser, and it went red anyway on a machine
    // another program had at a load average of two hundred. A guard a third party can trip is a
    // guard that teaches a reader to ignore the suite, and the thing it was guarding is visible in
    // the reading.
    //
    // **Read off the one build rather than timed on a second, since 2026-09-26.** This test built a
    // whole chain beside `Chain.standard` to time it, so the JVM held two, each about half a
    // gigabyte, under the forked test JVM's `-Xmx1024m`; measured that day, `theories/test` on
    // `7.0` passed and the same suite with one more derivation in the chain died here of an
    // `OutOfMemoryError`. The build `Chain.standard` already does is the same reading.
    val elapsed = Chain.standardMilliseconds
    elapsed should be >= 0L

    info(s"the chain builds in $elapsed ms, which is a reading and not an assertion")
  }

  /* ------------------------------------------------------------------ the driver */

  "The induction driver" should "prove a statement about every number, given its recurrences" in {
    // The shape a consumer wrote out seven times by hand. What it takes is the equations the
    // rewriter may use; what it does is instantiate induction, rewrite each half, and hand the rest
    // to `Ring`.
    val recurrences = Vector(
      force(chain.series.fact(Series.PowerAtZero)),
      force(chain.series.fact(Series.PowerAtSuccessor)),
      force(chain.series.fact(Series.AtZero)),
      force(chain.series.fact(Series.AtSuccessor))
    )

    val statement = force(
      chain.series.proposition("!n:num. Sum (\\i:num. Power 2 i) n = Power 2 n - 1")
    )

    val theorem = force(chain.induct.prove(statement, recurrences))

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe statement
  }

  it should "refuse rather than hand back a theorem about something else" in {
    // A driver that returned whatever it managed to build would be the first of the two mistakes
    // the card says go wrong silently. Handed no recurrences it cannot reach either half, and it
    // says so instead of producing a theorem the caller then has to check.
    val statement = force(chain.series.proposition("!n:num. Sum (\\i:num. Power 2 i) n = Power 2 n - 1"))

    chain.induct.prove(statement, Vector.empty).isLeft shouldBe true
  }

  it should "hand the two halves over when the hypothesis is not usable as a rewrite" in {
    // The limit of the default step, measured rather than assumed: the induction hypothesis has to
    // have its left side as a subterm of the step goal. `Sum f n = Power 2 n - 1` has that shape and
    // `Sum f n + 1 = Power 2 n` does not, and they are the same statement. That is the case the
    // card's waypoint list was for, and the reason the halves arrive as functions is that a caller
    // cannot name the variable the step is about: the driver opens the quantifier itself.
    val recurrences = force(
      Rewrite.Rule.all(
        chain.logic,
        Vector(
          force(chain.series.fact(Series.PowerAtZero)),
          force(chain.series.fact(Series.PowerAtSuccessor)),
          force(chain.series.fact(Series.AtZero)),
          force(chain.series.fact(Series.AtSuccessor))
        )
      )
    )

    val awkward = force(
      chain.series.proposition("!n:num. Sum (\\i:num. Power 2 i) n + 1 = Power 2 n")
    )

    chain.induct.prove(awkward, Vector.empty).isLeft shouldBe true

    // The same statement, with a step that turns the hypothesis round before using it. `sym` is all
    // it takes here, since what is wanted is `Power 2 n` replaced rather than the sum.
    val theorem = force(
      chain.induct.proveBy(
        awkward,
        goal => chain.induct.settle(recurrences)(goal, Vector.empty),
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          for {
            turned <- Conv.sym(hypothesis)
            rule <- Rewrite.Rule.of(chain.logic, turned)
            proved <- chain.induct.settle(recurrences)(goal, Vector(rule))
          } yield proved
      )
    )

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe awkward
  }

  it should "tell an exhausted rewriter from a false identity, which are the same Left otherwise" in {
    // The finding card 5f0cd494 is about, met again in a new place. `Rewrite.rewrite` hands back the
    // theorem it had built when the step limit ran out, and that theorem is true: nothing in it says
    // whether the rewriting had finished. So the driver's step, whose rules do not settle, produced
    // `Ring`'s "the two normal forms differ" and sent a caller to check an identity that was never
    // the problem.
    //
    // Two rules that undo each other, so the rewriting alternates for ever. What must come back is
    // `NotNormalised` and not the ring's complaint.
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)
    val f = Term.variable("ff", Type.fun(numbers, values))
    val g = Term.variable("gg", Type.fun(numbers, values))

    val there = force(chain.series.proposition("!i:num. (ff:num->real) i = (gg:num->real) i"))
    val back = force(chain.series.proposition("!i:num. (gg:num->real) i = (ff:num->real) i"))
    val alternating = force(
      Rewrite.Rule.all(
        chain.logic,
        Vector(
          force(LogicError.lift(Kernel.assume(there))),
          force(LogicError.lift(Kernel.assume(back)))
        )
      )
    )

    val goal = force(chain.series.proposition("(ff:num->real) (n:num) = 1"))

    chain.induct.settle(alternating)(goal, Vector.empty).left.map(_.getClass) shouldBe
      Left(classOf[NotNormalised])
    val _ = (f, g)
  }

  /* ------------------------------------------------------------------ the congruence */

  "The rewriter" should "go into the lambda a sum binds, which is why the congruence is narrow" in {
    // The measurement that made the card's own earlier claim smaller. A summand written out is
    // rewritten where it stands, so for the common case no lemma is needed at all.
    val logic = chain.logic
    val theory = chain.series.theory
    val notation = chain.series.notation

    val ff = Term.variable("ff", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
    val gg = Term.variable("gg", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
    val pointwise = force(
      Parser.proposition(theory, notation, "!i:num. (ff:num->real) i = (gg:num->real) i")
    )
    val rule = force(Rewrite.Rule.of(logic, force(LogicError.lift(Kernel.assume(pointwise)))))

    def rewritten(text: String): String = {
      val term = force(Parser.term(theory, notation, text))
      val equation = force(Rewrite.rewrite(Vector(rule), term))
      chain.series.show(Term.destEq(equation.conclusion).get._2)
    }

    rewritten("Sum (\\i:num. (ff:num->real) i) (n:num)") should include("gg")
    rewritten("Sum (\\i:num. 2 * (ff:num->real) i) (n:num)") should include("gg")

    // And the case it does not reach, which is the whole scope of the lemma below: a bare symbol
    // has no redex to go into.
    rewritten("Sum (ff:num->real) (n:num)") should not include "gg"
    val _ = (ff, gg)
  }

  "The congruence lemma" should "cover exactly that case, and assume nothing" in {
    val congruence = force(chain.series.fact(Series.Congruence))

    chain.series.show(congruence.conclusion) shouldBe
      "!f:num -> real. !g:num -> real. (!n:num. f n = g n) ==> (!n:num. Sum f n = Sum g n)"
    congruence.hypotheses shouldBe empty
  }

  it should "no longer be the only route into a binder, since eta landed" in {
    // **This assertion has changed meaning and the number is why.** It read as the record that
    // extensionality was not among what is believed, and that while it was not, a congruence lemma
    // was the only route into a binder whose body is a bare symbol; a future product or integral
    // would have wanted its own. Eta went into `Classical.scala` on 2026-09-10, so the count moved
    // to nineteen and the reason went away: `Classical.ext` takes the pointwise hypothesis to an
    // equation between the two functions, and congruence carries that into any binder at all.
    //
    // `SUM_CONGRUENCE` is still proved and still exported, because a caller holding the pointwise
    // hypothesis should not have to know which of the two routes is cheaper. What changed is that
    // the next binding operator does not need one of its own.
    chain.series.theory.axioms.toSet shouldBe chain.naturals.theory.axioms.toSet
    chain.series.theory.definitions.keySet should contain(Series.SumName)
  }
}
