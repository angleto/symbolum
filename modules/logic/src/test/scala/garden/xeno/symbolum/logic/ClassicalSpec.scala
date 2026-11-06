package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The two axioms about the formalism, and everything derived from them.
 *
 * What is asserted here is two statements, so the part of this file that pins them is short and the
 * reading is the whole of the check. The rest measures what they buy, and the measurement that
 * matters most is which of the two each derived theorem reaches: the excluded middle reaches
 * `SELECT` and not `ETA`, which is the opposite of what this file said before eta landed.
 * `docs/adr/0007` is the record.
 */
class ClassicalSpec extends AnyFlatSpec with Matchers {


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

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val logic = classical.logic
  private val rules = logic.rules

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)

  "The classical extension" should "hold exactly the axioms below, printed as written" in {
    // The copy is written out by hand, as `RealSpec` writes out the sixteen, so a changed or added
    // axiom fails the build until the copy changes in the same commit. Comparing the theory with
    // its own list parsed again would pass any edit.
    //
    // **It was one until 2026-09-10 and it is two from here**, and the second is eta. Not because
    // the excluded middle wanted it, which is what the plan said and what the derivation below
    // refutes, but because `SUM_CONGRUENCE` in `Series` is an induction that exists only for the
    // want of it, and every operator that binds a variable was going to need its own. That is a
    // derivation in this repository paying for the absence, which is the justification
    // `docs/adr/0007` requires before an axiom lands.
    // The quotes arrived on 2026-09-12: both axioms are schemas over a type variable, and the
    // printer now writes one as `'a`, which is what the parser reads it back from.
    classical.theory.axioms.map(classical.show) shouldBe Vector(
      "!f:'a -> bool. !x:'a. f x ==> f (select f)",
      "!f:'a -> 'b. (\\x:'a. f x) = f"
    )

    // The letters are the printer's: bound variables have no name in the term, so the predicate the
    // source calls `P` prints as `x`. The two statements are the ones HOL Light calls `SELECT_AX`
    // and `ETA_AX`.
    force(classical.axiom(Classical.Choice)).hypotheses shouldBe empty
    force(classical.axiom(Classical.Eta)).hypotheses shouldBe empty
  }

  it should "leave the logic it was built over exactly as it was" in {
    // The reason this is an extension beside `Logic` and not a change to it: a development that
    // does not reach for the classical axioms does not carry them, and there are eight connectives
    // and a full set of derived rules below this line that never needed either.
    Logic.standard.theory.axioms shouldBe empty
    classical.theory.axioms.size shouldBe 2
  }

  it should "declare the operator at a schema a caller may instantiate" in {
    val atBool = force(classical.select(Type.Bool))
    val atFunction = force(classical.select(Type.fun(Type.Bool, Type.Bool)))

    Term.typeOf(atBool) shouldBe Type.fun(Type.fun(Type.Bool, Type.Bool), Type.Bool)
    Term.typeOf(atFunction) should not be Term.typeOf(atBool)
  }

  "Every derived theorem" should "arrive at the statement it was meant to arrive at" in {
    // What the kernel does not check. A derivation that reaches `!p. p \/ ~p \/ p` produces a
    // perfectly good theorem which is not the excluded middle, and nothing but a reader would
    // notice. So each statement is written out as text, parsed, and compared as a term: the
    // comparison is on terms rather than on printed strings, because the printer renames bound
    // variables and a test about its choice of letters would fail for the wrong reason.
    Classical.Statements.foreach { case (name, text) =>
      val theorem = force(classical.fact(name))

      withClue(s"$name printed as ${classical.show(theorem.conclusion)}\n") {
        classical.proposition(text) shouldBe Right(theorem.conclusion)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  it should "offer exactly these and nothing this file has not read" in {
    classical.facts.keySet shouldBe Classical.Statements.map(_._1).toSet
  }

  "The excluded middle" should "rest on choice alone, which the plan for it did not expect" in {
    // The most valuable line in this file. The brief for this change, and the note that stood in
    // `Classical.scala` before it, both said `p \/ ~p` was unreachable from choice because
    // Diaconescu's argument wants extensionality as well. It wants extensionality for the two
    // predicates it compares, and those are literal abstractions, so `Kernel.abs` supplies it: that
    // rule takes `s = t` to `(\x. s) = (\x. t)` and has been in the trusted base from the start.
    // What eta adds is functions that arrive as variables, which this argument never has.
    //
    // Measured rather than argued, and measured on the proof record rather than on the source: the
    // walk over the derivation turns up one axiom and it is choice.
    val middle = force(classical.fact(Classical.ExcludedMiddle))
    val eta = force(classical.axiom(Classical.Eta))
    val choice = force(classical.axiom(Classical.Choice))

    Derivation.axiomsOf(middle) shouldBe Set(choice.conclusion)
    Derivation.axiomsOf(middle) should not contain eta.conclusion
  }

  it should "hold at a compound proposition and not only at a variable" in {
    // The general theorem is derived once over a free variable and specialised per use, so this is
    // the check that the specialisation is a specialisation: a statement about `q /\ ~q` rather
    // than a second derivation.
    val compound = force(logic.mkConj(q, force(logic.mkNot(q))))
    val atCompound = force(classical.excludedMiddleAt(compound))

    classical.show(atCompound.conclusion) shouldBe "q /\\ ~q \\/ ~(q /\\ ~q)"
    atCompound.hypotheses shouldBe empty
  }

  it should "be refused at a term that is not a proposition" in {
    // A refusal by name rather than a kernel type error several steps in.
    classical.excludedMiddleAt(Term.variable("n", TyVar("a"))) match {
      case Left(NotOfForm(expected, _)) => expected should include("proposition")
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  "What each derivation reaches" should "divide over choice and eta exactly where the mathematics says" in {
    // The picture the proof record draws of this whole file, and it is the right one. Two of the
    // six statements were always available and are collected here rather than bought; eta pays for
    // one of them and choice for the other three. Nothing reaches both, which is worth knowing:
    // the two axioms are independent purchases and a development could take either alone.
    def reaches(name: String): Set[Term] = Derivation.axiomsOf(force(classical.fact(name)))

    val choice = force(classical.axiom(Classical.Choice)).conclusion
    val eta = force(classical.axiom(Classical.Eta)).conclusion

    reaches(Classical.TruthNotFalsity) shouldBe empty
    reaches(Classical.DeMorganDisjunction) shouldBe empty
    reaches(Classical.FunctionExtensionality) shouldBe Set(eta)
    reaches(Classical.ExcludedMiddle) shouldBe Set(choice)
    reaches(Classical.DoubleNegation) shouldBe Set(choice)
    reaches(Classical.DeMorganConjunction) shouldBe Set(choice)

    // The two conditional equations are on choice's side of the same line, and that they reach
    // nothing else is the interesting half: the obvious proof of them is a case split, which would
    // put the excluded middle's derivation inside each of them and would still reach only `SELECT`
    // while costing several times as much. These go to the axiom directly.
    reaches(Classical.CondTrue) shouldBe Set(choice)
    reaches(Classical.CondFalse) shouldBe Set(choice)
  }

  it should "be the same division read from the sizes, which is where a silent regression shows" in {
    // Not a performance test. A derivation that quietly started going through a rewriter, or that
    // lost the sharing between the two disjunction eliminations, would still prove the same theorem
    // and would show up here first.
    //
    // The figures are `Derivation.size`, remeasured on 2026-09-11 when `Conv.refl` began sharing
    // the reflexivity of an atom instead of building one per use: 153, 242 and 983 became 122, 197
    // and 829, which is a sixth of each derivation gone. They moved because the work stopped being
    // done, and they are pinned exactly rather than bounded so that the next time they move
    // somebody has to say which way and why.
    //
    // The excluded middle moved again on 2026-09-16, 829 to 841, and this is that saying. `Rules.mp`
    // stopped accepting an antecedent that differs from the implication's by a beta redex and
    // started **converting** it, which costs three kernel steps each time. Diaconescu's argument
    // reaches choice twice, so it pays twice. The twelve steps buy the rule refusing an antecedent
    // that proves something else, which it used to accept while leaving the undischarged
    // antecedent on the left of the turnstile where only `thm.hypotheses` would show it.
    val sizes = Classical.Statements.map { case (name, _) =>
      name -> Derivation.size(force(classical.fact(name)))
    }.toMap

    sizes(Classical.TruthNotFalsity) shouldBe 122
    sizes(Classical.FunctionExtensionality) shouldBe 197
    sizes(Classical.ExcludedMiddle) shouldBe 841

    // The two conditional equations, measured on 2026-09-12 when they landed. They are pinned for
    // the same reason the three above are: both go through `chosenSatisfies` and a change that made
    // that stop sharing the choice instance between them would prove the same theorems and would
    // show here first.
    //
    // 476 until 2026-09-16, and the six they gained is the same six the excluded middle gained
    // twice: `chosenSatisfies` reaches choice once, and `Rules.mp` now converts the unreduced
    // application the axiom states into the reduct the caller assumed, where it used to leave the
    // difference standing as a hypothesis. Both moved by exactly six, which is what says the
    // sharing this pin watches is still happening.
    sizes(Classical.CondTrue) shouldBe 482
    sizes(Classical.CondFalse) shouldBe 482

    // De Morgan for the universal quantifier, measured when it landed on 2026-09-15. It is above
    // the excluded middle for the reason the two lines below give: it uses the double negation
    // twice, and each use carries the whole of that derivation.
    sizes(Classical.NotForall) shouldBe 1155

    // The excluded middle is the expensive one and everything classical below it pays that cost
    // again, which is what saying it is derived rather than asserted means.
    sizes(Classical.DoubleNegation) should be > sizes(Classical.ExcludedMiddle)
    sizes(Classical.DeMorganConjunction) should be > sizes(Classical.DeMorganDisjunction)
  }

  "Function extensionality" should "be derived from the smaller statement, not asserted as the larger" in {
    // What asserting eta rather than the pointwise form buys, and the reason the trade is worth
    // making: the axiom a reader checks is four symbols long and the statement callers use is the
    // one they wanted. Upstream makes the same trade.
    val extensionality = force(classical.fact(Classical.FunctionExtensionality))

    classical.show(extensionality.conclusion) shouldBe
      "!f:'a -> 'b. !g:'a -> 'b. (!x:'a. f x = g x) ==> f = g"

    Classical.Axioms.map(_._1) should not contain Classical.FunctionExtensionality
  }

  it should "work as a rule at a concrete type, which is what a caller has" in {
    // The theorem is over type variables and a derivation is over `bool`, `num` or `real`, so the
    // rule instantiates two types and two functions before it detaches. Every caller would write
    // the same four lines.
    val f = Term.variable("f", Type.fun(Type.Bool, Type.Bool))
    val g = Term.variable("g", Type.fun(Type.Bool, Type.Bool))

    val atF = force(LogicError.lift(Term.app(f, p)))
    val atG = force(LogicError.lift(Term.app(g, p)))
    val pointwise = force(logic.mkForall(p, force(LogicError.lift(Term.eq(atF, atG)))))
    val assumed = force(LogicError.lift(Kernel.assume(pointwise)))

    val equal = force(classical.ext(assumed))

    classical.show(equal.conclusion) shouldBe "f = g"
    // The hypothesis is carried rather than discharged, which is what makes it a rule usable in the
    // middle of a derivation: the caller discharges it when they are ready to.
    equal.hypotheses.map(classical.show) shouldBe List("!p:bool. f p = g p")
  }

  it should "refuse a body that is not an application of two functions to the variable" in {
    // The refusal that matters. `!x. f x = c` is a true statement of a shape eta cannot close, and
    // a rule that closed it anyway would produce a theorem about `\x. c` rather than about `c`.
    val body = force(LogicError.lift(Term.eq(logic.truth, logic.truth)))
    val pointwise = force(logic.mkForall(p, body))
    val assumed = force(LogicError.lift(Kernel.assume(pointwise)))

    classical.ext(assumed) match {
      case Left(NotOfForm(expected, _)) => expected should include("application")
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  it should "refuse a theorem that is not a quantification at all" in {
    classical.ext(Kernel.refl(logic.truth)) match {
      case Left(NotOfForm(expected, _)) => expected should include("universal")
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  "The case split" should "close a goal proved on both sides of a proposition" in {
    // The rule the classical axioms are worth their cost for, and the one every tactic will want.
    // Until the excluded middle was derived, the theory of the reals was the only supplier of a
    // case split in this system: `LT_TOTAL` gave a disjunction about an order and there was nothing
    // at all for a proposition.
    val notP = force(logic.mkNot(p))
    val goal = force(logic.mkDisj(p, notP))

    val positive = force(rules.disjIntro1(notP, force(LogicError.lift(Kernel.assume(p)))))
    val negative = force(rules.disjIntro2(p, force(LogicError.lift(Kernel.assume(notP)))))

    val proved = force(classical.cases(p, positive, negative))

    proved.conclusion shouldBe goal
    // Both branches discharged, so the two assumptions are gone and nothing is left.
    proved.hypotheses shouldBe empty
  }

  it should "refuse two branches that prove different things" in {
    // `Rules.disjElim`'s check, arriving through this rule rather than being repeated in it.
    val notP = force(logic.mkNot(p))
    val positive = force(LogicError.lift(Kernel.assume(p)))
    val negative = force(LogicError.lift(Kernel.assume(notP)))

    classical.cases(p, positive, negative) match {
      case Left(NotOfForm(_, _)) => succeed
      case other => fail(s"expected a refusal about the two conclusions, got $other")
    }
  }

  "Proof by contradiction" should "conclude a proposition from the absurdity of its negation" in {
    // The direction this logic could not reach. `Rules.falsityElim` gives anything from falsity and
    // is intuitionistic; this gives `p` from `~p` being impossible and is not.
    val notQ = force(logic.mkNot(q))
    val target = force(logic.mkDisj(q, notQ))
    val negation = force(logic.mkNot(target))

    val assumedNegation = force(LogicError.lift(Kernel.assume(negation)))
    val absurd = force(rules.notElim(assumedNegation, force(classical.excludedMiddleAt(q))))

    val proved = force(classical.contradiction(target, absurd))

    proved.conclusion shouldBe target
    proved.hypotheses shouldBe empty
  }

  it should "be refused when what it is handed does not prove falsity" in {
    classical.contradiction(p, Kernel.refl(logic.truth)) match {
      case Left(NotOfForm(expected, _)) => expected should include("falsity")
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  "De Morgan" should "hold both ways, and only one of the two needs an axiom" in {
    // Asked for as a pair and delivered as a pair, and then measured, because the pair is not
    // symmetric: from `~(p /\ q)` nothing intuitionistic says which of the two fails, and from
    // `~(p \/ q)` both follow directly. The second is here rather than in `Logic` only because a
    // reader looking for De Morgan should find both in one place.
    classical.show(force(classical.fact(Classical.DeMorganDisjunction)).conclusion) shouldBe
      "!p:bool. !q:bool. (~(p \\/ q)) = (~p /\\ ~q)"
    classical.show(force(classical.fact(Classical.DeMorganConjunction)).conclusion) shouldBe
      "!p:bool. !q:bool. (~(p /\\ q)) = (~p \\/ ~q)"

    Derivation.axiomsOf(force(classical.fact(Classical.DeMorganDisjunction))) shouldBe empty
    Derivation.axiomsOf(force(classical.fact(Classical.DeMorganConjunction))) should have size 1
  }

  "A witness that exists" should "be named, which is what the naturals need" in {
    // The derivation the choice axiom is for. `Kernel.defineType` wants a closed predicate, and
    // eliminating an existential gives a variable; this turns `something satisfies P` into a term
    // that does.
    val boolVariable = Term.variable("p", Type.Bool)
    val predicate =
      lam(boolVariable, force(LogicError.lift(Term.eq(boolVariable, logic.truth))))

    val instance = force(LogicError.lift(Term.eq(logic.truth, logic.truth)))
    val proved = Kernel.refl(logic.truth)
    val exists = force(rules.existsIntro(predicate, logic.truth, proved))

    val named = force(classical.witness(exists))

    named.hypotheses shouldBe empty

    // The unreduced application, and that is the point rather than an untidiness.
    // `Kernel.defineType` reads the predicate off the outermost application of its witness, so this
    // shape hands it `\x. x = T`, the predicate the caller meant. Reduced to `select ... = T` it
    // would hand over `(= (select ...))`, the predicate that holds of that one term: the first
    // defines the type asked for and the second defines a singleton.
    classical.show(named.conclusion) shouldBe
      "(\\p:bool. p = T) (select (\\p:bool. p = T))"

    named.conclusion match {
      case App(carried, chosen) =>
        carried shouldBe predicate
        classical.show(chosen) shouldBe "select (\\p:bool. p = T)"
      case other => fail(s"expected an application, got $other")
    }

    // And it says what it was supposed to say: reducing it gives the instance.
    val reduced = force(Conv.betaRoot(named.conclusion).flatMap(_ => Right(named.conclusion)))
    reduced shouldBe named.conclusion
    instance should not be named.conclusion
  }

  it should "be refused when the theorem is not an existential" in {
    // The refusal that keeps a caller from reading a witness out of something that is not one.
    classical.witness(Kernel.refl(logic.truth)) match {
      case Left(NotOfForm(expected, _)) => expected should include("existential")
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  /* ------------------------------------------------------------------ the conditional */

  "The conditional" should "be defined rather than assumed, so the trusted base does not move" in {
    // The whole claim the card makes about what `COND` costs. It is a constant in the signature and
    // a row in `docs/reading-register.md`, and it is not an axiom: the choice operator already in
    // this file is what names the value, so nothing new is believed.
    classical.theory.definitions.keySet should contain(Classical.Conditional)
    classical.theory.axioms.size shouldBe 2

    val defining = force(classical.definition(Classical.Conditional))
    defining.hypotheses shouldBe empty
    classical.show(defining.conclusion) shouldBe
      "COND = (\\p:bool. \\x:'a. \\y:'a. select (\\z:'a. (p ==> z = x) /\\ (~p ==> z = y)))"
  }

  it should "be declared at a schema over the type of its two branches" in {
    val atBool = force(classical.conditional(Type.Bool))
    val atFunction = force(classical.conditional(Type.fun(Type.Bool, Type.Bool)))

    Term.typeOf(atBool) shouldBe
      Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))
    Term.typeOf(atFunction) should not be Term.typeOf(atBool)
  }

  it should "be written as an application, since it was given no spelling of its own" in {
    // The precedence decision, asserted rather than described: `COND` has no row in the table and is
    // read and printed at application precedence like any other constant. The round trip is what
    // makes that a decision somebody can live with rather than a gap, so it is the thing checked.
    val term = force(classical.term("COND (p /\\ q) p q"))

    classical.show(term) shouldBe "COND (p /\\ q) p q"
    classical.term(classical.show(term)) shouldBe Right(term)

    classical.notation.infixOf(Classical.Conditional) shouldBe None
    classical.notation.prefixOf(Classical.Conditional) shouldBe None
    classical.notation.binderOf(Classical.Conditional) shouldBe None
  }

  it should "settle a conditional at a condition that is decided, which is what a caller does" in {
    // End to end rather than by the statement of the lemma: a caller holds a proof of the condition
    // and wants the branch. `T` is the condition that is provable with nothing, so this is the
    // shortest such caller there is, and what comes back is an equation with no hypotheses.
    val a = Term.variable("a", Type.Bool)
    val b = Term.variable("b", Type.Bool)

    val equation = force(
      for {
        general <- classical.fact(Classical.CondTrue)
        instantiated <- Right(Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), general))
        atArguments <- rules.specAll(instantiated, List(logic.truth, a, b))
        isTruth <- logic.rules.truth
        settled <- rules.mp(atArguments, isTruth)
      } yield settled
    )

    classical.show(equation.conclusion) shouldBe "COND T a b = a"
    equation.hypotheses shouldBe empty
  }

  it should "take the other branch when the condition is refuted" in {
    val a = Term.variable("a", Type.Bool)
    val b = Term.variable("b", Type.Bool)

    val equation = force(
      for {
        general <- classical.fact(Classical.CondFalse)
        instantiated <- Right(Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), general))
        atArguments <- rules.specAll(instantiated, List(logic.falsity, a, b))
        assumed <- LogicError.lift(Kernel.assume(logic.falsity))
        refuted <- rules.notIntro(logic.falsity, assumed)
        settled <- rules.mp(atArguments, refuted)
      } yield settled
    )

    classical.show(equation.conclusion) shouldBe "COND F a b = b"
    equation.hypotheses shouldBe empty
  }

  it should "say nothing at all about a condition nobody has settled" in {
    // The refusal that is not a refusal but a shape, and the reason it belongs in a test: `COND` is
    // total, so `COND p a b` is a perfectly good term at an undecided `p`, and neither equation
    // detaches. A reader who expects a conditional to evaluate has to meet that here rather than in
    // a tactic that silently picks a branch.
    val a = Term.variable("a", Type.Bool)
    val b = Term.variable("b", Type.Bool)

    val general = force(classical.fact(Classical.CondTrue))
    val instantiated = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), general)
    val atArguments = force(rules.specAll(instantiated, List(p, a, b)))

    classical.show(atArguments.conclusion) shouldBe "p ==> COND p a b = a"

    // And there is no way to get the branch without a proof of `p`. **Which outcome that is
    // changed on 2026-09-16 and the old one is worth stating, because this test was written to
    // pin it.** `Rules.mp` was a cut that did not check what it was handed, so detaching against
    // something else did not refuse: it left `p` standing as a hypothesis, which is honest and is
    // not an equation anybody may use, and only `thm.hypotheses` ever showed it. It refuses now,
    // so the two outcomes this test distinguishes are "refused" and "answered", where they used to
    // be "refused" and "answered under an assumption".
    val notDetached = rules.mp(atArguments, Kernel.refl(logic.truth))

    notDetached.left.map(_.getClass) shouldBe Left(classOf[NotOfForm])

    // Naming what it was handed, or this passes against a rule that refuses everything.
    notDetached.fold(_.message, _ => "") should include("T")

    // The branch is still reachable with a real proof of the condition, which is what says the
    // refusal above is about the mismatch and not about `COND` having stopped working.
    val assumed = force(LogicError.lift(Kernel.assume(p)))
    classical.show(force(rules.mp(atArguments, assumed)).conclusion) shouldBe "COND p a b = a"
  }

  "The source" should "name the one operation that asserts an axiom, and no other file in this module" in {
    // The same scan `RealSpec` runs, kept here as well because this module had no axiom at all
    // before and the property that it has exactly one file with them is worth failing on.
    //
    // **This is the assertion that did not move when the second axiom landed**, and that is the
    // point of it being separate from the count above: eta went into the file choice was already
    // in, so what has to be believed grew and the set of places it can grow from did not. A third
    // axiom in a third file would fail here instead.
    val naming = java.nio.file.Files
      .walk(java.nio.file.Paths.get("modules/logic/src/main"))
      .filter(path => path.toString.endsWith(".scala"))
      .filter(path => java.nio.file.Files.readString(path).contains("assertAxiom"))
      .map[String](path => path.getFileName.toString)
      .sorted()
      .toArray
      .toVector

    naming shouldBe Vector("Classical.scala")
  }

  /* --------------------------------------------- the figures quoted outside this file */

  "The step counts quoted in prose" should "be spelled from the derivations, wherever they are written" in {
    // The repair the card `49e8dab4` asks for, at the places a table cannot reach. A figure inside
    // a sentence cannot be generated, so it is bound instead: the number is read off the derivation
    // here and the sentence is searched for with it already substituted, which fails in both
    // directions rather than only when the document drops a name.
    //
    // These four sentences were all stale on 2026-09-11 and all four were found by hand with
    // `grep`. The excluded middle's own file said one number, `AGENTS.md` said the same one, and
    // `Classical.scala` said a third that was two repairs out of date.
    // Read with the line breaks taken out, because a sentence in a document is wrapped where the
    // column ran out and a figure lands on either side of that break with no warning. The first
    // version of this test asserted against the file as written and failed on a sentence that says
    // exactly what it should, which is a test failing on typography.
    def read(relative: String): String =
      java.nio.file.Files
        .readString(java.nio.file.Paths.get(relative))
        .replaceAll("\\s+", " ")

    def size(name: String): Int = Derivation.size(force(classical.fact(name)))

    val excludedMiddle = size(Classical.ExcludedMiddle)
    val truthNotFalsity = size(Classical.TruthNotFalsity)
    val largest = Classical.Statements.map { case (name, _) => size(name) }.max

    val guide = read("docs/proving.md")
    withClue(s"docs/proving.md does not say the excluded middle is $excludedMiddle steps: ") {
      guide should include(s"$excludedMiddle inference steps by `Derivation.size`")
    }
    withClue(s"docs/proving.md does not say `TRUTH_NOT_FALSITY` is $truthNotFalsity steps: ") {
      guide should include(s"that is $truthNotFalsity steps and no axiom at all")
    }

    withClue(s"AGENTS.md does not say the excluded middle is $excludedMiddle steps: ") {
      read("AGENTS.md") should include(s"in $excludedMiddle steps")
    }

    val logicFile = read("modules/logic/src/main/scala/garden/xeno/symbolum/logic/Logic.scala")
    withClue(s"Logic.scala does not say the excluded middle is $excludedMiddle steps: ") {
      logicFile should include(s"in $excludedMiddle steps")
    }

    val classicalFile = read("modules/logic/src/main/scala/garden/xeno/symbolum/logic/Classical.scala")
    // The count in that sentence is a WORD and cannot be spliced from the derivations, so it is
    // pinned here instead: one more derived fact fails this line and names the number the places
    // in `Classical.scala` that spell it have to be changed to. It said "eight" until
    // `NOT_FORALL` landed on 2026-09-15.
    Classical.Statements.size shouldBe 9
    withClue(s"Classical.scala does not say the largest of the nine is $largest steps: ") {
      classicalFile should include(s"of the nine is $largest inference steps")
    }

    // And the table itself is gone from that file rather than kept in step with the document: two
    // copies of one measurement is the defect, not the fact that they disagreed.
    classicalFile should not include "EXCLUDED_MIDDLE          |-"
  }

  it should "be written out nowhere the test above does not reach, which is the half it was missing" in {
    // **The gate above is a list of sentences, and a list only covers what somebody put on it.**
    // Card `ad47e293` was opened on the reading that nothing guarded the excluded middle's count
    // at all, which is false and is worth recording as the instrument's failure rather than the
    // reader's: that card was written from `git grep 841`, and the test above spells the figure
    // from the derivation instead of writing it, so a grep for the digits cannot see the guard
    // that covers them. An absence an instrument reports is not an absence until the instrument
    // has been seen finding something.
    //
    // What the card was right about is the half a list cannot have. Counted on 2026-09-22, the
    // figure stood at fifteen places: three inside generated regions, which `GuideSpec` and
    // `TheoremsSpec` compare against the derivation; the pin below; two DATED sentences about a
    // past move, which do not go stale when the figure moves again; three covered by the list
    // above; and **six that nothing watched**. Those six are gone, and this is what stops a
    // seventh: a copy written into a source or a document is caught here whether or not anybody
    // adds it to that list.
    //
    // Two of the six are worth naming. `Theorems.Showcase` carried it in a literal that a
    // GENERATED page is built from, twenty-eight lines above the same count printed by `Essay`
    // from `Derivation.size`: `TheoremsSpec` compares the page with its generator, and the
    // generator embeds the literal, so both sides would have moved together and the page would
    // have come to disagree with itself with every gate green. And `docs/adr/0009` carried it in
    // the present tense inside a dated record, which is the one place a moving figure should
    // never be.
    val digits = Derivation.size(force(classical.fact(Classical.ExcludedMiddle))).toString

    // Bounded on both sides, so the digits inside a longer number are not a match. Such numbers
    // exist, and every one of them is in `ArbitrarySpec`'s decimal expansions of pi and of the
    // sine of one.
    val standalone = s"(?<![0-9])$digits(?![0-9])".r

    // What may carry it, and the SENTENCES in each that may, read with the line breaks taken out
    // as the test above reads them. Until 2026-09-24 this was a set of files, and the verification
    // of card `ad47e293` measured what that cost: a second live sentence written into `AGENTS.md`
    // or `docs/proving.md` stayed green, because a carrier was exempt as a whole. A sentence here
    // is removed from its file before the search, ONCE for each time it is listed, so the file
    // may hold these and nothing else: the first version of this removed every occurrence, and the
    // assertion below that a second live sentence is found went red on it, because a second
    // sentence ending `in 841 steps` was exempted by the first one's entry.
    //
    // Each is one of the readings above. The live ones are the sentences the test above asserts,
    // the generated ones are compared against the derivation by `GuideSpec` and `TheoremsSpec`, and
    // the rest of `AGENTS.md` names the figure as the SUBJECT of a lesson about finding it, which
    // is a dated account and not a count. Every entry is a copy this assertion has stopped
    // watching, so adding one is how the repair comes undone.
    val carriers: Map[String, Vector[String]] = Map(
      "AGENTS.md" -> Vector(
        s"in $digits steps", // the live sentence, asserted by the test above
        s"829 to $digits on 2026-09-16", // a dated move
        s"`git grep $digits`", // the instrument a card was opened with, named twice
        s"`git grep $digits`",
        s"the sites of `$digits`",
        s"guards `$digits` by spelling it"),
      "docs/proving.md" -> Vector(
        s"$digits inference steps by `Derivation.size`", // live, asserted above
        s"| `SELECT` | $digits |"), // the generated table, `GuideSpec`
      "docs/theorems.md" -> Vector(
        s"$digits inferences of its own, a published fact it uses"), // generated, `TheoremsSpec`
      "modules/logic/src/main/scala/garden/xeno/symbolum/logic/Logic.scala" -> Vector(
        s"in $digits steps")) // live, asserted above

    def uncovered(path: String): Boolean = {
      val flowed = ClassicalSpec.contentsOf(path).replaceAll("\\s+", " ")
      val left = carriers.getOrElse(path, Vector.empty).foldLeft(flowed)(ClassicalSpec.removeOnce)
      standalone.findFirstIn(left).isDefined
    }

    // This file is the one carrier exempt as a whole, and only because it is where the figure is
    // pinned and where the history of the pin is told: a copy here is read by whoever edits the
    // pin, which is not true of any other file.
    val self = "modules/logic/src/test/scala/garden/xeno/symbolum/logic/ClassicalSpec.scala"
    val scanned =
      (ClassicalSpec.everyDocument ++ ClassicalSpec.everyModuleSource).filterNot(_ == self)

    val spread = scanned.filter(uncovered)

    withClue(s"writing $digits out where the derivation should be named instead: ${spread.mkString(", ")}\n") {
      spread shouldBe empty
    }

    // Not vacuous, which is the whole lesson of the card this answers: an absence reported by an
    // instrument that read nothing looks exactly like an absence reported by one that read
    // everything. The walk must reach the modules, and it must find the figure where the figure
    // legitimately lives.
    withClue("the walk over the modules found no sources: ") {
      ClassicalSpec.everyModuleSource.size should be > 100
    }
    standalone.findFirstIn(ClassicalSpec.contentsOf(
      "modules/logic/src/main/scala/garden/xeno/symbolum/logic/Logic.scala")) shouldBe defined

    // And the walk over the documents reaches the two the list of three did not, which is where
    // the verification of 2026-09-24 put a copy and saw this stay green.
    withClue("the walk over the documents missed a file the old list missed: ") {
      ClassicalSpec.everyDocument should contain("docs/numerics.md")
      ClassicalSpec.everyDocument.exists(_.startsWith("docs/adr/0009")) shouldBe true
      ClassicalSpec.everyDocument.size should be > 50
    }

    // And a sentence exemption removes that sentence and not the file: text holding every
    // exempted sentence of `AGENTS.md` once, and the live one a second time, still holds the
    // figure. Built from the entries rather than read from the file, so that this half stays green
    // when the list above goes red on a drifted sentence and the two are seen failing apart.
    val exempted = carriers("AGENTS.md")
    val twice = (exempted :+ s"derived in $digits steps").mkString(" ")
    standalone.findFirstIn(exempted.foldLeft(twice)(ClassicalSpec.removeOnce)) shouldBe defined

    // **What it does not cover.** It searches for the digits, so on the day the derivation moves
    // to a count some unrelated line happens to hold, this goes red on a file that is not a copy;
    // the failure names the file and the answer is a row in `carriers` with its reason, which is
    // the arrangement `NotationBoundarySpec` already runs for interpolated prose. It reads
    // the Scala of `modules/` and every document on disk outside the directories git ignores, so
    // a figure written into a script under `tools/` is outside it —
    // `tools/verify/perturb-the-figure-the-code-knows.sh` names the bytes it substitutes and is
    // one. A figure that moves also leaves a dated entry above matching nothing, which is harmless:
    // the entry removes nothing, and it is read by whoever looks at why the list says what it says.
  }
}

private object ClassicalSpec {

  /**
   * Every Scala source of every module, main and test, relative to the repository root.
   *
   * Found by asking the disk rather than from a list, so a module added later is inside the scan
   * without anybody remembering to add it. The test scope is walked as well as the main one,
   * because two of the copies this was written for were in specs.
   */
  lazy val everyModuleSource: Vector[String] = {
    val root = java.nio.file.Paths.get("modules")
    val modules = java.nio.file.Files.list(root)
    val roots =
      try {
        val iterator = modules.iterator
        Iterator.continually(iterator).takeWhile(_.hasNext).map(_.next()).toVector.sortBy(_.toString)
      } finally modules.close()

    roots.flatMap { module =>
      Vector("src/main", "src/test")
        .map(module.resolve)
        .filter(java.nio.file.Files.isDirectory(_))
        .flatMap { source =>
          val stream = java.nio.file.Files.walk(source)
          try {
            val iterator = stream.iterator
            Iterator
              .continually(iterator)
              .takeWhile(_.hasNext)
              .map(_.next())
              .toVector
              .filter(path =>
                java.nio.file.Files.isRegularFile(path) && path.toString.endsWith(".scala"))
              .map(_.toString)
          } finally stream.close()
        }
    }
  }

  /**
   * Every document of the repository, relative to its root: every `.md` on disk.
   *
   * Asked of the disk for the reason [[everyModuleSource]] is, and it replaced a list of three on
   * 2026-09-24. What it skips is what git ignores and a session writes into: `scratch/` and
   * `private/`, which hold other sessions' probes on a shared checkout, the build's `target/`
   * directories, and every directory whose name starts with a dot. Measured that day, what is left
   * is exactly the tracked documents except `scratch/README.md`, which sits in an ignored directory
   * and says what the directory is for.
   */
  lazy val everyDocument: Vector[String] = {
    import java.nio.file.{FileVisitResult, Files, Path, Paths, SimpleFileVisitor}
    import java.nio.file.attribute.BasicFileAttributes

    val root = Paths.get("").toAbsolutePath
    val skipped = Set("scratch", "private", "target", "node_modules")
    val found = Vector.newBuilder[String]

    // A visitor and not `Files.walk`, so that `target/` and `.git/` are never descended into
    // rather than walked and then filtered: the first is the build's and the second is large.
    Files.walkFileTree(
      root,
      new SimpleFileVisitor[Path] {
        override def preVisitDirectory(
          dir: Path,
          attributes: BasicFileAttributes
        ): FileVisitResult = {
          val name = Option(dir.getFileName).map(_.toString).getOrElse("")
          if (dir != root && (name.startsWith(".") || skipped.contains(name)))
            FileVisitResult.SKIP_SUBTREE
          else FileVisitResult.CONTINUE
        }

        override def visitFile(file: Path, attributes: BasicFileAttributes): FileVisitResult = {
          if (attributes.isRegularFile && file.getFileName.toString.endsWith(".md"))
            found += root.relativize(file).toString
          FileVisitResult.CONTINUE
        }
      }
    )
    found.result().sorted
  }

  /** `text` with the first occurrence of `fragment` taken out, and unchanged where there is none. */
  def removeOnce(text: String, fragment: String): String = {
    val at = text.indexOf(fragment)
    if (at < 0) text else text.substring(0, at) + text.substring(at + fragment.length)
  }

  def contentsOf(relative: String): String =
    java.nio.file.Files.readString(java.nio.file.Paths.get(relative))
}
