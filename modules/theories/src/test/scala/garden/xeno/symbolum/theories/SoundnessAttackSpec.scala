package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.{Conv, Logic, Rules}

/**
 * The attack that made this kernel unsound, kept as a test that it no longer works.
 *
 * A case class hands out its fields, and pattern matching on a binder cannot be taken away because
 * the printer, the matcher and the rewriter all need it. So a caller outside the kernel can hold a
 * term whose index has lost its binder. That was harmless only as long as nothing accepted one,
 * and everything accepted one: substitution and beta move terms across binders without shifting,
 * precisely because they were entitled to assume no such term existed.
 *
 * The full derivation, which ran before the fix and is reproduced step by step below:
 *
 * {{{
 * 2. |- (\x. h) v = h                          a legitimate beta step
 * 3. |- (\x. f x) v = f ?0                     inst h := (f ?0), captured on the left only
 * 4. |- (\x. (\y. f y) v) = (\x. f x)          abs w, capturing the index on the right
 * 5. apply both sides, reduce, instantiate f   two different functions proved equal
 * }}}
 *
 * Found by an adversarial audit, not by use, and not by any test that existed at the time.
 *
 * == The corpus, and its score ==
 *
 * Track K of `docs/evaluation.md` asks for the adversarial cases as one artifact with a score
 * rather than as assertions spread over several files, and [[Corpus]] below is that artifact. Each
 * entry names the attack, where it came from, and whether the kernel must turn it away or take it,
 * and one test runs the lot and reports the counts. The must-accept half is not decoration: a rule
 * whose refusals are all correct and whose product is unusable passes every must-reject row there
 * is, and nothing else in the file would notice.
 *
 * **What the corpus does not hold, and where those live.** Four cases from the historical record
 * are tested as a rule's contract rather than as an attack, and their home is the kernel's own
 * suite: abstraction over a variable free in a hypothesis and `eqMp` between sides that are not the
 * same term, both in `KernelSpec`, the behaviour of `instType` under a substitution that could
 * collide, also there, and a definition whose type variables escape, in `TheorySpec`. They are
 * named here rather than copied here, because a second copy of a test is a defect while the two
 * agree and this file would be the copy.
 *
 * **And what neither holds.** This is not coverage. It is the attacks that occurred to the people
 * who wrote them, and the 2026-09-03 defect is the standing evidence that such a corpus proves only
 * what it contains: it survived `docs/architecture.md`, `TrustBoundarySpec`, `IsolationSpec` and
 * 251 tests.
 */
class SoundnessAttackSpec extends AnyFlatSpec with Matchers {


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

  private def force[E, T](r: Either[E, T]): T = r.fold(e => fail(s"unexpected refusal: $e"), identity)
  private val real = TyApp(Real.TypeName, Nil)

  private val f = Term.variable("f", Type.fun(real, real))
  private val v = Term.variable("v", real)
  private val h = Term.variable("h", real)

  /** The term with a loose index, obtained the only way it can be: by destructuring a lambda. */
  private val loose: Term =
    lam(v, force(Term.app(f, v))) match {
      case Abs(_, body) => body
      case other => fail(s"expected an abstraction, got $other")
    }

  "A destructured binder body" should "still be obtainable, since pattern matching stays public" in {
    Term.isLocallyClosed(loose) shouldBe false
  }

  /* -------------------------------------------------- what a verdict alone cannot say */

  it should "read the predicate from the theorem, so no other one can be smuggled beside it" in {
    // Structural rather than checked, and worth pinning as such: the signature takes a theorem and
    // not a predicate, so `P` is whatever the witness applies. A rule that accepted both would have
    // to compare them, and comparing them is the check nobody would notice was missing.
    val ind = TyApp("ind", Nil)
    val theory = force(
      for {
        withInd <- Theory.primitive.declareTypeOperator("ind", 0)
        withP <- withInd.declareConstant("P", Type.fun(ind, Type.Bool))
        withW <- withP.declareConstant("w", ind)
      } yield withW
    )
    val predicate = force(theory.constant("P", Type.fun(ind, Type.Bool)))
    val applied = force(Term.app(predicate, force(theory.constant("w", ind))))
    val (asserted, witness) = force(Kernel.assertAxiom(theory, applied))

    val (_, (_, characterises)) = force(Kernel.defineType(asserted, "sub", "abs", "rep", witness))

    // The predicate in the theorem that comes back is the one the witness carried, and the only way
    // to change it is to supply a different witness, which is a different theorem.
    Term.destEq(characterises.conclusion).map(_._1) match {
      case Some(App(carried, _)) => carried shouldBe predicate
      case other => fail(s"expected the predicate applied, got $other")
    }
  }

  /* --------------------------------------------------- the hole that is known and open */

  "Two theories that define one name differently" should "no longer combine, since 2026-09-10" in {
    // This derived `|- T = F` with no hypotheses until `docs/adr/0008`, and both halves were
    // theorems the kernel was right to produce: each theory is a conservative extension of the
    // logic, each is consistent, and `defineConstant` refuses a name only within one theory. It was
    // the limitation `Kernel`'s comment named, pinned here rather than described.
    //
    // A constant carries the term that defined it now, so the two `c`s are different terms and the
    // chaining is refused by the rule that compares them. Nothing was added to any rule.
    val logic = Logic.standard

    val asTruth = force(Kernel.defineConstant(logic.theory, "c", logic.truth))._2
    val asFalsity = force(Kernel.defineConstant(logic.theory, "c", logic.falsity))._2

    // Both still hold, and they still print alike, which is the cost the record names: the identity
    // is structural and the spelling cannot show it.
    asTruth.display shouldBe "|- (c = T)"
    asFalsity.display shouldBe "|- (c = F)"

    val mixed = for {
      flipped <- Conv.sym(asTruth)
      joined <- Conv.trans(flipped, asFalsity)
    } yield joined

    mixed match {
      case Left(error) =>
        // The refusal has to say why, because this is the one difference the spelling cannot show:
        // without the clause the message reads `c is not c`, which tells a caller nothing.
        error.message should include("different definitions")
      case Right(theorem) => fail(s"expected the two chains not to combine, got ${theorem.display}")
    }
  }

  it should "still combine when the two definitions agree, since then it is one constant" in {
    // The other half, and the one a check that refused everything would pass. Two theories that
    // define a name the same way are talking about the same thing, so their theorems chain.
    val logic = Logic.standard

    val here = force(Kernel.defineConstant(logic.theory, "c", logic.truth))._2
    val there = force(Kernel.defineConstant(logic.theory, "c", logic.truth))._2

    val joined = for {
      flipped <- Conv.sym(here)
      result <- Conv.trans(flipped, there)
    } yield result

    joined.map(_.display) shouldBe Right("|- (T = T)")
  }

  it should "refuse a declared constant where a defined one is meant, which is the conservative side" in {
    // Named because a caller will meet it. A theorem about an uninterpreted `c` holds under every
    // interpretation, including the one that defines it, so this refuses an inference that would
    // have been valid. That is the price of the identity being the definition, and it falls on the
    // safe side.
    val logic = Logic.standard

    val declared = force(logic.theory.declareConstant("c", Type.Bool))
    val loose = force(declared.constant("c", Type.Bool))
    val defined = force(Kernel.defineConstant(logic.theory, "c", logic.truth))._2

    Kernel.trans(Kernel.refl(loose), defined).isLeft shouldBe true
  }

  /* ------------------------------------------------------------- the corpus, and its score */

  /**
   * What an entry expects, which is the refusal by name rather than the fact of one.
   *
   * A corpus that recorded only refused-or-taken would pass on a kernel that turned every attack
   * away for the wrong reason, and turning something away for the wrong reason is how a check that
   * has stopped working looks from outside. So a row carries the error it must come back with, and
   * [[Taken]] is the one value that is not an error.
   */
  private val Taken: String = "taken"

  /**
   * One case, with the defect it comes from.
   *
   * `attempt` returns what the kernel actually did, so a row that comes out the wrong way is
   * reported by name beside the ones that did not, rather than failing the run at the first.
   */
  private final case class Attack(
    name: String,
    origin: String,
    expected: String,
    attempt: () => String,
    /**
     * Whether the row records a limit rather than a defence.
     *
     * A row the kernel takes is otherwise the must-accept half, which exists so that a kernel
     * refusing everything cannot score well. A row that gets through **and should not** is a third
     * thing, and filing it under either of the other two would say something false: under
     * must-refuse the suite would go red for a defect nobody has repaired, and under must-accept
     * the corpus would be claiming a limit as a feature. This repository keeps `Refutation`'s seven
     * answers apart for the same reason.
     */
    known: Boolean = false
  )

  private def verdictOf[E, T](result: Either[E, T]): String =
    result.fold(_.getClass.getSimpleName, _ => Taken)

  /** A theory with a predicate on a declared type and something that satisfies it. */
  private def witnessed: (Theory, Kernel.Thm) = {
    val ind = TyApp("ind", Nil)
    val theory = force(
      for {
        withInd <- Theory.primitive.declareTypeOperator("ind", 0)
        withP <- withInd.declareConstant("P", Type.fun(ind, Type.Bool))
        withW <- withP.declareConstant("w", ind)
      } yield withW
    )
    val applied = force(
      Term.app(force(theory.constant("P", Type.fun(ind, Type.Bool))), force(theory.constant("w", ind)))
    )
    val (asserted, witness) = force(Kernel.assertAxiom(theory, applied))
    (asserted, witness)
  }

  private val Capture = "the capture hole of 2026-09-03"
  private val TypeRule = "the type definition rule of 2026-09-10"
  private val Typo = "a typo in a constant name, which parses as a variable"
  private val Signature = "the signature invariant, read adversarially on 2026-09-10"
  private val DeclaredOrigin = "the origin of a declared constant, measured 2026-09-12"

  /**
   * Falsity out of two theories that each declare one name and axiomatise it the other way.
   *
   * `Theory.declareConstant` records the name and writes nothing into `origins`, so a constant
   * that is declared and never defined carries `origin = None`, and `Const.sameOrigin` matches
   * `(None, None)`. Two theories that declare `p : bool` therefore build the **same** constant,
   * and a `Kernel.Thm` carries no theory of its own, so the two axioms meet in one rule.
   *
   * This is the case `Real.scala` is made of: `+`, `*`, `neg`, `inv`, `<`, `0` and `1` are
   * declared and take their meaning from an axiom, not from a defining body.
   *
   * Returned as a whole theorem rather than a verdict string, because the row has to assert that
   * what came back is `|- F` outright and not merely that some rule did not refuse.
   */
  private def falsityFromTwoDeclarations: Option[Kernel.Thm] = {
    val base = Logic.standard
    val negation = force(base.theory.constant("~", Type.fun(Type.Bool, Type.Bool)))

    val theoryA = force(base.theory.declareConstant("p", Type.Bool))
    val theoryB = force(base.theory.declareConstant("p", Type.Bool))

    val (_, holds) = force(Kernel.assertAxiom(theoryA, force(theoryA.constant("p", Type.Bool))))
    val denied = force(Term.app(negation, force(theoryB.constant("p", Type.Bool))))
    val (_, doesNot) = force(Kernel.assertAxiom(theoryB, denied))

    Rules(base).notElim(doesNot, holds).toOption
  }

  /** A type operator no theory in this repository declares. */
  private val ghostType: Type = TyApp("ghost", Nil)

  /** `|- x:A = x:A`, whose type variable is what `instType` replaces. */
  private val polymorphic: Kernel.Thm = Kernel.refl(Term.variable("x", TyVar("A")))

  /** A proposition about a type nobody declared, built without any rule noticing. */
  private val ghostClaim: Term =
    force(Term.eq(Term.variable("g", ghostType), Term.variable("g", ghostType)))

  private val Corpus: Vector[Attack] = Vector(
    Attack("a loose index through inst", Capture, "NotLocallyClosed", () => {
      val betaStep = force(Kernel.beta(force(Term.app(lam(v, h), v))))
      verdictOf(Kernel.inst(Map(h -> loose), betaStep))
    }),
    Attack("a loose index assumed", Capture, "NotLocallyClosed", () => verdictOf(Kernel.assume(loose))),
    // Built by hand, because `Term.app` refuses to place it in an application at all.
    Attack("a loose index reduced", Capture, "NotLocallyClosed", () => verdictOf(Kernel.beta(loose))),
    Attack("a loose index applied", Capture, "NotLocallyClosed", () => verdictOf(Term.app(f, loose))),
    // The one this list did not have until 2026-09-10, and the list is the reason it is worth
    // saying twice: the six lines around this one enumerate the operations that must refuse a
    // loose index, `Term.abs` belongs among them, and it was the only one of the seven that did
    // not check. An adversarial review found it; reading the corpus did not, because a corpus
    // shows what it contains.
    //
    // What it bought an attacker: `close` leaves a loose index alone and the new binder captures
    // it, at whatever type that binder has. Abstract the body of `\z:real. z = z` under a variable
    // of type `bool` and the result applies equality at `real` to two booleans, which `typeOf`
    // answers for rather than refusing, because it is entitled to assume what `abs` was failing to
    // establish.
    Attack("a loose index abstracted", Capture, "NotLocallyClosed", () =>
      verdictOf(Term.abs(Term.variable("w", Type.Bool), loose))
    ),
    Attack("a loose index equated", Capture, "NotLocallyClosed", () => verdictOf(Term.eq(loose, loose))),
    Attack("a loose index defined", Capture, "NotLocallyClosed", () =>
      verdictOf(Kernel.defineConstant(Real.standard.theory, "c", loose))
    ),
    Attack("a loose index asserted", Capture, "NotLocallyClosed", () =>
      verdictOf(Kernel.assertAxiom(Real.standard.theory, loose))
    ),
    // `refl` returns a theorem rather than an `Either`, so it defends itself by throwing. That is
    // the reason nothing can carry a loose index into `defineType`, which takes a theorem.
    Attack("a loose index reflected", Capture, "KernelInvariantViolation", () =>
      try { Kernel.refl(loose); Taken }
      catch { case error: Throwable => error.getClass.getSimpleName }
    ),
    // A predicate with nothing in it, given a type anyway, and the reason the witness has to hold
    // outright. Assume `P w`, define the type under that assumption, and discharge it afterwards:
    // neither theorem that comes back carries a hypothesis, so the assumption would vanish and a
    // predicate satisfied by nothing would be in bijection with an inhabited type.
    Attack("a type from a witness that is only assumed", TypeRule, "TheoremHasHypotheses", () => {
      val (theory, witness) = witnessed
      val assumed = force(Kernel.assume(witness.conclusion))
      verdictOf(Kernel.defineType(theory, "sub", "abs", "rep", assumed))
    }),
    Attack("a type from a witness of another signature", TypeRule, "UnknownConstant", () => {
      // Found by the second reading of the rule, on 2026-09-10. The predicate named a constant the
      // theory being extended does not declare, so the type came back characterised by a
      // proposition that same theory then refused as an axiom.
      val away = force(Theory.primitive.declareConstant("elsewhere", Type.Bool))
      val foreign = force(away.constant("elsewhere", Type.Bool))
      verdictOf(Kernel.defineType(Theory.primitive, "sub", "abs", "rep", Kernel.refl(foreign)))
    }),
    Attack("a type named over an existing type", TypeRule, "AlreadyDeclared", () => {
      val (theory, witness) = witnessed
      verdictOf(Kernel.defineType(theory, "ind", "abs", "rep", witness))
    }),
    // How one arrives: the parser reads an unknown letter-initial name as a variable, so a typo in
    // a constant name states something about an arbitrary function and prints identically.
    Attack("an axiom with a free variable", Typo, "DefinitionIsNotClosed", () => {
      val statement = force(Real.standard.proposition("!x:real. x + ng x = 0"))
      verdictOf(Kernel.assertAxiom(Real.standard.theory, statement))
    }),
    Attack("a type from a witness that holds outright", TypeRule, Taken, () => {
      val (theory, witness) = witnessed
      verdictOf(Kernel.defineType(theory, "sub", "abs", "rep", witness))
    }),
    Attack("an axiom that is closed", Typo, Taken, () => {
      val statement = force(Real.standard.proposition("!x:real. x + x = 2 * x"))
      verdictOf(Kernel.assertAxiom(Real.standard.theory, statement))
    }),

    /* ----------------------------- the origin of a declared constant, and the falsity it allows */

    // Card `a9b78674` asked whether this case derives falsity or only looks as though it might.
    // It derives: 110 inferences to `|- F` with no hypotheses, measured 2026-09-12. That settles
    // the question the card left open, in the direction that makes the card larger rather than
    // smaller, and it is the one row here that is a falsity rather than a broken invariant.
    //
    // What `docs/adr/0008` closed is the case of two theories that **define** a name differently:
    // the origin is the defining body, the bodies differ, the constants differ, and the row two
    // paragraphs below still passes. What it does not close is two theories that **declare** a
    // name and constrain it with different axioms, because an axiom is not the origin of a
    // constant and there is nothing to compare.
    //
    // Filed as a recorded limit rather than a must-refuse, under the rule that governs this
    // corpus: a must-refuse row would turn the suite red for a defect nobody has repaired, and
    // the repair is a design decision (what the identity of an axiomatised constant is) that an
    // ADR superseding 0008 has to take. The day it lands, this row flips and somebody is told.
    //
    // **The sentence above that says there is nothing to compare stopped being true on
    // 2026-09-13, and this row still stands.** There is something to compare, and it is not on
    // the constant: it is the theory's own axiom list against the axioms the derivation rests on.
    // `Derivation.foreignTo` compares them, and the test below this corpus shows it naming this
    // very theorem as foreign to both of the theories that made it. What that does NOT do is stop
    // the theorem being built, which is why this row is unchanged and `known` is still true: the
    // hole is detectable at a boundary now, and it is not closed. Closing it means carrying the
    // theory on every theorem, which `docs/adr/0008` priced and declined.
    //
    // Not an inconsistency in ordinary use: there is one theory of the reals, and reaching this
    // takes a caller who builds two and then combines their theorems on purpose.
    Attack("falsity from two theories that axiomatise one declared name", DeclaredOrigin, Taken, () =>
      falsityFromTwoDeclarations match {
        case Some(theorem) if theorem.conclusion == Logic.standard.falsity && theorem.hypotheses.isEmpty =>
          Taken
        case Some(theorem) => s"a theorem, but ${theorem.display}"
        case None => "refused"
      },
      known = true
    ),

    /* ------------------------------------ the signature invariant, and where it does not hold */

    // Found on 2026-09-10 by an adversarial re-reading of the kernel, verified here rather than
    // argued. `instType` takes a map of type variables to types and never sees a theory, so the
    // type it substitutes in is whatever the caller wrote down. `Type`'s constructors are public
    // on purpose, because naming a type proves nothing and a type from outside is checked by
    // `Theory.checkType`, and these two rules are where that check is not reached.
    Attack("an undeclared type operator through instType", Signature, Taken, () =>
      verdictOf(Right(Kernel.instType(Map("A" -> ghostType), polymorphic))), known = true
    ),

    // The same hole one step earlier, and the reason the repair is not "give those two rules a
    // theory": `Term.variable` is public and unchecked, so a type nobody declared is already in a
    // term before any rule is asked. `refl` then hands back a theorem about it. A repair that
    // covered `inst` and `instType` and stopped there would have left this row exactly as it is.
    Attack("an undeclared type operator through a variable", Signature, Taken, () =>
      try { Kernel.refl(Term.variable("g", ghostType)); Taken }
      catch { case error: Throwable => error.getClass.getSimpleName },
      known = true
    ),

    // And the door that is shut, which is the whole reason the two rows above are a broken
    // invariant and not a falsity: all three theory extensions call `Theory.checkTerm`, so a
    // theorem naming a type nobody declared cannot be recycled into an axiom or a definition. It
    // stays a statement about an uninterpreted type, and every model of the theory extends to one
    // that interprets it, because a HOL type is non-empty and nothing can prove one empty.
    Attack("an undeclared type operator asserted as an axiom", Signature, "UnknownTypeOperator", () =>
      verdictOf(Kernel.assertAxiom(Real.standard.theory, ghostClaim))
    ),
    Attack("an undeclared type operator defined into a constant", Signature, "UnknownTypeOperator", () =>
      verdictOf(Kernel.defineConstant(Real.standard.theory, "ghosted", Term.variable("g", ghostType)))
    )
  )

  "The adversarial corpus" should "come out the way every entry says it must" in {
    val outcomes = Corpus.map(attack => (attack, attack.attempt()))

    info(
      s"${Corpus.size} attacks over ${Corpus.map(_.origin).distinct.size} defects: " +
        s"${Corpus.count(attack => attack.expected != Taken)} must be refused, " +
        s"${Corpus.count(attack => attack.expected == Taken && !attack.known)} must be taken, " +
        s"${Corpus.count(_.known)} get through and are recorded limits; " +
        s"${outcomes.count { case (attack, got) => attack.expected != got }} came out otherwise"
    )

    val wrong = outcomes.collect {
      case (attack, got) if attack.expected != got =>
        s"${attack.name} (${attack.origin}): expected ${attack.expected}, got $got"
    }

    withClue(s"came out the wrong way:\n${wrong.mkString("\n")}\n") {
      wrong shouldBe empty
    }
  }

  it should "hold a must-accept half, since a rule that refuses everything passes the rest" in {
    // The guard that keeps the score from being satisfiable by a kernel that says no to all of it,
    // and the recorded limits are excluded from it: they are taken because nothing checks, which
    // is not evidence that the rules that do check produce anything usable.
    Corpus.count(attack => attack.expected == Taken && !attack.known) should be >= 2
  }

  it should "say which rows are limits rather than defences, by name" in {
    // Printed rather than counted, because a limit nobody can name is a limit nobody will repair.
    //
    // Two kinds sit here and they are **not** the same size, which is why this comment names them
    // apart rather than calling them all limits. The signature rows are a broken invariant and not
    // a falsity: a theorem of a theory should name only that theory's signature, two rules plus
    // one public constructor do not enforce it, and `docs/architecture.md` carries the argument
    // for why nothing false follows. The declared-origin row **is** a falsity, `|- F` with no
    // hypotheses, measured rather than argued.
    //
    // Both repairs are the same question, and it is the one this file does not settle: whether a
    // `Thm` knows the theory it came from.
    Corpus.filter(_.known).foreach(attack => info(s"${attack.name} (${attack.origin})"))
    Corpus.count(_.known) should be > 0
  }

  /* ------------------------------------ the limit made detectable, which is not the same as closed */

  /**
   * The two theories that produce the falsity, each with its axiom asserted.
   *
   * Rebuilt here rather than returned by [[falsityFromTwoDeclarations]], which hands back the
   * theorem alone. `Theory` is a case class and its axioms are terms compared structurally, so a
   * theory rebuilt the same way is the same theory to every question asked below; what could not
   * be rebuilt is the theorem, because the two axiom nodes in its derivation have to be the ones
   * that meet in the rule.
   */
  private def bothDeclaringTheories: (Theory, Theory) = {
    val base = Logic.standard.theory
    val negation = force(base.constant("~", Type.fun(Type.Bool, Type.Bool)))
    val theoryA = force(base.declareConstant("p", Type.Bool))
    val theoryB = force(base.declareConstant("p", Type.Bool))
    val (withP, _) = force(Kernel.assertAxiom(theoryA, force(theoryA.constant("p", Type.Bool))))
    val denied = force(Term.app(negation, force(theoryB.constant("p", Type.Bool))))
    val (withNotP, _) = force(Kernel.assertAxiom(theoryB, denied))
    (withP, withNotP)
  }

  "The falsity two declaring theories produce" should "be foreign to both of them" in {
    // The row above says the kernel builds this theorem and nothing refuses, and that is still
    // true. What is new on 2026-09-13 is that a caller can ASK, and the thing it asks is not about
    // the constant: `p` is declared in both theories with no origin in either, so nothing on the
    // term tells them apart, and `docs/adr/0008` says that is right for an uninterpreted name.
    // What distinguishes them is the axiom, and an axiom belongs to the theory.
    //
    // **Until 2026-09-16 this test measured one of the two and the base**, while its name said
    // both, and the difference is the one `c776f787` asks for: "foreign to the base" is a weaker
    // statement that a theorem of either sibling also satisfies, so the sentence a caller wants —
    // neither parent certifies what the two of them made — was not asserted anywhere.
    val theorem = falsityFromTwoDeclarations.getOrElse(fail("the attack no longer builds"))
    val base = Logic.standard.theory
    val (withP, withNotP) = bothDeclaringTheories

    // Against the theory that holds only `p`: the `~p` axiom is foreign, and it is reported as an
    // AXIOM rather than as a constant, which is the half that matters for soundness.
    val againstA = Derivation.foreignTo(withP, theorem)
    againstA.clean shouldBe false
    againstA.axioms should have size 1
    againstA.constants shouldBe empty

    // And the other parent, symmetrically: it holds `~p` and the `p` axiom is the foreign one. The
    // two together are what the name of this test claims, and neither alone is.
    val againstB = Derivation.foreignTo(withNotP, theorem)
    againstB.clean shouldBe false
    againstB.axioms should have size 1
    againstB.constants shouldBe empty

    // The two foreign axioms are different axioms, which is what stops the pair above from being
    // satisfied by a check that reports the same thing twice.
    againstA.axioms should not be againstB.axioms

    // And against a theory that holds neither: both axioms are foreign. Paired with the rows
    // above, because "reports something" is what a check that reports everything also does.
    val againstBase = Derivation.foreignTo(base, theorem)
    againstBase.axioms should have size 2

    // The other direction, which is what says the check is not simply refusing: a theorem of the
    // base theory, resting on no axiom at all, is clean against the base and against both siblings.
    val innocent = force(Rules(Logic.standard).truth)
    Derivation.foreignTo(base, innocent).clean shouldBe true
    Derivation.foreignTo(withP, innocent).clean shouldBe true
    Derivation.foreignTo(withNotP, innocent).clean shouldBe true
  }

  it should "be taken by a check that reads only its constants, which is why that is not the check" in {
    // The measurement that decides where the boundary check lives, and it is the one thing a
    // reading of `docs/adr/0019` could not supply. That record adopts `Theory.certifies(thm)` and
    // the card carrying it defines it as: every constant of the theorem is the theory's, compared
    // by name, type and origin. Comparing all three over a term is `Theory.checkTerm`, which is
    // public and which the three theory extensions already call.
    //
    // Run over this theorem against each theory that built it, it says YES to all of it. The
    // reason is not a defect in `checkTerm`: `p` does not OCCUR in `|- F`. The sequent is
    // `F` with no hypotheses, every constant in it belongs to the logic both theories extend, and
    // a check that reads the statement's vocabulary has nothing to object to.
    //
    // So the two halves of the card cannot both be met by one definition: "reads the constants"
    // and "says no on this theorem" are incompatible here, and what says no is the AXIOM half,
    // which `Derivation.foreignTo` computes and the test above asserts.
    //
    // **The inference runs one way only, and a reader who generalises this test needs to know
    // which.** `checkTerm` is STRICTLY STRONGER than the definition it is standing in for: before
    // it compares any constant it asks `Term.isLocallyClosed`, and inside the walk it checks the
    // type of every free variable and of every binder. So green here implies that the weaker
    // reading also takes the theorem, which is the direction the conclusion needs; a red would
    // imply nothing about it, because it could come from either of the other two conditions and
    // neither has anything to do with an origin. On `|- F` those conditions are trivial, which is
    // why the substitution is fair here and not in general.
    val theorem = falsityFromTwoDeclarations.getOrElse(fail("the attack no longer builds"))
    val (withP, withNotP) = bothDeclaringTheories

    val statement = theorem.conclusion :: theorem.hypotheses
    statement.foreach { term =>
      withP.checkTerm(term) shouldBe Right(())
      withNotP.checkTerm(term) shouldBe Right(())
    }

    // The floor, and it is a refusal rather than a count. A fold reporting "nothing objected to"
    // is what a check that objects to nothing also reports, and the size of the statement does not
    // separate the two: `|- F` has one term whatever happens. What separates them is the same call
    // turning something away, by name, against the same two theories.
    val foreign = force(Real.standard.theory.constant(Real.Zero, real))
    withP.checkTerm(foreign) shouldBe Left(UnknownConstant(Real.Zero))
    withNotP.checkTerm(foreign) shouldBe Left(UnknownConstant(Real.Zero))
  }

  it should "not be closed by this, which the corpus row above still records" in {
    // The assertion that stops the sentence above from being read as a repair. The theorem is
    // still `|- F` with no hypotheses, built by a kernel that refused nothing, and every caller
    // that does not ask is exactly where it was.
    val theorem = falsityFromTwoDeclarations.getOrElse(fail("the attack no longer builds"))

    theorem.conclusion shouldBe Logic.standard.falsity
    theorem.hypotheses shouldBe empty
  }
}
