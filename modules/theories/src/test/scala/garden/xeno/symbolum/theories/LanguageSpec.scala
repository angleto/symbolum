package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The embedded theory's language, and the two things a reader has to be shown about it.
 *
 * The file was about `NUM_TERM` alone when it was written and now covers the formulas, the
 * numerals, the substitution and the axioms of PA. The pair below is what each group is held
 * to, not a description of the term predicate that happens to lead: a predicate is shown to
 * accept and shown to refuse, and a group with only the first half is not checked.
 *
 * **That it accepts, and to any depth.** The five introduction rules are the easy half and a
 * compound term is derived here rather than described: `0 + v7` is three codes nested two deep, and
 * it goes through by composing the rules, which is what says the recursion is usable and not only
 * provable.
 *
 * **That it REFUSES, which is the half that says it is a term predicate at all.** A predicate that
 * held everywhere would satisfy every introduction rule above and would be useless. `NUM_TERM_ZERO`
 * and `NUM_TERM_NOT_ZERO` together already say it is not constant, and that is the weakest form of
 * the claim. The two derived here are the strong form: a code with an **unrecognised tag** is not a
 * term, and a code for zero with a **payload other than zero** is not a term. The first says the
 * predicate reads its tag; the second says the payload condition in the definition is doing work,
 * which its docstring claims and nothing else here would check.
 *
 * Both need one thing the repository did not have this morning, which is that two numerals of `num`
 * differ. `Successor.distinct` is that, and it exists because of this test rather than the other way
 * round.
 *
 * The axioms of PA are refused the cheapest way of any group here, and the contrast is worth the
 * line. The other refusals open the recursion equation and rule out each clause; this one costs
 * three lines, because `NUM_PA_FORM` says an axiom is a formula and the code of zero is already
 * known not to be one. A group that has a fact about it does not need a derivation about it.
 */
class LanguageSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val language = chain.language
  private val logic = language.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)

  private def term(text: String): Term =
    force(Parser.term(language.theory, language.notation, text, numbers))

  private def proposition(text: String): Term =
    force(Parser.proposition(language.theory, language.notation, text))

  "The term predicate" should "be the statements this development publishes" in {
    Language.Statements.foreach { case (name, text) =>
      val theorem = force(language.fact(name))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe force(
          Parser.proposition(language.theory, language.notation, text)
        )
        theorem.hypotheses shouldBe empty
      }
    }
  }

  /**
   * What each statement costs, and the split is the measurement rather than the total.
   *
   * Everything built here is built on `Descent`, which is built on the recursion theorem, which
   * spends choice and infinity: two axioms, the naturals' own, and nothing beyond them. That was
   * the whole assertion until the axioms of PA landed, and those cost **nothing at all**.
   *
   * It is worth saying why rather than filing it as a pleasant surprise. `NUM_PA` is a disjunction
   * of seven cases, so membership in it is settled by unfolding a definition and picking a
   * disjunct; no clause of it reads the predicate being defined, so there is no recursion to
   * justify and no admissibility proof to pay for. That is the same fact as "PA is recursively
   * axiomatised" seen from inside: the property Goedel's argument needs of the axiom set is that a
   * machine can recognise it, and here it shows up as a proof that spends no axiom.
   *
   * So the assertion is two-sided, and the second side is the one with teeth: the free statements
   * are exactly the eight about `NUM_PA` and no others, which fails if a later clause of the axiom
   * set is written recursively, and fails equally if some fact that ought to cost the recursion
   * quietly stops using it.
   */
  it should "cost what the naturals cost, except where a definition alone settles it" in {
    val recursion = force(chain.naturals.recursion)
    val naturals = Derivation.axiomsOf(recursion)
    naturals should have size 2

    val costs = Language.Statements.map { case (name, _) =>
      name -> Derivation.axiomsOf(force(language.fact(name)))
    }

    val free = costs.collect { case (name, spent) if spent.isEmpty => name }
    free.toSet shouldBe (Language.Axioms.map(_._1) ++ Language.LogicalAxioms ++
      Vector(
        Language.AxiomInduction,
        Language.AxiomCases,
        Language.LogicCases,
        Language.ClosedCases
      )).toSet

    costs.foreach { case (name, spent) =>
      withClue(s"$name: ") {
        if (!free.contains(name)) spent shouldBe naturals
      }
    }
  }

  /**
   * The seven axioms are seven, and this is the guard the defect that occurred asks for.
   *
   * `NUM_PA` is a right-nested disjunction and a membership proof enters it at its own position,
   * wrapped once per disjunct before it. Getting that nesting wrong is not a compile error and not
   * a kernel refusal: what comes out is a theorem, correctly proved, about the wrong disjunct. It
   * happened while this was written, and every one of the seven still built.
   *
   * So the assertion is that the seven conclusions are pairwise distinct terms. Under the defect
   * they collapse onto one, and under a corrected version they cannot: two codes are equal only if
   * their tags and payloads are, and the six axioms are six different formulas.
   *
   * This is deliberately about the theorems rather than about `Axioms`, whose entries a reader can
   * see are different by looking. What is being checked is that the proof of each landed where its
   * name says, and the only way to see that is to read what was proved.
   */
  it should "prove seven different memberships and not one of them seven times" in {
    val names = Language.Axioms.map(_._1) :+ Language.AxiomInduction
    val conclusions = names.map(name => force(language.fact(name)).conclusion)

    conclusions.distinct should have size names.size
  }

  /** The same guard for the logical axioms, where every one of the eight is a scheme. */
  it should "prove eight different logical axioms and not one of them eight times" in {
    val conclusions = Language.LogicalAxioms.map(name => force(language.fact(name)).conclusion)

    conclusions.distinct should have size Language.LogicalAxioms.size
  }

  /**
   * An instance of specialisation, built at a concrete formula and a concrete closed term.
   *
   * The eight schemes are provable and that is not the same as usable. This one is the hardest of
   * the eight to use, because its third condition is `NUM_CLOSED t`, and nothing until this commit
   * could discharge such a condition at all: it needs freeness at every index, which is what the
   * previous piece of work was for.
   *
   * What comes out is the code of `(!v0. v0 = v0) ==> (v0 = v0)[v0 := 0]`, which is a logical
   * axiom. Everything the object theory will ever derive goes through instances built this way, so
   * a scheme nothing can instantiate would be a scheme nothing notices is useless.
   */
  it should "hold an instance of specialisation at a closed term" in {
    val zeroCode = term("NUM_CODE 1 0")
    val variable = term("NUM_CODE 0 0")
    val claim = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))")

    // The object language's zero is closed: no index occurs in it, one index at a time.
    val atIndex = force(rules.spec(term("k"), force(language.fact(Language.FreeZero))))
    val occurs = Term.destEq(atIndex.conclusion).map(_._1).getOrElse(fail("an equation"))
    val nowhere = force(
      LogicError
        .lift(Kernel.assume(occurs))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(atIndex, assumed)))
        .flatMap(rules.notIntro(occurs, _))
        .flatMap(rules.gen(Term.variable("k", numbers), _))
    )
    val closed = force(
      rules
        .spec(zeroCode, force(language.fact(Language.ClosedCases)))
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, nowhere)))
    )
    closed.hypotheses shouldBe empty
    closed.conclusion shouldBe proposition("NUM_CLOSED (NUM_CODE 1 0)")

    val isVariable = force(rules.spec(term("0"), force(language.fact(Language.TermVariable))))
    val isFormula = force(
      rules
        .specAll(force(language.fact(Language.FormulaEquality)), List(variable, variable))
        .flatMap(rules.mp(_, isVariable))
        .flatMap(rules.mp(_, isVariable))
    )

    val instance = force(
      rules
        .specAll(
          force(language.fact("NUM_LOGIC_SPECIALISE")),
          List(term("0"), zeroCode, claim)
        )
        .flatMap(rules.mp(_, isFormula))
        .flatMap(rules.mp(_, force(language.fact(Language.TermZero))))
        .flatMap(rules.mp(_, closed))
    )

    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      "NUM_LOGIC (NUM_CODE 7 (NUM_PAIR " +
        "(NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))))) " +
        "(NUM_SUBST_FORM 0 (NUM_CODE 1 0) " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))))))"
    )
    Derivation.axiomsOf(instance) should have size 2
  }

  /**
   * A term two constructors deep goes through by composing the rules.
   *
   * `0 + v7`, whose code is `NUM_CODE 3 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 0 7))`. Nothing in the
   * five rules mentions depth and nothing has to: the recursion `Descent` produced is what carries
   * it, and this is the assertion that the produced equation is usable rather than merely true.
   */
  it should "accept a term two constructors deep" in {
    val zeroTerm = term("NUM_CODE 1 0")
    val variable = term("NUM_CODE 0 7")

    val zeroIsTerm = force(language.fact(Language.TermZero))
    val variableIsTerm =
      force(rules.spec(term("7"), force(language.fact(Language.TermVariable))))

    val sum = force(
      rules
        .specAll(force(language.fact(Language.TermSum)), List(zeroTerm, variable))
        .flatMap(rules.mp(_, zeroIsTerm))
        .flatMap(rules.mp(_, variableIsTerm))
    )

    sum.hypotheses shouldBe empty
    sum.conclusion shouldBe proposition(
      "NUM_TERM (NUM_CODE 3 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 0 7)))"
    )
    Derivation.axiomsOf(sum) should have size 2
  }

  /**
   * A code the predicate does not recognise is refused, and this is the assertion with teeth.
   *
   * Read `NUM_TERM_CASES` the other way at `NUM_CODE 5 0`. The constructor is injective, so the
   * tag is `5`; every clause of the definition pins the tag to one of `0` to `4`; and five is none
   * of those. What comes out is a theorem and not a silence.
   */
  it should "refuse a code whose tag it does not know" in {
    refuse(term("5"), term("0"), "NUM_CODE 5 0")
  }

  /**
   * A code for zero whose payload is not zero is refused, which is the condition doing work.
   *
   * The definition's clause for zero is `t = 1 /\ p = 0`, and the file's docstring says the second
   * conjunct is not decoration: without it `NUM_CODE 1 5` would be a second code for the same term.
   * That sentence is worth nothing unless the refusal is derived, so it is.
   */
  it should "refuse a code for zero that carries the wrong payload" in {
    refuse(term("1"), term("5"), "NUM_CODE 1 5")
  }

  /**
   * `~(NUM_TERM (NUM_CODE tag payload))`, by ruling out every clause the definition offers.
   *
   * The tag is recovered by `NUM_CODE_INJECTIVE` and then each of the four disjuncts is refused:
   * three of them pin the tag to a numeral and the fourth pins it to one of two, so the whole thing
   * is five numeral disequalities and the payload's own, and `Successor.distinct` settles each.
   */
  private def refuse(tag: Term, payload: Term, text: String): Unit = {
    val coded = force(LogicError.lift(Term.appAll(
      force(LogicError.lift(language.theory.constant(
        Numbering.CodeName, Type.fun(numbers, Type.fun(numbers, numbers))))),
      List(tag, payload)
    )))
    val claim = force(LogicError.lift(Term.app(
      force(LogicError.lift(language.theory.constant(
        Language.TermName, Type.fun(numbers, Type.Bool)))),
      coded
    )))

    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val cases = force(rules.spec(coded, force(language.fact(Language.TermCases))))
    val opened = force(LogicError.lift(Kernel.eqMp(cases, assumed)))

    def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic
        .destExistsPredicate(existential.conclusion)
        .getOrElse(fail("an existential was expected"))
      val variable = Conv.freshVariable(name, numbers, taken)
      val applied = force(LogicError.lift(Term.app(predicate, variable)))
      val contraction = force(Conv.betaRoot(applied))
      val body = Term.destEq(contraction.conclusion).map(_._2).getOrElse(fail("an equation"))
      val instance = force(LogicError.lift(Kernel.assume(body)))
      force(rules.existsElim(existential, variable, reach(variable, instance)))
    }

    val absurd = open(opened, "t", Set.empty) { (foundTag, atTag) =>
      open(atTag, "p", Set(foundTag)) { (foundPayload, atPayload) =>
        val isCode = force(rules.conjElim1(atPayload))
        val disjunction = force(rules.conjElim2(atPayload))
        val recovered = force(
          rules
            .specAll(
              force(language.numbering.fact(Numbering.CodeInjective)),
              List(tag, payload, foundTag, foundPayload)
            )
            .flatMap(rules.mp(_, isCode))
        )
        val tagIs = force(rules.conjElim1(recovered))
        val payloadIs = force(rules.conjElim2(recovered))

        /** `F` from a clause that pins the found tag to `wanted`, which the real tag is not. */
        def byTag(pinned: Kernel.Thm, wanted: Term): Kernel.Thm = {
          val chained = force(Conv.trans(tagIs, pinned))
          force(rules.notElim(force(chain.successor.distinct(tag, wanted)), chained))
        }

        val parts = {
          val (first, rest) = logic.destDisj(disjunction.conclusion).getOrElse(fail("a disjunction"))
          val (second, tail) = logic.destDisj(rest).getOrElse(fail("a disjunction"))
          val (third, fourth) = logic.destDisj(tail).getOrElse(fail("a disjunction"))
          Vector(first, second, third, fourth)
        }

        val falsity = logic.falsity
        val atVariable = {
          val a = force(LogicError.lift(Kernel.assume(parts(0))))
          byTag(a, term("0"))
        }
        val atZero = {
          val a = force(LogicError.lift(Kernel.assume(parts(1))))
          val pinnedTag = force(rules.conjElim1(a))
          val pinnedPayload = force(rules.conjElim2(a))
          if (tag == term("1")) {
            val chained = force(Conv.trans(payloadIs, pinnedPayload))
            force(rules.notElim(force(chain.successor.distinct(payload, term("0"))), chained))
          } else byTag(pinnedTag, term("1"))
        }
        val atSuccessor = {
          val a = force(LogicError.lift(Kernel.assume(parts(2))))
          byTag(force(rules.conjElim1(a)), term("2"))
        }
        val atBinary = {
          val a = force(LogicError.lift(Kernel.assume(parts(3))))
          val tags = force(rules.conjElim1(a))
          val (isThree, isFour) = logic.destDisj(tags.conclusion).getOrElse(fail("a disjunction"))
          val three = byTag(force(LogicError.lift(Kernel.assume(isThree))), term("3"))
          val four = byTag(force(LogicError.lift(Kernel.assume(isFour))), term("4"))
          force(rules.disjElim(tags, three, four))
        }

        val tail = force(LogicError.lift(Kernel.assume(
          force(logic.mkDisj(parts(2), parts(3))))))
        val rest = force(LogicError.lift(Kernel.assume(
          force(logic.mkDisj(parts(1), force(logic.mkDisj(parts(2), parts(3))))))))
        val insideTail = force(rules.disjElim(tail, atSuccessor, atBinary))
        val insideRest = force(rules.disjElim(rest, atZero, insideTail))
        val settled = force(rules.disjElim(disjunction, atVariable, insideRest))
        settled.conclusion shouldBe falsity
        settled
      }
    }

    val refuted = force(rules.notIntro(claim, absurd))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~(NUM_TERM ($text))")
    Derivation.axiomsOf(refuted) should have size 2
  }

  /* --------------------------------------------------------------------------- the formulas */

  /**
   * A formula three constructors deep, built by composing the rules.
   *
   * `!v0. v0 = 0`, whose code is `NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0)
   * (NUM_CODE 1 0))))`. It crosses the two predicates once: the equality's two arguments are terms
   * and its premises are `NUM_TERM`, while the quantifier's is `NUM_FORM`.
   */
  it should "accept a quantified formula built out of terms" in {
    val variable = term("NUM_CODE 0 0")
    val zeroTerm = term("NUM_CODE 1 0")

    val variableIsTerm =
      force(rules.spec(term("0"), force(language.fact(Language.TermVariable))))
    val zeroIsTerm = force(language.fact(Language.TermZero))

    val equality = force(
      rules
        .specAll(force(language.fact(Language.FormulaEquality)), List(variable, zeroTerm))
        .flatMap(rules.mp(_, variableIsTerm))
        .flatMap(rules.mp(_, zeroIsTerm))
    )
    val quantified = force(
      rules
        .specAll(
          force(language.fact(Language.FormulaUniversal)),
          List(term("0"), term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))"))
        )
        .flatMap(rules.mp(_, equality))
    )

    quantified.hypotheses shouldBe empty
    quantified.conclusion shouldBe proposition(
      "NUM_FORM (NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0)))))"
    )
    Derivation.axiomsOf(quantified) should have size 2
  }

  /**
   * A term is not a formula, which is what the two tag ranges being disjoint buys.
   *
   * `NUM_CODE 1 0` is the code of zero and `Language`'s docstring says the ranges are kept apart so
   * that a code carries which of the two it is without a context to read it in. That is a claim
   * about the tags and it is worth nothing until the refusal is derived: here it is four numeral
   * disequalities, one per clause of `NUM_FORM_CASES`.
   */
  it should "refuse a term as a formula" in {
    refuseFormula(term("1"), term("0"), "NUM_CODE 1 0", None)
  }

  /**
   * An equality whose arguments are not terms is not a formula, which is the side condition biting.
   *
   * `NUM_CODE 5 (NUM_PAIR 0 0)` has the **right tag**, so three of the four clauses go by
   * disequality and the fourth has to be entered. Inside, `NUM_PAIR_INJECTIVE` recovers the two
   * arguments as `0` and `0`, and `NUM_TERM_NOT_ZERO` says zero is not a term.
   *
   * This is the assertion that the equality clause's `NUM_TERM a /\ NUM_TERM b` is load-bearing.
   * Without it the predicate would accept any pair at all under tag five, every introduction rule
   * above would still be provable, and every other test here would still pass.
   */
  it should "refuse an equality whose arguments are not terms" in {
    refuseFormula(term("5"), term("NUM_PAIR 0 0"), "NUM_CODE 5 (NUM_PAIR 0 0)", Some(0))
  }

  /**
   * `~(NUM_FORM (NUM_CODE tag payload))`, ruling out each of the four clauses in turn.
   *
   * `matching` names the clause whose tag the code actually carries, if any. Every other clause is
   * refused by `Successor.distinct` on the tag alone; the matching one has to be opened and refuted
   * on what it asks of the payload.
   */
  private def refuseFormula(
    tag: Term,
    payload: Term,
    text: String,
    matching: Option[Int]
  ): Kernel.Thm = {
    val coded = force(LogicError.lift(Term.appAll(
      force(LogicError.lift(language.theory.constant(
        Numbering.CodeName, Type.fun(numbers, Type.fun(numbers, numbers))))),
      List(tag, payload)
    )))
    val claim = force(LogicError.lift(Term.app(
      force(LogicError.lift(language.theory.constant(
        Language.FormulaName, Type.fun(numbers, Type.Bool)))),
      coded
    )))

    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val cases = force(rules.spec(coded, force(language.fact(Language.FormulaCases))))
    val opened = force(LogicError.lift(Kernel.eqMp(cases, assumed)))

    def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic
        .destExistsPredicate(existential.conclusion)
        .getOrElse(fail("an existential was expected"))
      val variable = Conv.freshVariable(name, numbers, taken)
      val applied = force(LogicError.lift(Term.app(predicate, variable)))
      val contraction = force(Conv.betaRoot(applied))
      val body = Term.destEq(contraction.conclusion).map(_._2).getOrElse(fail("an equation"))
      val instance = force(LogicError.lift(Kernel.assume(body)))
      force(rules.existsElim(existential, variable, reach(variable, instance)))
    }

    val absurd = open(opened, "t", Set.empty) { (foundTag, atTag) =>
      open(atTag, "p", Set(foundTag)) { (foundPayload, atPayload) =>
        val isCode = force(rules.conjElim1(atPayload))
        val disjunction = force(rules.conjElim2(atPayload))
        val recovered = force(
          rules
            .specAll(
              force(language.numbering.fact(Numbering.CodeInjective)),
              List(tag, payload, foundTag, foundPayload)
            )
            .flatMap(rules.mp(_, isCode))
        )
        val tagIs = force(rules.conjElim1(recovered))
        val payloadIs = force(rules.conjElim2(recovered))

        val parts = {
          val (first, rest) = logic.destDisj(disjunction.conclusion).getOrElse(fail("a disjunction"))
          val (second, tail) = logic.destDisj(rest).getOrElse(fail("a disjunction"))
          val (third, fourth) = logic.destDisj(tail).getOrElse(fail("a disjunction"))
          Vector(first, second, third, fourth)
        }

        /** The clause whose tag the code does not carry, refused on the numeral alone. */
        def byTag(which: Int, wanted: String): Kernel.Thm = {
          val a = force(LogicError.lift(Kernel.assume(parts(which))))
          val pinned = force(rules.conjElim1(a))
          val chained = force(Conv.trans(tagIs, pinned))
          force(rules.notElim(force(chain.successor.distinct(tag, term(wanted))), chained))
        }

        /** The equality clause entered: its two arguments have to be terms, and zero is not one. */
        def atEquality: Kernel.Thm = {
          val a = force(LogicError.lift(Kernel.assume(parts(0))))
          val arguments = force(rules.conjElim2(a))
          val inner = open(arguments, "a", Set(foundTag, foundPayload)) { (left, atLeft) =>
            open(atLeft, "b", Set(foundTag, foundPayload, left)) { (right, atRight) =>
              val isPair = force(rules.conjElim1(atRight))
              val both = force(rules.conjElim2(atRight))
              val leftIsTerm = force(rules.conjElim1(both))

              // `payload = NUM_PAIR left right` and the payload IS `NUM_PAIR 0 0`.
              // `NUM_CODE_INJECTIVE` gives `payload = p` and the clause gives `p = NUM_PAIR a b`,
              // so the two compose straight: no `sym` between them.
              val asPair = force(Conv.trans(payloadIs, isPair))
              val components = force(
                rules
                  .specAll(
                    force(language.numbering.fact(Numbering.PairInjective)),
                    List(term("0"), term("0"), left, right)
                  )
                  .flatMap(rules.mp(_, asPair))
              )
              val leftIsZero = force(rules.conjElim1(components))
              val headed = force(LogicError.lift(language.theory.constant(
                Language.TermName, Type.fun(numbers, Type.Bool))))
              val atZero = force(
                Conv
                  .apTerm(headed, force(Conv.sym(leftIsZero)))
                  .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, leftIsTerm)))
              )
              force(rules.notElim(force(language.fact(Language.TermNotZero)), atZero))
            }
          }
          force(rules.disch(arguments.conclusion, inner).flatMap(rules.mp(_, arguments)))
        }

        val clauses = Vector(
          if (matching.contains(0)) atEquality else byTag(0, "5"),
          byTag(1, "6"),
          byTag(2, "7"),
          byTag(3, "8")
        )

        val tail = force(LogicError.lift(Kernel.assume(
          force(logic.mkDisj(parts(2), parts(3))))))
        val rest = force(LogicError.lift(Kernel.assume(
          force(logic.mkDisj(parts(1), force(logic.mkDisj(parts(2), parts(3))))))))
        val insideTail = force(rules.disjElim(tail, clauses(2), clauses(3)))
        val insideRest = force(rules.disjElim(rest, clauses(1), insideTail))
        val settled = force(rules.disjElim(disjunction, clauses(0), insideRest))
        settled.conclusion shouldBe logic.falsity
        settled
      }
    }

    val refuted = force(rules.notIntro(claim, absurd))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~(NUM_FORM ($text))")
    Derivation.axiomsOf(refuted) should have size 2
    refuted
  }

  /**
   * A code that is not an axiom, which is what every axiom being a formula buys.
   *
   * The refusing half of `NUM_PA`, and it is three lines rather than the seventy the two above
   * cost, because it does not go near the disjunction. `NUM_PA_FORM` says an axiom is a formula
   * and the code of the object language's zero is already known not to be one, so the
   * contrapositive settles it. Refuting it disjunct by disjunct would have worked and would have
   * been the wrong shape: what makes the axiom set a set of formulas is one fact, not seven.
   *
   * The measurement beside it is the point. The membership facts cost nothing and this costs the
   * naturals' two, because being a formula is decided by the recursion while being an axiom is
   * decided by a disjunction.
   */
  it should "refuse a code that is not an axiom" in {
    refuseMembership(Language.AxiomFormula, "NUM_PA")
  }

  /** The same for the logical axioms, off the same fact about the same code. */
  it should "refuse a code that is not a logical axiom" in {
    refuseMembership(Language.LogicFormula, "NUM_LOGIC")
  }

  private def refuseMembership(carrier: String, set: String): Unit = {
    val notAFormula = refuseFormula(term("1"), term("0"), "NUM_CODE 1 0", None)

    val claim = proposition(s"$set (NUM_CODE 1 0)")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val implied = force(
      rules
        .spec(term("NUM_CODE 1 0"), force(language.fact(carrier)))
        .flatMap(rules.mp(_, assumed))
    )
    val refused = force(
      rules.notElim(notAFormula, implied).flatMap(rules.notIntro(claim, _))
    )

    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe proposition(s"~($set (NUM_CODE 1 0))")
    Derivation.axiomsOf(refused) should have size 2
  }

  /* ------------------------------------------------------------------------------ freeness */

  /**
   * The quantifier binds, which is the clause a wrong version would pass every other test with.
   *
   * `NUM_FREE_FORM_ALL` is published with the comparison left standing, as a `COND` the caller
   * decides. Every fact about it is an equation either way, so the two branches being the wrong way
   * round is not something the shape of the clause can show: what shows it is taking the clause at
   * the index it is asking about and finding `F` rather than the body's own answer.
   *
   * This is the whole reason the predicate exists. A freeness that did not bind would say the index
   * of `!v0. v0 = v0` occurs free in it, and the two logical axioms waiting on this would each be
   * stated with a condition that is never satisfied.
   */
  it should "bind the index the quantifier quantifies" in {
    val index = term("i")
    val body = term("p")

    val clause = force(
      rules.specAll(force(language.fact(Language.FormulaFreeUniversal)), List(index, index, body))
    )

    // The conditional's three parts are read OFF the clause rather than rebuilt, because a rebuilt
    // guard that did not match would be refused by `Rules.specAll` and read as a broken test.
    val answer = Term.destEq(clause.conclusion).map(_._2).getOrElse(fail("an equation"))
    val parts = answer match {
      case App(App(App(_, guard), yes), no) => (guard, yes, no)
      case other => fail(s"a conditional was expected, found $other")
    }

    val condTrue = Kernel.instType(
      Map(Classical.TypeVariable -> Type.Bool),
      force(language.numbering.peano.naturals.classical.fact(Classical.CondTrue))
    )
    val collapsed = force(
      rules
        .specAll(condTrue, List(parts._1, parts._2, parts._3))
        .flatMap(rules.mp(_, Conv.refl(index)))
    )
    val settled = force(Conv.trans(clause, collapsed))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe proposition(
      "NUM_FREE_FORM i (NUM_CODE 8 (NUM_PAIR i p)) = F"
    )
  }

  /**
   * A variable is free in itself and another one is not, which says the predicate discriminates.
   *
   * The same shape as the refusals above and much cheaper, because freeness is a `COND` nest rather
   * than an existential: what decides both is `NUM_FREE_TERM_VAR`, whose right-hand side is the
   * comparison of the two indices. The first is a reflexivity and the second is two numerals of
   * `num` differing, which is the fourth thing in this development resting on `Successor.distinct`.
   *
   * Without a pair like this every clause equation would still hold of the predicate that answers
   * `T` everywhere, and of the one that answers `F` everywhere the four recursive clauses would.
   */
  it should "say a variable occurs in itself and not in another" in {
    val clause = force(language.fact(Language.FreeVariable))

    val itself = force(
      rules
        .specAll(clause, List(term("i"), term("i")))
        .flatMap(equation =>
          Conv.sym(equation).flatMap(reversed =>
            LogicError.lift(Kernel.eqMp(reversed, Conv.refl(term("i"))))
          )
        )
    )
    itself.hypotheses shouldBe empty
    itself.conclusion shouldBe proposition("NUM_FREE_TERM i (NUM_CODE 0 i)")

    val another = force(
      rules
        .specAll(clause, List(term("0"), term("1")))
        .flatMap { equation =>
          val claim = Term.destEq(equation.conclusion).map(_._1).getOrElse(fail("an equation"))
          for {
            assumed <- LogicError.lift(Kernel.assume(claim))
            differ <- LogicError.lift(Kernel.eqMp(equation, assumed))
            never <- chain.successor.distinct(term("1"), term("0"))
            absurd <- rules.notElim(never, differ)
            refused <- rules.notIntro(claim, absurd)
          } yield refused
        }
    )
    another.hypotheses shouldBe empty
    another.conclusion shouldBe proposition("~(NUM_FREE_TERM 0 (NUM_CODE 0 1))")
    Derivation.axiomsOf(another) should have size 2
  }

  /* --------------------------------------------------------------------------- the numerals */

  /**
   * The numeral for two is the code of `S (S 0)`, written out.
   *
   * The recursion is short enough that its **orientation** is the only thing that can be wrong, and
   * it is the kind of wrong a type checker never sees: a step that built `NUM_CODE 2 v` with the
   * layers the other way round would still be a recursion, still typecheck, and still make every
   * other fact about numerals provable. So the second numeral is unfolded to a closed term and
   * compared against what the object language's `S (S 0)` is.
   */
  it should "spell the numeral for two as two successors over zero" in {
    val two = term("SUC (SUC 0)")
    val atZero = force(language.fact(Language.NumeralAtZero))
    val atSuccessor = force(language.fact(Language.NumeralAtSuccessor))
    val numeral = force(LogicError.lift(language.theory.constant(
      Language.NumeralName, Type.fun(numbers, numbers))))
    val code = force(LogicError.lift(language.theory.constant(
      Numbering.CodeName, Type.fun(numbers, Type.fun(numbers, numbers)))))
    val successorTag = force(LogicError.lift(Term.app(code, term("2"))))

    /** The equation with one more `NUM_CODE 2` wrapped round both sides. */
    def wrapped(equation: Kernel.Thm): Kernel.Thm = force(Conv.apTerm(successorTag, equation))

    val once = force(rules.spec(term("SUC 0"), atSuccessor))
    val twice = force(rules.spec(term("0"), atSuccessor))
    val spelled = force(
      Conv
        .trans(once, wrapped(twice))
        .flatMap(Conv.trans(_, wrapped(wrapped(atZero))))
    )

    spelled.hypotheses shouldBe empty
    spelled.conclusion shouldBe force(LogicError.lift(Term.eq(
      force(LogicError.lift(Term.app(numeral, two))),
      term("NUM_CODE 2 (NUM_CODE 2 (NUM_CODE 1 0))")
    )))
    Derivation.axiomsOf(spelled) should have size 2
  }

  /**
   * Distinct numbers get distinct numerals, which is what makes this a numbering of numbers.
   *
   * The statement is an implication and the content is its contrapositive: a `NUM_NUMERAL` that
   * ignored its argument would satisfy every other fact in this file, including that every numeral
   * is a term, and would make the object language unable to tell two numbers apart. Instantiated
   * here at zero and one so that the claim is not only true but reaches a pair.
   */
  it should "give two different numbers two different numerals" in {
    val injective = force(language.fact(Language.NumeralInjective))
    val instance = force(rules.specAll(injective, List(term("0"), term("SUC 0"))))

    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      "NUM_NUMERAL 0 = NUM_NUMERAL (SUC 0) ==> 0 = SUC 0"
    )

    // And the conclusion is refutable, so the premise is too: the two numerals differ.
    val never = force(rules.spec(term("0"), force(chain.naturals.fact(Natural.SuccessorNotZero))))
    val premise = force(LogicError.lift(Term.eq(
      force(LogicError.lift(Term.app(
        force(LogicError.lift(language.theory.constant(
          Language.NumeralName, Type.fun(numbers, numbers)))),
        term("0")))),
      force(LogicError.lift(Term.app(
        force(LogicError.lift(language.theory.constant(
          Language.NumeralName, Type.fun(numbers, numbers)))),
        term("SUC 0"))))
    )))
    val assumed = force(LogicError.lift(Kernel.assume(premise)))
    val equal = force(rules.mp(instance, assumed))
    val refuted = force(rules.notIntro(premise, force(
      rules.notElim(never, force(Conv.sym(equal))))))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(logic.mkNot(premise))
  }

  /* ----------------------------------------------------------------------- the substitution */

  /**
   * The substitution replaces the variable it was given and leaves the others alone.
   *
   * `NUM_SUBST_VAR` says the answer at a variable is `COND (j = i) t (NUM_CODE 0 j)`, which is the
   * whole content and none of it: a conditional is not an answer until the guard is decided. So
   * both sides are decided here, at the variable being replaced and at another one, and the second
   * needs two numerals of `num` to differ, which is the fourth thing in this development that does.
   *
   * **A `NUM_SUBST` that returned its argument unchanged would satisfy four of the five published
   * equations**, all but this one, and this one only up to a conditional nobody resolved. That is
   * what makes these two derivations the assertion rather than the equations.
   */
  it should "replace the variable it was given and no other" in {
    // Numerals and not successor forms: `Successor.distinct` reads a numeral, which is what the
    // published statements carry anyway.
    val replaced = term("1")
    val other = term("0")
    val replacement = term("NUM_CODE 1 0")
    val rule = force(language.fact(Language.SubstituteVariable))
    val condTrue = Kernel.instType(
      Map(Classical.TypeVariable -> numbers), force(chain.classical.fact(Classical.CondTrue)))
    val condFalse = Kernel.instType(
      Map(Classical.TypeVariable -> numbers), force(chain.classical.fact(Classical.CondFalse)))

    def answerAt(variable: Term, held: Either[Kernel.Thm, Kernel.Thm]): Kernel.Thm = {
      val instance = force(rules.specAll(rule, List(replaced, replacement, variable)))
      val conditional = Term.destEq(instance.conclusion).map(_._2).getOrElse(fail("an equation"))
      val (guard, yes, no) = conditional match {
        case App(App(App(_, g), y), n) => (g, y, n)
        case term => fail(s"a conditional was expected: $term")
      }
      val stepped = held match {
        case Left(proved) =>
          force(rules.specAll(condTrue, List(guard, yes, no)).flatMap(rules.mp(_, proved)))
        case Right(refuted) =>
          force(rules.specAll(condFalse, List(guard, yes, no)).flatMap(rules.mp(_, refuted)))
      }
      force(Conv.trans(instance, stepped))
    }

    // At the variable being replaced the guard is a reflexivity.
    val atReplaced = answerAt(replaced, Left(Conv.refl(replaced)))
    atReplaced.conclusion shouldBe proposition(
      "NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 0 1) = NUM_CODE 1 0"
    )

    // At any other it is two numerals differing, and the variable comes back untouched.
    val atOther = answerAt(other, Right(force(chain.successor.distinct(other, replaced))))
    atOther.conclusion shouldBe proposition(
      "NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 0 0) = NUM_CODE 0 0"
    )

    atReplaced.hypotheses shouldBe empty
    atOther.hypotheses shouldBe empty
    Derivation.axiomsOf(atReplaced) should have size 2
  }

  /**
   * Substitution goes under a constructor, which is what the recursion was for.
   *
   * `v1 + 0` with the numeral for zero put in for `v1`, whose code is
   * `NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 (SUC 0)) (NUM_CODE 1 0))`. One step of `NUM_SUBST_ADD` and
   * then the two arguments separately, which is the shape every use above here will have.
   */
  it should "go under a constructor and replace inside it" in {
    val index = term("1")
    val replacement = term("NUM_CODE 1 0")
    val left = term("NUM_CODE 0 1")
    val right = term("NUM_CODE 1 0")

    val outer = force(
      rules.specAll(force(language.fact(Language.SubstituteSum)), List(index, replacement, left, right))
    )
    outer.hypotheses shouldBe empty
    outer.conclusion shouldBe proposition(
      "NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))) = " +
        "NUM_CODE 3 (NUM_PAIR (NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 0 1)) " +
        "(NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 1 0)))"
    )

    // And the right argument, which is zero, is left exactly as it was.
    val atZero = force(rules.specAll(force(language.fact(Language.SubstituteZero)), List(index, replacement)))
    atZero.conclusion shouldBe proposition(
      "NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 1 0) = NUM_CODE 1 0"
    )
    Derivation.axiomsOf(outer) should have size 2
  }

  /**
   * A quantifier over the variable being replaced binds it, and one over another does not.
   *
   * This is what makes `NUM_SUBST_FORM` a substitution for a **free** variable, and the published
   * equation does not say it: it says the answer is a conditional, which is not an answer until the
   * guard is decided. So both sides are decided here.
   *
   * **A `NUM_SUBST_FORM` that recursed under every quantifier would satisfy three of the four
   * equations**, and the fourth up to a conditional nobody resolved. It would also be wrong in the
   * way that matters most later: the diagonal lemma substitutes into a formula with a quantifier in
   * it, and a substitution that reached a bound variable would produce a different sentence.
   */
  it should "leave a formula alone under a quantifier that binds the variable" in {
    val replaced = term("1")
    val other = term("0")
    val replacement = term("NUM_CODE 1 0")
    val inner = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))")
    val rule = force(language.fact(Language.FormulaSubstituteUniversal))
    val condTrue = Kernel.instType(
      Map(Classical.TypeVariable -> numbers), force(chain.classical.fact(Classical.CondTrue)))
    val condFalse = Kernel.instType(
      Map(Classical.TypeVariable -> numbers), force(chain.classical.fact(Classical.CondFalse)))

    def answerAt(bound: Term, held: Either[Kernel.Thm, Kernel.Thm]): Kernel.Thm = {
      val instance = force(rules.specAll(rule, List(replaced, replacement, bound, inner)))
      val conditional = Term.destEq(instance.conclusion).map(_._2).getOrElse(fail("an equation"))
      val (guard, yes, no) = conditional match {
        case App(App(App(_, g), y), n) => (g, y, n)
        case term => fail(s"a conditional was expected: $term")
      }
      val stepped = held match {
        case Left(proved) =>
          force(rules.specAll(condTrue, List(guard, yes, no)).flatMap(rules.mp(_, proved)))
        case Right(refuted) =>
          force(rules.specAll(condFalse, List(guard, yes, no)).flatMap(rules.mp(_, refuted)))
      }
      force(Conv.trans(instance, stepped))
    }

    // Bound by the quantifier: the formula comes back exactly as it went in.
    val whenBound = answerAt(replaced, Left(Conv.refl(replaced)))
    whenBound.conclusion shouldBe proposition(
      "NUM_SUBST_FORM 1 (NUM_CODE 1 0) " +
        "(NUM_CODE 8 (NUM_PAIR 1 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))) = " +
        "NUM_CODE 8 (NUM_PAIR 1 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))"
    )

    // Bound by another: the substitution goes under it and the index is kept.
    val whenFree = answerAt(other, Right(force(chain.successor.distinct(other, replaced))))
    whenFree.conclusion shouldBe proposition(
      "NUM_SUBST_FORM 1 (NUM_CODE 1 0) " +
        "(NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))) = " +
        "NUM_CODE 8 (NUM_PAIR 0 (NUM_SUBST_FORM 1 (NUM_CODE 1 0) " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0)))))"
    )

    whenBound.hypotheses shouldBe empty
    whenFree.hypotheses shouldBe empty
    Derivation.axiomsOf(whenBound) should have size 2
  }

  /**
   * The equality clause hands its arguments to the TERM substitution and does not recurse.
   *
   * The one place the two substitutions meet, and the reason the formula one costs its
   * admissibility proof nothing at that clause: `NUM_SUBST_TERM` is already defined when
   * `NUM_SUBST_FORM` is, so the step does not mention the function it is defining.
   */
  it should "hand an equality's two sides to the term substitution" in {
    val instance = force(
      rules.specAll(
        force(language.fact(Language.FormulaSubstituteEquality)),
        List(term("1"), term("NUM_CODE 1 0"), term("NUM_CODE 0 1"), term("NUM_CODE 1 0"))
      )
    )
    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      "NUM_SUBST_FORM 1 (NUM_CODE 1 0) (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))) = " +
        "NUM_CODE 5 (NUM_PAIR (NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 0 1)) " +
        "(NUM_SUBST_TERM 1 (NUM_CODE 1 0) (NUM_CODE 1 0)))"
    )
    Derivation.axiomsOf(instance) should have size 2
  }

  /**
   * Substituting a term into a term gives a term, at a place where it is not already known.
   *
   * The published lemma is proved by course-of-values induction and this asserts it is **usable**:
   * instantiated at a compound code whose substitution is not the identity, with both premises
   * discharged from the introduction rules. What comes out is that the answer is a term without
   * anyone computing the answer, which is what the lemma is for.
   *
   * Its premises are satisfiable, which is the vacuity question for a lemma with two of them, and
   * this discharges both rather than saying so.
   */
  it should "keep a term a term when it substitutes into it" in {
    val index = term("1")
    val replacement = term("NUM_CODE 1 0")
    val subject = term("NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))")

    val zeroIsTerm = force(language.fact(Language.TermZero))
    val variableIsTerm = force(rules.spec(term("1"), force(language.fact(Language.TermVariable))))
    val subjectIsTerm = force(
      rules
        .specAll(force(language.fact(Language.TermSum)), List(term("NUM_CODE 0 1"), term("NUM_CODE 1 0")))
        .flatMap(rules.mp(_, variableIsTerm))
        .flatMap(rules.mp(_, zeroIsTerm))
    )

    val kept = force(
      rules
        .specAll(force(language.fact(Language.SubstituteKeepsTerms)), List(index, replacement, subject))
        .flatMap(rules.mp(_, subjectIsTerm))
        .flatMap(rules.mp(_, zeroIsTerm))
    )

    kept.hypotheses shouldBe empty
    kept.conclusion shouldBe proposition(
      "NUM_TERM (NUM_SUBST_TERM 1 (NUM_CODE 1 0) " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))"
    )
    Derivation.axiomsOf(kept) should have size 2
  }

  /**
   * Substituting into a formula gives a formula, at a quantified one.
   *
   * The subject is chosen to exercise the clause that differs from the terms': a quantifier, whose
   * answer is a conditional and whose bound index the lemma has to be right about **either way**.
   * The lemma is stated without that conditional, which is what makes it usable: the caller gets
   * "the answer is a formula" without deciding whether the index matched.
   *
   * That is the shape the induction scheme of PA will want, and it is why this lemma comes before
   * the axioms rather than with them.
   */
  it should "keep a formula a formula when it substitutes into a quantified one" in {
    val index = term("1")
    val replacement = term("NUM_CODE 1 0")
    val body = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))")
    val quantified = term(
      "NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))")

    val zeroIsTerm = force(language.fact(Language.TermZero))
    val variableIsTerm = force(rules.spec(term("1"), force(language.fact(Language.TermVariable))))
    val bodyIsFormula = force(
      rules
        .specAll(force(language.fact(Language.FormulaEquality)), List(term("NUM_CODE 0 1"), term("NUM_CODE 1 0")))
        .flatMap(rules.mp(_, variableIsTerm))
        .flatMap(rules.mp(_, zeroIsTerm))
    )
    val quantifiedIsFormula = force(
      rules
        .specAll(force(language.fact(Language.FormulaUniversal)), List(term("0"), body))
        .flatMap(rules.mp(_, bodyIsFormula))
    )

    val kept = force(
      rules
        .specAll(
          force(language.fact(Language.FormulaSubstituteKeepsFormulas)),
          List(index, replacement, quantified)
        )
        .flatMap(rules.mp(_, quantifiedIsFormula))
        .flatMap(rules.mp(_, zeroIsTerm))
    )

    kept.hypotheses shouldBe empty
    kept.conclusion shouldBe proposition(
      "NUM_FORM (NUM_SUBST_FORM 1 (NUM_CODE 1 0) " +
        "(NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))))"
    )
    Derivation.axiomsOf(kept) should have size 2
  }
  /**
   * The freeness condition discharged at a code, which is what it was missing.
   *
   * `Deduction`'s deduction theorem asks `!i. ~(NUM_FREE_FORM i h)` of its hypothesis, and until
   * `notFreeIn` existed nothing could supply that for any particular `h`: the theorem was proved
   * and applied to no formula anybody could name. So the assertion here is not that the walk
   * works, it is that **the two meet**: what comes out of the walk is exactly what the theorem
   * asks for, at all six of the axioms with a fixed code.
   *
   * The two doubly-quantified axioms are the ones worth having in the list. A code with one binder
   * exercises the quantifier clause once and could pass while the inequality it carries went
   * nowhere; with two, the inner walk has to find the right one of two inequalities at each
   * variable, and `NUM_PA_SUC_INJECTIVE` mentions both.
   */
  "The freeness of a closed code" should "be decided, which is what the deduction theorem needs" in {
    val named = Vector(
      "NUM_PA_SUC_NOT_ZERO",
      "NUM_PA_SUC_INJECTIVE",
      "NUM_PA_ADD_ZERO",
      "NUM_PA_ADD_SUC",
      "NUM_PA_MUL_ZERO",
      "NUM_PA_MUL_SUC"
    )

    named.foreach { name =>
      val member = force(language.fact(name))
      val code = member.conclusion match {
        case App(_, argument) => argument
        case other => fail(s"a claim about a code was expected, found $other")
      }

      withClue(s"$name: ") {
        val proved = force(language.notFreeIn(code))
        proved.hypotheses shouldBe empty
        Derivation.axiomsOf(proved) should have size 2

        // The shape the deduction theorem asks for, built independently and compared.
        val marker = Conv.freshVariable("i", numbers, Term.freeVariables(code))
        val free = force(LogicError.lift(Term.appAll(
          force(LogicError.lift(language.theory.constant(
            Language.FormulaFreeName, Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
          List(marker, code))))
        proved.conclusion shouldBe force(logic.mkForall(marker, force(logic.mkNot(free))))
      }
    }
  }

  /**
   * The shapes the axioms do not exercise, which is where the walk could have been wrong.
   *
   * All six axioms above bind index zero, and most of them bind it once. That leaves the case the
   * implementation is least obviously right about: the bound indices are carried as a **list** and
   * looked up with `find`, which returns the first match, so a shadowed index is where "first" and
   * "innermost" could come apart. They do not, because the list is prepended to on the way down,
   * and this is the assertion that says so rather than the reading.
   *
   * The other three are the neighbouring shapes: two distinct binders with the variable under the
   * outer one, the same with it under the inner one, and a quantifier binding an index its body
   * never mentions. None of the four appears in any code this repository builds today, which is
   * exactly why they are here: a walk verified only on the codes it was written for is verified
   * against its author's expectations.
   */
  it should "hold where a binder is shadowed, and where a binder binds nothing" in {
    val shapes = Vector(
      "the same index bound twice" ->
        ("NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 8 (NUM_PAIR 0 " +
          "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))))))"),
      "two binders, the outer one binding it" ->
        ("NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 8 (NUM_PAIR 1 " +
          "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))))))"),
      "two binders, the inner one binding it" ->
        ("NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 8 (NUM_PAIR 1 " +
          "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 1 0))))))"),
      "a binder its body never mentions" ->
        "NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 1 0))))"
    )

    shapes.foreach { case (what, source) =>
      withClue(s"$what: ") {
        val code = force(Parser.term(language.theory, language.notation, source, numbers))
        val proved = force(language.notFreeIn(code))
        proved.hypotheses shouldBe empty
        Derivation.axiomsOf(proved) should have size 2
      }
    }
  }

  /**
   * And one that is closed in one half and not in the other, which a coarser walk would accept.
   *
   * `(!v0. v0 = 0) ==> (v0 = 0)` binds the variable on the left and leaves it free on the right.
   * A walk that collected binders anywhere in the code rather than along the path to each variable
   * would call this closed. It is not, and the refusal names the index.
   */
  it should "refuse where a variable is bound in one half and free in the other" in {
    val code = force(Parser.term(language.theory, language.notation,
      ("NUM_CODE 7 (NUM_PAIR (NUM_CODE 8 (NUM_PAIR 0 " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))))) " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))))"),
      numbers))

    language.notFreeIn(code).isLeft shouldBe true
  }

  /**
   * A code that is not closed is refused, and the refusal names the index.
   *
   * The one case the walk can fail on, and the reason it must: `NUM_CODE 0 0` inside no quantifier
   * is the variable `v0` occurring free, the claim is **false** of such a code, and returning
   * anything at all would be worse than refusing. A procedure that answered here would be the one
   * way this machinery could mislead.
   */
  it should "be refused where the code has a variable nothing binds" in {
    val open = force(Parser.term(
      language.theory, language.notation,
      "NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0)))", numbers))

    language.notFreeIn(open).isLeft shouldBe true

    // And the same code under a quantifier binding that index is accepted, which is what makes the
    // refusal above about the freeness rather than about the shape.
    val closed = force(Parser.term(
      language.theory, language.notation,
      "NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0)))))",
      numbers))

    force(language.notFreeIn(closed)).hypotheses shouldBe empty
  }

}
