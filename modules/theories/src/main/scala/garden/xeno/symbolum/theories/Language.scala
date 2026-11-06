package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The language of the embedded theory, as numbers: a term of PA is a number, and being one is a
 * predicate.
 *
 * `docs/adr/0014` is the decision and this file is the first thing that spends it. There is no
 * datatype of terms and no new type; `NUM_TERM n` says that `n` is the code of a term of Peano
 * arithmetic, and it is defined by recursion on `n` rather than on a structure, because the codes
 * of a term's arguments are **smaller numbers** than the code of the term. `Numbering.CodeLeft` and
 * `Numbering.CodeRight` are what say so and are the whole reason the constructor carries a
 * successor.
 *
 * == The tags ==
 *
 * A code is `NUM_CODE t p`, a tag and a payload, and for terms the tags are:
 *
 *   - `0`, a **variable**, whose payload is its index. Any payload: there are infinitely many
 *     variables and nothing to check.
 *   - `1`, **zero**, whose payload must be `0`. The condition is not decoration: without it
 *     `NUM_CODE 1 5` would be a second code for the same term and the coding would stop being
 *     injective.
 *   - `2`, the **successor**, whose payload is the code of its argument.
 *   - `3` and `4`, **addition** and **multiplication**, whose payload is `NUM_PAIR a b` with `a`
 *     and `b` the codes of the two arguments.
 *
 * Tags from `5` are left for the formulas, which will share this constructor. They need not be
 * disjoint, since a term and a formula are different predicates, and they are kept disjoint anyway
 * so that a code carries which of the two it is without a context to read it in.
 *
 * == What the definition costs, and where ==
 *
 * The recursion is [[Descent]] and the price is not the definition, it is the **admissibility
 * condition** that theorem asks for: that the step gives the same answer when handed two functions
 * agreeing below the index. Every application of the function inside the step is at an argument the
 * step's own equation bounds, so the condition holds, and proving it is most of this file. It is
 * two directions of one implication over a four-way case split, with the two recursive clauses
 * doing the work and the other two carried across unchanged.
 *
 * The two directions are the same derivation with the roles exchanged, which is why it is written
 * once and called twice, and `Kernel.deductAntisym` is what turns the pair into the equation the
 * condition is stated as.
 */
final class Language private (
  val numbering: Numbering,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val successor: Successor,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  val peano: Peano = numbering.peano

  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /**
   * `|- !i. ~(NUM_FREE_FORM i c)` for a concrete closed code, by walking it.
   *
   * The condition `Deduction`'s deduction theorem asks of its hypothesis, and until this existed
   * nothing could discharge it at a code: the theorem was proved and applied to no formula anybody
   * could name. That is the gap this closes, and it is the reason the method is here rather than
   * beside its consumer, since `NUM_FREE_FORM` is this development's.
   *
   * **Nine clauses decide it and there is no search.** Four over formulas and five over terms, each
   * an equation this development publishes, applied to the shape the code actually has. The
   * recursion is over the Scala term, so what it costs is the size of the code and nothing else.
   *
   * **The quantifier is the only interesting case.** `NUM_FREE_FORM i (!b. body)` is
   * `COND (b = i) F (NUM_FREE_FORM i body)`, so the walk splits on whether the index being asked
   * about is the one bound here. If it is, the answer is falsity outright. If it is not, the walk
   * descends into the body **carrying that inequality**, which is what lets a variable inside be
   * refused later: `NUM_FREE_TERM i (NUM_CODE 0 b)` is `b = i`, and the inequality is exactly its
   * negation. A code with two quantifiers carries two, and that is the whole bookkeeping.
   *
   * **It refuses rather than guesses**, and the case it refuses on is the one that matters: a
   * variable no enclosing quantifier binds. Such a code is not closed and the claim is false of it,
   * so returning anything would be worse than refusing. The refusal names the index.
   */
  /**
   * `|- NUM_SUBST_FORM i t c = c'` for a concrete formula code, by computing the substitution.
   *
   * **The conclusion of two of the eight schemes is unreadable without this.** Specialisation and
   * replacement both produce a code containing `NUM_SUBST_FORM i t p`, left standing, and the
   * caller wanted the code that substitution denotes: what comes out of `NUM_PROV_SPECIALISE` at
   * PA's axiom for addition is provability of `NUM_SUBST_FORM 0 (NUM_NUMERAL m) <body>`, and the
   * claim anyone means by that is provability of the code of `numeral m + 0 = numeral m`. The two
   * are the same number and nothing said so.
   *
   * **It is a rule set rather than a walk, which is the opposite of [[notFreeIn]] and was
   * measured rather than assumed.** The sibling walks the nine freeness clauses by hand because
   * its guard compares the index asked about, a variable, with a binder: that is a case split, and
   * each branch carries a hypothesis down into the recursion. Here every index in the code is a
   * concrete numeral and so is the one being replaced, so each guard is decided outright and
   * nothing is carried. What is left is nine equations and a rewriter that already exists. The
   * walk was written first and abandoned at the measurement: it would have been two hundred lines
   * to reach what these fifty do.
   *
   * Three kinds of rule go in. The nine clauses of the two substitutions, which are equations
   * already. `COND T a b = a` and `COND F a b = b`, derived here because `COND_TRUE` and
   * `COND_FALSE` carry their guard as a hypothesis and a rewrite rule is an equation and nothing
   * else. And one decision per index the code mentions, `(j = i) = T` by reflexivity or
   * `(j = i) = F` through `Successor.distinct`, which is where a code whose indices are not
   * numerals is refused and refused by name.
   *
   * The result is checked for a residue rather than handed back as it comes: a right side still
   * carrying a substitution or a conditional means an index went undecided, and returning that
   * equation would be returning a true statement that does not answer the question.
   */
  def substituteIn(
    index: Term,
    replacement: Term,
    code: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
    val classical = numbering.peano.naturals.classical

    for {
      coding <- LogicError.lift(theory.constant(Numbering.CodeName, arithmetic))
      pairing <- LogicError.lift(theory.constant(Numbering.PairName, arithmetic))
      variableTag <- Parser.term(theory, notation, "0", numbers)
      quantifierTag <- Parser.term(theory, notation, "8", numbers)

      /* Every index the code mentions, from the two positions that can carry one. */
      indices = {
        def collect(subject: Term): Vector[Term] = subject match {
          case App(App(head, tag), payload) if head == coding && tag == variableTag =>
            Vector(payload)
          case App(App(head, tag), App(App(join, left), right))
              if head == coding && tag == quantifierTag && join == pairing =>
            left +: collect(right)
          case App(left, right) => collect(left) ++ collect(right)
          case _ => Vector.empty
        }
        collect(code).distinct
      }

      decisions <- indices.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        (carried, mentioned) =>
          for {
            found <- carried
            guard <- LogicError.lift(Term.eq(mentioned, index))
            decided <-
              if (mentioned == index) rules.eqTruthIntro(Kernel.refl(mentioned))
              else
                for {
                  apart <- successor.distinct(mentioned, index)
                  assumed <- LogicError.lift(Kernel.assume(guard))
                  toFalsity <- rules.notElim(apart, assumed)
                  fromFalsity <- LogicError
                    .lift(Kernel.assume(logic.falsity))
                    .flatMap(rules.falsityElim(guard, _))
                  equated <- Conv.sym(Kernel.deductAntisym(toFalsity, fromFalsity))
                } yield equated
          } yield found :+ decided
      }

      conditionals <- Language.conditionalRules(logic, classical, numbers)

      clauses <- Vector(
        Language.SubstituteVariable, Language.SubstituteZero, Language.SubstituteSuccessor,
        Language.SubstituteSum, Language.SubstituteProduct,
        Language.FormulaSubstituteEquality, Language.FormulaSubstituteNegation,
        Language.FormulaSubstituteImplication, Language.FormulaSubstituteUniversal
      ).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
        carried.flatMap(found => fact(name).map(found :+ _))
      }

      ruleSet <- Rewrite.Rule.all(logic, clauses ++ conditionals ++ decisions)
      substituting <- LogicError.lift(theory.constant(
        Language.FormulaSubstituteName,
        Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers)))))
      subject <- LogicError.lift(Term.appAll(substituting, List(index, replacement, code)))
      equation <- Rewrite.rewrite(ruleSet, subject)

      answer <- Term
        .destEq(equation.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", equation.conclusion))
      _ <-
        if (residue(answer)) Left(NotOfForm("a code with the substitution carried out", answer))
        else Right(())
    } yield equation
  }

  /** Whether a term still carries a substitution or an undecided conditional. */
  private def residue(subject: Term): Boolean = subject match {
    case Const(name, _) =>
      name == Language.FormulaSubstituteName || name == Language.SubstituteName ||
        name == Classical.Conditional
    case App(left, right) => residue(left) || residue(right)
    case _ => false
  }

  def notFreeIn(code: Term): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
    val classical = numbering.peano.naturals.classical

    def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new Language.RefusedWalking(error), identity)

    def applied(head: Term, arguments: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, arguments)))
    def digits(source: String): Term = force(Parser.term(theory, notation, source, numbers))

    val pairing = force(LogicError.lift(theory.constant(Numbering.PairName, arithmetic)))
    val coding = force(LogicError.lift(theory.constant(Numbering.CodeName, arithmetic)))
    val formulaFree = force(LogicError.lift(theory.constant(
      Language.FormulaFreeName, Type.fun(numbers, Type.fun(numbers, Type.Bool)))))
    val negation =
      force(LogicError.lift(theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool))))

    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool),
      force(classical.fact(Classical.CondTrue)))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool),
      force(classical.fact(Classical.CondFalse)))
    val deMorgan = force(classical.fact(Classical.DeMorganDisjunction))
    val middle = force(classical.fact(Classical.ExcludedMiddle))

    def clause(name: String): Kernel.Thm = force(fact(name))
    def assumeThat(subject: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(subject)))

    def destCode(subject: Term): (Term, Term) = subject match {
      case App(App(head, tag), payload) if head == coding => (tag, payload)
      case other => throw new Language.RefusedWalking(NotOfForm("a code", other))
    }
    def destPair(subject: Term): (Term, Term) = subject match {
      case App(App(head, left), right) if head == pairing => (left, right)
      case other => throw new Language.RefusedWalking(NotOfForm("a pair", other))
    }

    /** From `X = F`, that `~X`. */
    def notFromFalsity(equation: Kernel.Thm): Kernel.Thm = {
      val subject = Term
        .destEq(equation.conclusion)
        .map(_._1)
        .getOrElse(throw new Language.RefusedWalking(
          NotOfForm("an equation", equation.conclusion)))
      force(rules.notIntro(subject,
        force(LogicError.lift(Kernel.eqMp(equation, assumeThat(subject))))))
    }

    /** From `X = Y` and `~Y`, that `~X`. */
    def notAcross(equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(Conv.apTerm(negation, equation)
        .flatMap(Conv.sym)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, held))))

    /** From `~A` and `~B`, that `~(A \/ B)`. */
    def neither(left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm = {
      def subjectOf(theorem: Kernel.Thm): Term = logic
        .destNot(theorem.conclusion)
        .getOrElse(throw new Language.RefusedWalking(
          NotOfForm("a negation", theorem.conclusion)))
      val instance = force(rules.specAll(deMorgan, List(subjectOf(left), subjectOf(right))))
      force(rules.conjIntro(left, right)
        .flatMap(both => Conv.sym(instance)
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, both)))))
    }

    def bothParts(
      index: Term, bound: List[(Term, Kernel.Thm)], payload: Term, name: String,
      walk: (Term, List[(Term, Kernel.Thm)], Term) => Kernel.Thm
    ): Kernel.Thm = {
      val (left, right) = destPair(payload)
      notAcross(
        force(rules.specAll(clause(name), List(index, left, right))),
        neither(walk(index, bound, left), walk(index, bound, right)))
    }

    def inTerm(index: Term, bound: List[(Term, Kernel.Thm)], subject: Term): Kernel.Thm = {
      val (tag, payload) = destCode(subject)

      if (tag == digits("0"))
        bound.find(_._1 == payload) match {
          case Some((_, notEqual)) =>
            notAcross(
              force(rules.specAll(clause(Language.FreeVariable), List(index, payload))),
              notEqual)
          case None =>
            throw new Language.RefusedWalking(NotOfForm(
              s"a closed code; the variable at index $payload is bound by nothing", subject))
        }
      else if (tag == digits("1"))
        notFromFalsity(force(rules.spec(index, clause(Language.FreeZero))))
      else if (tag == digits("2"))
        notAcross(
          force(rules.specAll(clause(Language.FreeSuccessor), List(index, payload))),
          inTerm(index, bound, payload))
      else if (tag == digits("3"))
        bothParts(index, bound, payload, Language.FreeSum, inTerm)
      else if (tag == digits("4"))
        bothParts(index, bound, payload, Language.FreeProduct, inTerm)
      else
        throw new Language.RefusedWalking(NotOfForm("a term's tag", tag))
    }

    def inFormula(index: Term, bound: List[(Term, Kernel.Thm)], subject: Term): Kernel.Thm = {
      val (tag, payload) = destCode(subject)

      if (tag == digits("5")) {
        val (left, right) = destPair(payload)
        notAcross(
          force(rules.specAll(clause(Language.FormulaFreeEquality), List(index, left, right))),
          neither(inTerm(index, bound, left), inTerm(index, bound, right)))
      } else if (tag == digits("6"))
        notAcross(
          force(rules.specAll(clause(Language.FormulaFreeNegation), List(index, payload))),
          inFormula(index, bound, payload))
      else if (tag == digits("7"))
        bothParts(index, bound, payload, Language.FormulaFreeImplication, inFormula)
      else if (tag == digits("8")) {
        val (bindsAt, body) = destPair(payload)
        val equation = force(rules.specAll(
          clause(Language.FormulaFreeUniversal), List(index, bindsAt, body)))
        val guard = force(LogicError.lift(Term.eq(bindsAt, index)))
        val inner = applied(formulaFree, List(index, body))
        val split = force(rules.spec(guard, middle))
        val (whenSame, whenOther) = logic
          .destDisj(split.conclusion)
          .getOrElse(throw new Language.RefusedWalking(
            NotOfForm("a disjunction", split.conclusion)))

        val fromSame = notFromFalsity(force(Conv.trans(equation,
          force(rules.specAll(condTrue, List(guard, logic.falsity, inner))
            .flatMap(rules.mp(_, assumeThat(whenSame)))))))
        val fromOther = {
          val held = assumeThat(whenOther)
          notAcross(
            force(Conv.trans(equation,
              force(rules.specAll(condFalse, List(guard, logic.falsity, inner))
                .flatMap(rules.mp(_, held))))),
            inFormula(index, (bindsAt, held) :: bound, body))
        }
        force(rules.disjElim(split, fromSame, fromOther))
      } else
        throw new Language.RefusedWalking(NotOfForm("a formula's tag", tag))
    }

    try {
      val index = Conv.freshVariable("i", numbers, Term.freeVariables(code))
      rules.gen(index, inFormula(index, Nil, code))
    } catch { case refused: Language.RefusedWalking => Left(refused.error) }
  }
}

object Language {

  /** Carry a refusal out of [[Language.notFreeIn]], which walks a code in direct style. */
  private final class RefusedWalking(val error: LogicError) extends RuntimeException


  /** `NUM_TERM n` says `n` codes a term of the embedded theory. */
  val TermName: String = "NUM_TERM"

  /**
   * `|- !n. NUM_TERM n = (?t p. n = NUM_CODE t p /\ ...)`
   *
   * The recursion equation, which is what [[Descent]] returns and the only fact about [[TermName]]
   * that is not derived from another. Everything below is this equation read in one direction at
   * one tag.
   */
  val TermCases: String = "NUM_TERM_CASES"

  /** `|- !i. NUM_TERM (NUM_CODE 0 i)`. Every variable is a term, and there is no condition. */
  val TermVariable: String = "NUM_TERM_VAR"

  /** `|- NUM_TERM (NUM_CODE 1 0)`. Zero is a term, and its payload is pinned. */
  val TermZero: String = "NUM_TERM_ZERO"

  /** `|- !t. NUM_TERM t ==> NUM_TERM (NUM_CODE 2 t)`. */
  val TermSuccessor: String = "NUM_TERM_SUC"

  /** `|- !a b. NUM_TERM a ==> NUM_TERM b ==> NUM_TERM (NUM_CODE 3 (NUM_PAIR a b))`. */
  val TermSum: String = "NUM_TERM_ADD"

  /** `|- !a b. NUM_TERM a ==> NUM_TERM b ==> NUM_TERM (NUM_CODE 4 (NUM_PAIR a b))`. */
  val TermProduct: String = "NUM_TERM_MUL"

  /**
   * `|- ~(NUM_TERM ZERO)`
   *
   * Zero codes nothing, and it is refused by the **shape** of a code rather than by a clause about
   * it: every term is `NUM_CODE t p` and `Numbering.CodeNotZero` says no code vanishes. That is the
   * second job the constructor's successor does, and this is where it is collected.
   */
  val TermNotZero: String = "NUM_TERM_NOT_ZERO"

  /** `NUM_FORM n` says `n` codes a formula of the embedded theory. */
  val FormulaName: String = "NUM_FORM"

  /**
   * `|- !n. NUM_FORM n = (?t p. n = NUM_CODE t p /\ ...)`
   *
   * The recursion equation for the formulas, and the tags are `5` to `8`: an **equality** of two
   * terms, a **negation**, an **implication**, and a **universal quantifier** over a variable index.
   *
   * Four connectives and not six, because the others are definitions in the object language rather
   * than syntax: disjunction, conjunction and the existential are abbreviations built from these,
   * and giving each a tag would mean proving every clause of `Prov` four more times for nothing.
   * This is the usual first-order signature and it is what `docs/adr/0013` means by PA.
   */
  val FormulaCases: String = "NUM_FORM_CASES"

  /**
   * `|- !a b. NUM_TERM a ==> NUM_TERM b ==> NUM_FORM (NUM_CODE 5 (NUM_PAIR a b))`
   *
   * The only clause of either predicate that asks something of the **other** one, and it is a side
   * condition rather than a recursion: `NUM_TERM` is already defined when the formulas are, so the
   * step does not mention the function it is defining and that clause costs the admissibility proof
   * nothing at all. It is why the formulas are defined second and not why they are harder.
   */
  val FormulaEquality: String = "NUM_FORM_EQ"

  /** `|- !p. NUM_FORM p ==> NUM_FORM (NUM_CODE 6 p)`. */
  val FormulaNegation: String = "NUM_FORM_NOT"

  /** `|- !p q. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM (NUM_CODE 7 (NUM_PAIR p q))`. */
  val FormulaImplication: String = "NUM_FORM_IMP"

  /**
   * `|- !i p. NUM_FORM p ==> NUM_FORM (NUM_CODE 8 (NUM_PAIR i p))`
   *
   * The quantifier, whose payload pairs a **variable index** with a formula. It is the one clause
   * in this file that recurses on the second component of a pair and not on both, because the first
   * is an index and not a code, and that shape is why [[Clause]] has a fourth entry.
   *
   * Any index: a quantifier binding a variable that does not occur is a formula, and refusing it
   * would make the syntax depend on a free-variable analysis this development has not got.
   */
  val FormulaUniversal: String = "NUM_FORM_ALL"

  /** `|- ~(NUM_FORM ZERO)`, for the reason [[TermNotZero]] holds: no code vanishes. */
  val FormulaNotZero: String = "NUM_FORM_NOT_ZERO"

  /**
   * `NUM_NUMERAL n` is the code of the object language's term for `n`, which is `S` applied `n`
   * times to zero.
   *
   * **The bridge between the two levels, and the first place a number becomes a term about that
   * number.** Everything above here needs it: a claim of the embedded theory about a particular
   * number is a formula with this term in it, the diagonal lemma substitutes one of these, and
   * representability is the statement that a function on numbers is tracked by a formula relating
   * these.
   *
   * A primitive recursion and not a course-of-values one: the numeral for `SUC n` is built from the
   * numeral for `n` and nothing smaller, so `Recursion` suffices where the syntactic predicates
   * needed `Descent`.
   */
  val NumeralName: String = "NUM_NUMERAL"

  /** `|- NUM_NUMERAL ZERO = NUM_CODE 1 0`. The object language's zero is the meta level's. */
  val NumeralAtZero: String = "NUM_NUMERAL_ZERO"

  /** `|- !n. NUM_NUMERAL (SUC n) = NUM_CODE 2 (NUM_NUMERAL n)`. */
  val NumeralAtSuccessor: String = "NUM_NUMERAL_SUC"

  /** `|- !n. NUM_TERM (NUM_NUMERAL n)`. Every numeral is a term, which is what makes it usable. */
  val NumeralIsTerm: String = "NUM_NUMERAL_TERM"

  /**
   * `|- !n. NUM_CLOSED (NUM_NUMERAL n)`. Being a term is not enough: three schemes want this one.
   *
   * [[ClosedName]] is the condition `NUM_LOGIC_SPECIALISE` and `NUM_LOGIC_REPLACE` carry, and the
   * library stated no closure at all until this landed. What that cost is easy to miss, because
   * the two are theorems either way: a scheme whose side condition nothing can discharge is
   * provable and unusable, and those two were in exactly that position at every term but one.
   * `LanguageSpec` had discharged it once, at the object language's zero, by walking the freeness
   * clauses by hand inside the test that needed an instance of specialisation.
   *
   * A family and not another instance, which is the difference that matters to what comes next.
   * Goedel's argument substitutes the numeral of a number, and there is one of those per number;
   * a development that can close the numeral of `0` and no other cannot state that PA proves its
   * own arithmetic, which is the first brick of Sigma-1 completeness. The zero's case is now a
   * corollary of this one, [[NumeralAtZero]] being the equation between them.
   *
   * The proof is the induction the numeral's own recurrence asks for, and neither case reaches for
   * anything but a freeness clause. What is worth knowing is that the predicate does refuse: a
   * variable's own code is not closed, `NUM_FREE_TERM i (NUM_CODE 0 i)` being `i = i`, and
   * `LanguageSpec` derives that beside this so a freeness predicate that quietly went vacuous would
   * fail a test rather than make this one easier.
   */
  val NumeralIsClosed: String = "NUM_NUMERAL_CLOSED"

  /**
   * `|- !m n. NUM_NUMERAL m = NUM_NUMERAL n ==> m = n`
   *
   * Distinct numbers get distinct numerals, without which the object language could not tell two
   * numbers apart and no representability argument would mean anything. It is where the tags earn
   * their disjointness a second time: at the base the two sides carry tags `1` and `2`, and
   * `Successor.distinct` is what says those differ.
   */
  val NumeralInjective: String = "NUM_NUMERAL_INJECTIVE"

  /**
   * `NUM_SUBST_TERM i t s` puts the term `t` where the variable `i` stood in the term `s`.
   *
   * **The first function over codes, and why the projections had to come first.** A predicate says
   * a code *is* `NUM_CODE k p` for some `k` and `p` and works under the existential; a function has
   * to build an answer out of the parts, so it has to name them, and `NUM_TAG`, `NUM_PAYLOAD`,
   * `NUM_FST` and `NUM_SND` are those names.
   *
   * **The guards are equations about `s` and not about its tag**, which is the thing to understand
   * before reading the step. `NUM_TAG s = 2` would be the natural way to write "the tag is two", and
   * the recursion would not be admissible with it: at a number that is not a code at all,
   * `NUM_TAG s` is a choice that could fall on two, and then the branch would recurse at
   * `NUM_PAYLOAD s`, which nothing bounds. Written as `s = NUM_CODE 2 (NUM_PAYLOAD s)` the guard
   * says the shape, `Numbering.CodeLeft` and `Numbering.CodeRight` bound the parts, and the
   * recursion descends. The bound being the construction's reason, which `docs/adr/0014` says, is
   * this file's second use of it and the one where it could have gone wrong.
   *
   * **It is blind to capture and that is sound here.** Nothing checks whether `t`'s variables are
   * bound where they land, and for the substitution Goedel's argument performs they cannot be: what
   * is substituted is a **numeral**, which is closed. Substitution of an open term would need a
   * freshness condition this development has not got, and no consumer here wants one.
   */
  val SubstituteName: String = "NUM_SUBST_TERM"

  /** `|- !i t j. NUM_SUBST_TERM i t (NUM_CODE 0 j) = COND (j = i) t (NUM_CODE 0 j)`. */
  val SubstituteVariable: String = "NUM_SUBST_TERM_VAR"

  /** `|- !i t. NUM_SUBST_TERM i t (NUM_CODE 1 0) = NUM_CODE 1 0`. Zero has nothing to replace. */
  val SubstituteZero: String = "NUM_SUBST_TERM_ZERO"

  /** `|- !i t s. NUM_SUBST_TERM i t (NUM_CODE 2 s) = NUM_CODE 2 (NUM_SUBST_TERM i t s)`. */
  val SubstituteSuccessor: String = "NUM_SUBST_TERM_SUC"

  /**
   * `|- !i t a b. NUM_SUBST_TERM i t (NUM_CODE 3 (NUM_PAIR a b)) =
   * NUM_CODE 3 (NUM_PAIR (NUM_SUBST_TERM i t a) (NUM_SUBST_TERM i t b))`
   */
  val SubstituteSum: String = "NUM_SUBST_TERM_ADD"

  /** The same at tag `4`. */
  val SubstituteProduct: String = "NUM_SUBST_TERM_MUL"

  /**
   * `NUM_SUBST_FORM i t p` puts the term `t` where the **free** variable `i` stood in the formula
   * `p`.
   *
   * The same recursion over the four formula tags, with two differences that are the whole content.
   *
   * **The equality clause calls the TERM substitution and does not recurse.** An equality relates
   * two terms, so what happens inside it is [[SubstituteName]]'s business, which is already defined
   * when this is. That clause costs the admissibility proof nothing, exactly as the equality clause
   * of `NUM_FORM` costs its own nothing, and for the same reason.
   *
   * **The quantifier clause compares the bound index with the one being replaced**, and leaves the
   * formula alone where they agree. That is what makes this a substitution for a **free** variable:
   * `!v_i. p` has no free `v_i` in it, so nothing in it is replaced. The comparison cannot be
   * settled here, since both indices are variables, so it stays a conditional in the published
   * statement and the caller decides it, which is what the variable clause of the term
   * substitution already does.
   */
  val FormulaSubstituteName: String = "NUM_SUBST_FORM"

  /**
   * `|- !i t a b. NUM_SUBST_FORM i t (NUM_CODE 5 (NUM_PAIR a b)) =
   * NUM_CODE 5 (NUM_PAIR (NUM_SUBST_TERM i t a) (NUM_SUBST_TERM i t b))`
   */
  val FormulaSubstituteEquality: String = "NUM_SUBST_FORM_EQ"

  /** `|- !i t p. NUM_SUBST_FORM i t (NUM_CODE 6 p) = NUM_CODE 6 (NUM_SUBST_FORM i t p)`. */
  val FormulaSubstituteNegation: String = "NUM_SUBST_FORM_NOT"

  /** The same under an implication, on both sides of the pair. */
  val FormulaSubstituteImplication: String = "NUM_SUBST_FORM_IMP"

  /**
   * `|- !i t j p. NUM_SUBST_FORM i t (NUM_CODE 8 (NUM_PAIR j p)) =
   * COND (j = i) (NUM_CODE 8 (NUM_PAIR j p)) (NUM_CODE 8 (NUM_PAIR j (NUM_SUBST_FORM i t p)))`
   *
   * The clause that makes it a substitution for a free variable, and the conditional in it is the
   * statement rather than an unfinished proof.
   */
  val FormulaSubstituteUniversal: String = "NUM_SUBST_FORM_ALL"

  /**
   * `|- !i t s. NUM_TERM s ==> NUM_TERM t ==> NUM_TERM (NUM_SUBST_TERM i t s)`
   *
   * Substituting a term into a term gives a term, which is the first thing anything above here has
   * to know and the first consumer of `Peano.NUM_STRONG_INDUCTION`.
   *
   * **Ordinary induction cannot reach it.** The claim at a code follows from the claim at the codes
   * **inside** it, and those are smaller numbers rather than predecessors: `NUM_CODE 3 (NUM_PAIR a
   * b)` has `a` and `b` below it by the pairing's bound and the constructor's, and neither is its
   * predecessor. Course-of-values induction is exactly the shape of that, which is why it was
   * derived first.
   *
   * The variable clause is the one with a case split rather than a recursion: what comes back there
   * is `t` or the variable itself, and both are terms for reasons already in hand.
   */
  val SubstituteKeepsTerms: String = "NUM_SUBST_TERM_TERM"

  /**
   * `|- !i t s. NUM_TERM s ==> ~(NUM_FREE_TERM i s) ==> NUM_SUBST_TERM i t s = s`
   *
   * Substituting for a variable that does not occur changes nothing. It reads as something the
   * library must already have had and did not: until this landed, every fact about the two
   * substitutions was either a clause of their definitions or the statement that they preserve
   * well-formedness, and nothing at all said when a substitution does not move.
   *
   * **What wanted it is the object theory's equality**, and the shape of the need is worth stating
   * because it is not obvious from the name. `NUM_LOGIC_REPLACE` is the only scheme that can give
   * symmetry, transitivity or congruence, and each of those is obtained by choosing a formula with
   * a hole: symmetry takes `v_i = t` and needs its two instances to be `t = t` and `u = t`. Getting
   * there means substituting into a formula that MENTIONS the closed term `t`, and the walk stops
   * dead at `t` unless something says the substitution leaves it alone. [[Language.substituteIn]]
   * cannot help, because it computes at a concrete code and `t` here is a variable standing for any
   * closed term.
   *
   * So the rules of equality are stated over arbitrary closed terms rather than over numerals, and
   * this is the fact that buys the difference. Numerals would have been the cheaper lemma, one
   * induction on `NUM_NUMERAL` rather than a course-of-values induction over every code, and it
   * would have been enough for Goedel's argument alone and for nothing else the object theory has
   * to do.
   */
  val SubstituteIdle: String = "NUM_SUBST_TERM_NOT_FREE"

  /**
   * `|- !i t p. NUM_FORM p ==> NUM_TERM t ==> NUM_FORM (NUM_SUBST_FORM i t p)`
   *
   * Substituting a term into a formula gives a formula, which is what the induction scheme of PA
   * needs before it can be stated: every instance of it is a formula built by substituting into
   * another one, and a scheme whose instances might not be formulas is not a scheme.
   *
   * The same induction as [[SubstituteKeepsTerms]] over a different clause table, and two clauses
   * are worth naming. The **equality** clause asks nothing of the induction hypothesis: its two
   * arguments are terms, so what keeps them terms is that lemma, which is finished. The
   * **quantifier** clause is the one with a conditional, and where the index matches the formula
   * comes back untouched and is well formed by the premise rather than by anything rebuilt.
   */
  val FormulaSubstituteKeepsFormulas: String = "NUM_SUBST_FORM_FORM"

  /* ---------------------------------------------------- the object language, as it reads */

  /**
   * An expression of the object language, as a tree, which is what the codes and their proofs are
   * both generated from.
   *
   * A code is a nest of `NUM_CODE` and `NUM_PAIR` six deep and is unreadable as a literal, so the
   * first version of this wrote the six axioms through text-building functions. That works until
   * something has to **prove** a code is a formula, and then the grammar is written twice: once as
   * text and once as a composition of the introduction rules. Two encodings of one grammar is the
   * defect this repository keeps finding, and the repair is always to delete the second rather than
   * to keep the two in step.
   *
   * So the tree is the source and both come off it. [[render]] gives the text a reader checks by
   * eye against the informal statement, and [[wellFormedFormula]] walks the same tree composing the
   * rules. A constructor added here without a case in the prover does not compile.
   *
   * Two leaves are not object syntax and are here because the induction scheme needs them.
   * [[Obj.Hole]] is a formula **variable**, well formed by hypothesis rather than by construction,
   * and [[Obj.Substituted]] is a substitution left standing in the code, which is what makes the
   * scheme a scheme.
   */
  private enum Obj {
    case Var(index: String)
    case Zero
    case Succ(inner: Obj)
    case Sum(left: Obj, right: Obj)
    case Prod(left: Obj, right: Obj)
    case Eq(left: Obj, right: Obj)
    case Not(inner: Obj)
    case Implies(left: Obj, right: Obj)
    case Forall(index: String, inner: Obj)
    case Hole(name: String)
    case TermHole(name: String)
    case Substituted(index: String, replacement: Obj, inner: Obj)
  }

  /**
   * A scheme: a code with holes in it, the conditions its holes carry, and what it is called.
   *
   * The axioms of PA have one of these and the logical axioms are nothing but these, so the two
   * shapes a scheme is read in are written once here. `disjunct` is how it appears inside the
   * definition of the set, existentially quantified with its conditions as conjuncts; `statement`
   * is how a caller wants it, universally quantified with its conditions as antecedents.
   * [[schemeMembership]] is the walk from the second to the first, and it is the same walk whatever
   * the arity.
   */
  /**
   * A condition a scheme puts on one of its holes.
   *
   * Written as a value rather than as text because it is read three times and in three ways: as the
   * conjunct inside the definition of the set, as the antecedent of the published statement, and,
   * when a scheme's code has to be shown to be a formula, as the theorem that discharges the hole
   * it names. The third reading is what makes text unusable: recovering "this antecedent is what
   * says `p` is a formula" by matching on the string holds until somebody writes the same condition
   * with different spacing.
   *
   * [[Condition.Closed]] and [[Condition.NotFree]] discharge no hole. They are what the
   * substitution's blindness to capture costs: `NUM_SUBST_TERM` is sound where the replacement is
   * closed, so the schemes that substitute say so, and the scheme that generalises says the index
   * does not occur.
   */
  private enum Condition {
    case IsFormula(hole: String)
    case IsTerm(hole: String)
    case Closed(hole: String)
    case NotFree(index: String, hole: String)

    def text: String = this match {
      case Condition.IsFormula(hole)      => s"$FormulaName $hole"
      case Condition.IsTerm(hole)         => s"$TermName $hole"
      case Condition.Closed(hole)         => s"$ClosedName $hole"
      case Condition.NotFree(index, hole) => s"~($FormulaFreeName $index $hole)"
    }
  }

  private final case class Scheme(
    name: String,
    binders: List[String],
    premises: List[Condition],
    tree: Obj
  ) {

    /** `?b1 ... bn. prem1 /\ ... /\ premk /\ <subject> = <the code>`. */
    def disjunct(subject: String): String = {
      val body = (premises.map(_.text) :+ s"$subject = (${render(tree)})").mkString(" /\\ ")
      binders.foldRight(body)((binder, inner) => s"?$binder:num. $inner")
    }

    /** `!b1 ... bn. prem1 ==> ... ==> premk ==> <the set> <the code>`. */
    def statement(head: String): String = {
      val conclusion = s"$head (${render(tree)})"
      val body = premises.foldRight(conclusion)((premise, inner) => s"${premise.text} ==> $inner")
      s"!${binders.map(binder => s"$binder:num").mkString(" ")}. $body"
    }
  }

  /** The tags are `0` to `4` for the terms and `5` to `8` for the formulas, and this is where. */
  private def render(expression: Obj): String = expression match {
    case Obj.Var(index)          => s"NUM_CODE 0 ($index)"
    case Obj.Zero                => "NUM_CODE 1 0"
    case Obj.Succ(inner)         => s"NUM_CODE 2 (${render(inner)})"
    case Obj.Sum(left, right)    => s"NUM_CODE 3 (NUM_PAIR (${render(left)}) (${render(right)}))"
    case Obj.Prod(left, right)   => s"NUM_CODE 4 (NUM_PAIR (${render(left)}) (${render(right)}))"
    case Obj.Eq(left, right)     => s"NUM_CODE 5 (NUM_PAIR (${render(left)}) (${render(right)}))"
    case Obj.Not(inner)          => s"NUM_CODE 6 (${render(inner)})"
    case Obj.Implies(left, right) =>
      s"NUM_CODE 7 (NUM_PAIR (${render(left)}) (${render(right)}))"
    case Obj.Forall(index, inner) => s"NUM_CODE 8 (NUM_PAIR ($index) (${render(inner)}))"
    case Obj.Hole(name)           => name
    case Obj.TermHole(name)       => name
    case Obj.Substituted(index, replacement, inner) =>
      s"$FormulaSubstituteName $index (${render(replacement)}) (${render(inner)})"
  }

  /**
   * The six non-logical axioms of PA, written so that a reader can check them by eye.
   *
   * The axioms are the usual six, and the seventh of Robinson's Q, that every non-zero number is a
   * successor, is **not** among them and is not missing: it follows from the induction scheme,
   * which is what makes PA stronger than Q and is `docs/adr/0013`'s decision.
   *
   * The two variables are `v0` and `v1`. An object variable is an index rather than a name, and
   * which index is arbitrary: nothing below reads them and the scheme quantifies its own.
   */
  private val axiomTrees: Vector[(String, Obj)] = {
    val x = Obj.Var("0")
    val y = Obj.Var("1")
    Vector(
      "NUM_PA_SUC_NOT_ZERO" -> Obj.Forall("0", Obj.Not(Obj.Eq(Obj.Succ(x), Obj.Zero))),
      "NUM_PA_SUC_INJECTIVE" ->
        Obj.Forall("0", Obj.Forall("1",
          Obj.Implies(Obj.Eq(Obj.Succ(x), Obj.Succ(y)), Obj.Eq(x, y)))),
      "NUM_PA_ADD_ZERO" -> Obj.Forall("0", Obj.Eq(Obj.Sum(x, Obj.Zero), x)),
      "NUM_PA_ADD_SUC" ->
        Obj.Forall("0", Obj.Forall("1",
          Obj.Eq(Obj.Sum(x, Obj.Succ(y)), Obj.Succ(Obj.Sum(x, y))))),
      "NUM_PA_MUL_ZERO" -> Obj.Forall("0", Obj.Eq(Obj.Prod(x, Obj.Zero), Obj.Zero)),
      "NUM_PA_MUL_SUC" ->
        Obj.Forall("0", Obj.Forall("1",
          Obj.Eq(Obj.Prod(x, Obj.Succ(y)), Obj.Sum(Obj.Prod(x, y), x))))
    )
  }

  /** The induction scheme at an index `i` and a formula `p`, both free. */
  private val inductionScheme: Scheme = Scheme(
    "NUM_PA_INDUCTION",
    List("i", "p"),
    List(Condition.IsFormula("p")),
    Obj.Implies(
      Obj.Substituted("i", Obj.Zero, Obj.Hole("p")),
      Obj.Implies(
        Obj.Forall("i", Obj.Implies(
          Obj.Hole("p"),
          Obj.Substituted("i", Obj.Succ(Obj.Var("i")), Obj.Hole("p")))),
        Obj.Forall("i", Obj.Hole("p"))
      )
    )
  )

  /** The six, as the text that goes into the definition and into the published statements. */
  val Axioms: Vector[(String, String)] =
    axiomTrees.map { case (name, tree) => name -> render(tree) }

  /** The scheme, likewise. */
  val InductionScheme: String = render(inductionScheme.tree)

  /**
   * `NUM_PA n` says `n` codes a non-logical axiom of Peano arithmetic.
   *
   * **A plain definition and not a recursion**, which is worth saying after five that were: an
   * axiom is one of six fixed codes or an instance of one scheme, so what defines it is a
   * disjunction. Nothing here descends into a code.
   *
   * The scheme is the only clause with content, and it is the first consumer of
   * [[FormulaSubstituteKeepsFormulas]]: an instance of induction is built by substituting into a
   * formula twice, and a scheme whose instances might not be formulas is not a scheme.
   */
  val AxiomName: String = "NUM_PA"

  /** `|- !n. NUM_PA n = (n = <the first> \/ ... \/ (?i p. NUM_FORM p /\ n = <an instance>))`. */
  val AxiomCases: String = "NUM_PA_CASES"

  /**
   * `|- !i p. NUM_FORM p ==> NUM_PA <the instance at i and p>`
   *
   * The induction scheme, which is what separates PA from Robinson's Q and is why `docs/adr/0013`
   * chose the first: D3 is an induction carried out **inside** the theory, and Q has none.
   */
  val AxiomInduction: String = "NUM_PA_INDUCTION"

  /**
   * `|- !n. NUM_PA n ==> NUM_FORM n`, that an axiom is a formula.
   *
   * The obligation the axiom set owes, and the one thing about it a reader cannot check by eye: the
   * six codes are nests six deep and the seventh is a scheme, so "these are formulas" is a claim
   * about the grammar rather than a glance. It is also what the refusals rest on, since
   * `~(NUM_FORM (NUM_CODE 1 0))` is already proved and the contrapositive of this settles that the
   * code of the object language's zero is not an axiom.
   *
   * It costs the naturals' two axioms where the memberships cost none, and the split is the whole
   * content of the pair. Being an axiom is decided by a disjunction. Being a **formula** is decided
   * by the recursion, and the introduction rules this walks were built on it.
   */
  val AxiomFormula: String = "NUM_PA_FORM"

  /* --------------------------------------------------------------- where a variable is free */

  /**
   * `NUM_FREE_TERM i s` says the index `i` occurs in the term `s`.
   *
   * The first recursion here that answers with a **proposition** rather than a code, and the reason
   * it exists is that two of the logical axioms cannot be stated without it: specialisation asks
   * that what is substituted be closed, and the quantifier's axiom asks that the index not occur in
   * the antecedent. Both are conditions on occurrence, and nothing in this development could say
   * one.
   *
   * It is also what the substitution's blindness to capture is measured against. `NUM_SUBST_TERM`
   * replaces every occurrence without asking whether the replacement gets captured, which is sound
   * for a closed replacement and for nothing else; before this, "closed" was a thing said in a
   * docstring rather than a thing stated.
   */
  val FreeName: String = "NUM_FREE_TERM"

  /** `NUM_FREE_FORM i p` says `i` occurs **free** in the formula `p`, the quantifier binding it. */
  val FormulaFreeName: String = "NUM_FREE_FORM"

  val FreeVariable: String = "NUM_FREE_TERM_VAR"
  val FreeZero: String = "NUM_FREE_TERM_ZERO"
  val FreeSuccessor: String = "NUM_FREE_TERM_SUC"
  val FreeSum: String = "NUM_FREE_TERM_ADD"
  val FreeProduct: String = "NUM_FREE_TERM_MUL"

  val FormulaFreeEquality: String = "NUM_FREE_FORM_EQ"
  val FormulaFreeNegation: String = "NUM_FREE_FORM_NOT"
  val FormulaFreeImplication: String = "NUM_FREE_FORM_IMP"

  /** The one clause that binds: where the quantifier's index is the one asked about, nothing is. */
  val FormulaFreeUniversal: String = "NUM_FREE_FORM_ALL"

  /**
   * `NUM_CLOSED t` says no index occurs in the term `t`, which is what the substitution needs.
   *
   * `NUM_SUBST_TERM` is blind to capture and is therefore sound where what it puts in has nothing
   * to capture. **Two** of the logical schemes carry it, `NUM_LOGIC_SPECIALISE` once and
   * `NUM_LOGIC_REPLACE` twice, and it is a constant rather than a written-out quantifier because
   * of those three occurrences and because a reader meeting it in the register should meet it
   * under a name. This sentence said three schemes until 2026-09-15, which is an occurrence count
   * read as a scheme count, and `AGENTS.md` carried the same mistake in the same words.
   *
   * **A third scheme substitutes and does not need the condition**, which is worth knowing before
   * a reader concludes one was forgotten: PA's induction scheme puts `0` and `S i` where `i`
   * stood. The first is closed, and the second can capture nothing, because the only index it
   * mentions is the one being replaced and the substitution stops at a quantifier binding that.
   *
   * **It is stronger than the usual condition and the difference is a real cost.** The textbook
   * scheme asks that `t` be *substitutable* for the index in the formula, which permits a `t` with
   * free variables as long as none is captured; that is a recursion over the formula this
   * development has not got. What is lost is instantiating a universal at a variable, so the object
   * system is weaker than first-order logic here. What is not lost is Goedel's argument, which
   * substitutes numerals, and a numeral is closed.
   */
  val ClosedName: String = "NUM_CLOSED"

  /** `|- !t. NUM_CLOSED t = (!k. ~(NUM_FREE_TERM k t))`. */
  val ClosedCases: String = "NUM_CLOSED_CASES"

  /**
   * The four introduction rules for closure, mirroring the five for [[TermName]].
   *
   * There is no rule for a variable and that is the point: a variable's own code is the one term
   * shape that is never closed, which `LanguageSpec` derives. The other four say that closure is
   * built the way a term is, so a caller holding closed pieces gets a closed whole without walking
   * the freeness clauses again.
   *
   * They arrived with the arithmetic rather than with [[ClosedName]] itself, because until
   * something had to close a COMPOUND term nothing needed them: the first consumer is the
   * induction step of `numeral m + numeral n = numeral (m + n)`, where the successor's congruence
   * asks closure of a sum of two numerals. Before that the only closed thing anybody wanted was a
   * numeral, and [[NumeralIsClosed]] answers that on its own.
   */
  val ClosedZero: String = "NUM_CLOSED_ZERO"

  /** `|- !s. NUM_CLOSED s ==> NUM_CLOSED (NUM_CODE 2 s)`. */
  val ClosedSuccessor: String = "NUM_CLOSED_SUC"

  /** `|- !a b. NUM_CLOSED a ==> NUM_CLOSED b ==> NUM_CLOSED (NUM_CODE 3 (NUM_PAIR a b))`. */
  val ClosedSum: String = "NUM_CLOSED_ADD"

  /** `|- !a b. NUM_CLOSED a ==> NUM_CLOSED b ==> NUM_CLOSED (NUM_CODE 4 (NUM_PAIR a b))`. */
  val ClosedProduct: String = "NUM_CLOSED_MUL"

  /* ------------------------------------------------------------------ the logical axioms */

  /**
   * The axioms of first-order logic with equality, over this language's four connectives.
   *
   * Every one is a scheme, where PA had six fixed codes and one scheme, and that is the difference
   * a reader should carry into the file: nothing here is a particular formula.
   *
   * **Three propositional, and they are the usual three.** Weakening and distribution give the
   * deduction theorem with modus ponens, and contraposition is what makes the system classical.
   * Conjunction, disjunction and the existential have no axioms because they have no tags: they are
   * abbreviations in the object language, which is `NUM_FORM`'s decision being spent.
   *
   * **Three about the quantifier.** Specialisation, its distribution over an implication, and the
   * one that lets a formula the index does not occur in be generalised. The first and the third
   * are the two that could not be stated before freeness, which is why freeness came first.
   *
   * **Two about equality**, and two is the economical choice rather than a short list of the
   * obvious ones. Reflexivity and one replacement scheme give symmetry, transitivity and the
   * congruence of every function symbol, so writing `x = y ==> S x = S y` and its five siblings as
   * axioms would be writing down consequences.
   */
  private val logicalSchemes: Vector[Scheme] = {
    val p = Obj.Hole("p")
    val q = Obj.Hole("q")
    val r = Obj.Hole("r")
    val t = Obj.TermHole("t")
    val u = Obj.TermHole("u")
    val formula = Condition.IsFormula("p")

    Vector(
      Scheme(
        "NUM_LOGIC_WEAKEN",
        List("p", "q"),
        List(formula, Condition.IsFormula("q")),
        Obj.Implies(p, Obj.Implies(q, p))
      ),
      Scheme(
        "NUM_LOGIC_DISTRIBUTE",
        List("p", "q", "r"),
        List(formula, Condition.IsFormula("q"), Condition.IsFormula("r")),
        Obj.Implies(
          Obj.Implies(p, Obj.Implies(q, r)),
          Obj.Implies(Obj.Implies(p, q), Obj.Implies(p, r))
        )
      ),
      Scheme(
        "NUM_LOGIC_CONTRAPOSE",
        List("p", "q"),
        List(formula, Condition.IsFormula("q")),
        Obj.Implies(Obj.Implies(Obj.Not(p), Obj.Not(q)), Obj.Implies(q, p))
      ),
      Scheme(
        "NUM_LOGIC_SPECIALISE",
        List("i", "t", "p"),
        List(formula, Condition.IsTerm("t"), Condition.Closed("t")),
        Obj.Implies(Obj.Forall("i", p), Obj.Substituted("i", t, p))
      ),
      Scheme(
        "NUM_LOGIC_UNIVERSAL",
        List("i", "p", "q"),
        List(formula, Condition.IsFormula("q")),
        Obj.Implies(
          Obj.Forall("i", Obj.Implies(p, q)),
          Obj.Implies(Obj.Forall("i", p), Obj.Forall("i", q))
        )
      ),
      Scheme(
        "NUM_LOGIC_VACUOUS",
        List("i", "p"),
        List(formula, Condition.NotFree("i", "p")),
        Obj.Implies(p, Obj.Forall("i", p))
      ),
      Scheme(
        "NUM_LOGIC_REFLEXIVE",
        List("t"),
        List(Condition.IsTerm("t")),
        Obj.Eq(t, t)
      ),
      Scheme(
        "NUM_LOGIC_REPLACE",
        List("i", "t", "u", "p"),
        List(
          formula,
          Condition.IsTerm("t"),
          Condition.IsTerm("u"),
          Condition.Closed("t"),
          Condition.Closed("u")
        ),
        Obj.Implies(
          Obj.Eq(t, u),
          Obj.Implies(Obj.Substituted("i", t, p), Obj.Substituted("i", u, p))
        )
      )
    )
  }

  /** `NUM_LOGIC n` says `n` codes a logical axiom: an instance of one of the eight schemes. */
  val LogicName: String = "NUM_LOGIC"

  /** `|- !n. NUM_LOGIC n = (<the first scheme> \/ ... \/ <the eighth>)`. */
  val LogicCases: String = "NUM_LOGIC_CASES"

  /** The names of the eight, in the order the disjunction holds them. */
  val LogicalAxioms: Vector[String] = logicalSchemes.map(_.name)

  /**
   * `|- !n. NUM_LOGIC n ==> NUM_FORM n`, the obligation the logical axioms owe.
   *
   * The same claim [[AxiomFormula]] makes about PA and a harder one to see by eye, because not one
   * of the eight is a particular formula: what has to be shown is that every instance of every
   * scheme is well formed, and what shows it is that each scheme's conditions are exactly the
   * theorems its holes need.
   */
  val LogicFormula: String = "NUM_LOGIC_FORM"

  /** The step of freeness on terms, with `i` free: it becomes the parameter. */
  val FreeStepText: String =
    "\\f:num -> bool. \\s:num. " +
      "COND (s = NUM_CODE 0 (NUM_PAYLOAD s)) " +
      "     (NUM_PAYLOAD s = i) " +
      "     (COND (s = NUM_CODE 2 (NUM_PAYLOAD s)) " +
      "           (f (NUM_PAYLOAD s)) " +
      "           (COND (s = NUM_CODE 3 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (f (NUM_FST (NUM_PAYLOAD s)) \\/ f (NUM_SND (NUM_PAYLOAD s))) " +
      "                 (COND (s = NUM_CODE 4 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (f (NUM_FST (NUM_PAYLOAD s)) \\/ f (NUM_SND (NUM_PAYLOAD s))) " +
      "                       F)))"

  /**
   * The step of freeness on formulas, with `i` free.
   *
   * Tag `1` and anything that is not a code fall through to `F`, which is right in both readings:
   * zero has no variable in it, and a number that codes nothing has no variable free in it either.
   */
  val FormulaFreeStepText: String =
    "\\f:num -> bool. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "     (NUM_FREE_TERM i (NUM_FST (NUM_PAYLOAD s)) \\/ " +
      "      NUM_FREE_TERM i (NUM_SND (NUM_PAYLOAD s))) " +
      "     (COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) " +
      "           (f (NUM_PAYLOAD s)) " +
      "           (COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (f (NUM_FST (NUM_PAYLOAD s)) \\/ f (NUM_SND (NUM_PAYLOAD s))) " +
      "                 (COND (s = NUM_CODE 8 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (COND (NUM_FST (NUM_PAYLOAD s) = i) " +
      "                             F " +
      "                             (f (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       F)))"

  /**
   * Which argument positions of a clause the recursion reads, which is all the admissibility proof
   * needs to know about a language.
   *
   * The proof that a step is admissible does not care what a clause **means**, only where the
   * function under construction occurs in it and what bounds that occurrence. Four shapes cover
   * both predicates here, and a fifth would be a fifth entry rather than a second proof.
   *
   * Written as a descriptor rather than as a second derivation because the alternative was
   * measured: the formula predicate's condition is the term predicate's with one case exchanged,
   * and copying two hundred lines to change one of them is how two proofs of one fact drift apart.
   */
  private enum Clause {

    /** The clause does not mention the function; it crosses unchanged. */
    case Opaque

    /** `tag = k /\ f p`: one answer, at the payload. */
    case AtPayload

    /** `tags /\ ?a b. p = NUM_PAIR a b /\ f a /\ f b`: two answers, at both components. */
    case AtBoth

    /** `tag = k /\ ?i q. p = NUM_PAIR i q /\ f q`: one answer, at the second component alone. */
    case AtSecond
  }

  /**
   * The step of the substitution, as text, with `i` and `t` free: they become its parameters.
   *
   * Four guards, each an equation saying what shape `s` has, and a fifth branch that leaves `s`
   * alone. Tag `1` falls through it, which is right, and so does anything that is not a code.
   */
  val SubstituteStepText: String =
    "\\f:num -> num. \\s:num. " +
      "COND (s = NUM_CODE 0 (NUM_PAYLOAD s)) " +
      "     (COND (NUM_PAYLOAD s = i) t s) " +
      "     (COND (s = NUM_CODE 2 (NUM_PAYLOAD s)) " +
      "           (NUM_CODE 2 (f (NUM_PAYLOAD s))) " +
      "           (COND (s = NUM_CODE 3 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (NUM_CODE 3 (NUM_PAIR (f (NUM_FST (NUM_PAYLOAD s))) " +
      "                                       (f (NUM_SND (NUM_PAYLOAD s))))) " +
      "                 (COND (s = NUM_CODE 4 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (NUM_CODE 4 (NUM_PAIR (f (NUM_FST (NUM_PAYLOAD s))) " +
      "                                             (f (NUM_SND (NUM_PAYLOAD s))))) " +
      "                       s)))"

  /** The step of the substitution on formulas, with `i` and `t` free as its two parameters. */
  val FormulaSubstituteStepText: String =
    "\\f:num -> num. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "     (NUM_CODE 5 (NUM_PAIR (NUM_SUBST_TERM i t (NUM_FST (NUM_PAYLOAD s))) " +
      "                           (NUM_SUBST_TERM i t (NUM_SND (NUM_PAYLOAD s))))) " +
      "     (COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) " +
      "           (NUM_CODE 6 (f (NUM_PAYLOAD s))) " +
      "           (COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (NUM_CODE 7 (NUM_PAIR (f (NUM_FST (NUM_PAYLOAD s))) " +
      "                                       (f (NUM_SND (NUM_PAYLOAD s))))) " +
      "                 (COND (s = NUM_CODE 8 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (COND (NUM_FST (NUM_PAYLOAD s) = i) " +
      "                             s " +
      "                             (NUM_CODE 8 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                   (f (NUM_SND (NUM_PAYLOAD s)))))) " +
      "                       s)))"

  /** The step for the formulas, whose first clause reads `NUM_TERM` and not itself. */
  val FormulaStepText: String =
    "\\f:num -> bool. \\n:num. ?t:num. ?p:num. n = NUM_CODE t p /\\ " +
      "((t = 5 /\\ (?a:num. ?b:num. p = NUM_PAIR a b /\\ NUM_TERM a /\\ NUM_TERM b)) " +
      "\\/ (t = 6 /\\ f p) " +
      "\\/ (t = 7 /\\ (?a:num. ?b:num. p = NUM_PAIR a b /\\ f a /\\ f b)) " +
      "\\/ (t = 8 /\\ (?i:num. ?q:num. p = NUM_PAIR i q /\\ f q)))"

  /** Where the formulas read themselves: the equality clause reads `NUM_TERM` and so is opaque. */
  private val FormulaClauses: Vector[Clause] =
    Vector(Clause.Opaque, Clause.AtPayload, Clause.AtBoth, Clause.AtSecond)

  /** Where the recursion reads itself in [[StepText]], clause by clause, in that order. */
  private val TermClauses: Vector[Clause] =
    Vector(Clause.Opaque, Clause.Opaque, Clause.AtPayload, Clause.AtBoth)

  /** The step of the recursion, as text, which is the term [[Descent]] is applied to. */
  val StepText: String =
    "\\f:num -> bool. \\n:num. ?t:num. ?p:num. n = NUM_CODE t p /\\ " +
      "(t = 0 " +
      "\\/ (t = 1 /\\ p = 0) " +
      "\\/ (t = 2 /\\ f p) " +
      "\\/ ((t = 3 \\/ t = 4) /\\ (?a:num. ?b:num. p = NUM_PAIR a b /\\ f a /\\ f b)))"

  /* ------------------------------------- the derived connectives and the bounded quantifier */

  /**
   * The six constants that expand what this language calls an abbreviation, and the obligation
   * [[FormulaCases]] left behind.
   *
   * Four tags and not six is a decision made where the formulas are defined, and its reason is
   * that a tag for the conjunction would mean proving every clause of `Prov` twice more for
   * nothing. What it leaves is an obligation rather than a saving, and until 2026-09-16 nobody had
   * paid it: two places in this file said the conjunction, the disjunction and the existential are
   * "abbreviations in the object language", and **no code anywhere built one**. An abbreviation
   * nothing expands is a sentence about an intention, and a reader who took it for an
   * implementation would have gone looking for a constructor that was not there.
   *
   * These six are that expansion. Each is a constant of THIS logic that builds a code, the way
   * [[NumeralName]] is: they add nothing to the object syntax, and the `NUM_FORM_` fact published
   * about each says so by deriving that what comes out is a formula the existing four tags already
   * accept. No new tag, no new [[Clause]] shape, and no second admissibility proof.
   *
   * **What they are for is the bounded quantifier**, which `docs/adr/0014` says the object theory
   * needs in order to take a code apart without an unbounded search, and which is what keeps `Prov`
   * Sigma-1. The order has to come first, the order needs an existential, and the existential is a
   * negated universal: the whole chain below is forced by there being no relation symbol in this
   * signature at all.
   */
  val AndName: String = "NUM_AND"

  /** `|- !p q. NUM_AND p q = NUM_CODE 6 (NUM_CODE 7 (NUM_PAIR p (NUM_CODE 6 q)))`. */
  val AndCases: String = "NUM_AND_CASES"

  /** `NUM_OR p q` is the code of `~p ==> q`, one negation rather than the conjunction's three. */
  val OrName: String = "NUM_OR"

  /** `|- !p q. NUM_OR p q = NUM_CODE 7 (NUM_PAIR (NUM_CODE 6 p) q)`. */
  val OrCases: String = "NUM_OR_CASES"

  /** `NUM_EXISTS i p` is the code of `~!i.~p`, the only existential this language has. */
  val ExistsName: String = "NUM_EXISTS"

  /** `|- !i p. NUM_EXISTS i p = NUM_CODE 6 (NUM_CODE 8 (NUM_PAIR i (NUM_CODE 6 p)))`. */
  val ExistsCases: String = "NUM_EXISTS_CASES"

  /**
   * `NUM_LESS z s t` is the code of `?z. s + S z = t`, and `z` is a parameter for a reason.
   *
   * **It is not [[Peano.StrictOrder]] and the two cannot be confused by accident**, which is worth
   * saying because they are a word apart and this repository has already paid once for a pair of
   * names that were a letter apart. `NUM_LT` is the order of `num`, a predicate, and it is what
   * the ambient logic reasons WITH. `NUM_LESS` is a function into `num` that builds a piece of
   * object syntax, and it is what the embedded theory reasons ABOUT. Their types differ, so a
   * caller that reaches for the wrong one gets a type error rather than a theorem about something
   * else; that is the defence, and it is mechanical rather than a matter of reading carefully.
   *
   * **The witness index is an argument and not a fixed number.** A fixed one would need `z` to be
   * fresh for `s` and for `t`, and nothing here can discharge that: `notFreeIn` walks a concrete
   * CLOSED code and refuses precisely the codes that have a free variable in them, which is the
   * case the condition would be about. Handing the index to the caller moves the obligation to
   * where the codes are actually known, and it is the same decision tag `8` already makes by
   * accepting a quantifier over an index that does not occur.
   */
  val LessName: String = "NUM_LESS"

  /** `|- !z s t. NUM_LESS z s t = NUM_EXISTS z (NUM_CODE 5 (NUM_PAIR (s + S z) t))`, coded. */
  val LessCases: String = "NUM_LESS_CASES"

  /** `NUM_ALL_BELOW z i t p` is the code of `!i. i < t ==> p`, the bounded universal. */
  val AllBelowName: String = "NUM_ALL_BELOW"

  /** `|- !z i t p. NUM_ALL_BELOW z i t p = ...`, the universal over an implication. */
  val AllBelowCases: String = "NUM_ALL_BELOW_CASES"

  /** `NUM_EXISTS_BELOW z i t p` is the code of `?i. i < t /\ p`, the bounded existential. */
  val ExistsBelowName: String = "NUM_EXISTS_BELOW"

  /** `|- !z i t p. NUM_EXISTS_BELOW z i t p = ...`, the existential over a conjunction. */
  val ExistsBelowCases: String = "NUM_EXISTS_BELOW_CASES"

  /**
   * Each of the six builds a formula out of formulas, which is the half that says they are
   * abbreviations of this syntax rather than additions to it.
   *
   * They extend the run of introduction rules at [[FormulaEquality]] and are named to sit in it.
   * [[LessFormula]] is the one that asks for TERMS rather than formulas, because a comparison is
   * where the two levels meet, exactly as the equality clause is.
   */
  val AndFormula: String = "NUM_FORM_AND"
  val OrFormula: String = "NUM_FORM_OR"
  val ExistsFormula: String = "NUM_FORM_EXISTS"
  val LessFormula: String = "NUM_FORM_LESS"
  val AllBelowFormula: String = "NUM_FORM_ALL_BELOW"
  val ExistsBelowFormula: String = "NUM_FORM_EXISTS_BELOW"

  /**
   * Where an index occurs free in each of the six, extending the run at [[FormulaFreeEquality]].
   *
   * **Four of the six bind an index and two do not**, which is the split [[FormulaFreeUniversal]]
   * makes against its three neighbours and is not the three and three this comment claimed while
   * the six were names without statements. [[AndFree]] and [[OrFree]] answer with a disjunction;
   * the other four answer with a `COND`, and the two bounded ones with a `COND` inside a `COND`,
   * because they bind the quantified index and the witness separately.
   *
   * In [[LessFree]] the bound index is the witness, so the `COND` is about `z`; the occurrence of
   * `z` that the expansion itself introduces falls away under it, which is why the answer names
   * only `s` and `t`. In [[AllBelowFree]] and [[ExistsBelowFree]] the inner `COND` is what says
   * the bound `t` is read under that same witness: an index equal to `z` is bound there too, and
   * dropping the inner conditional is the perturbation `LanguageSpec` puts to the derivation.
   */
  val AndFree: String = "NUM_FREE_FORM_AND"
  val OrFree: String = "NUM_FREE_FORM_OR"
  val ExistsFree: String = "NUM_FREE_FORM_EXISTS"
  val LessFree: String = "NUM_FREE_FORM_LESS"
  val AllBelowFree: String = "NUM_FREE_FORM_ALL_BELOW"
  val ExistsBelowFree: String = "NUM_FREE_FORM_EXISTS_BELOW"

  /**
   * What a substitution does to each of the six, extending the run at
   * [[FormulaSubstituteEquality]].
   *
   * **These inherit [[FormulaSubstituteName]]'s blindness to capture and the condition is on the
   * caller, not on the equation.** Each clause below is true as an equation whatever is
   * substituted. What is not safe is substituting a term in which the bound index occurs free:
   * under [[LessName]] that index is the witness `z`, and a replacement mentioning `z` would come
   * out captured. The substitution this development publishes has always been sound only for a
   * closed replacement, [[NumeralIsClosed]] is what discharges that where Goedel's argument needs
   * it, and these six move the reader's attention to a second index rather than changing the rule.
   *
   * Where [[AllBelowSubstitute]] and [[ExistsBelowSubstitute]] carry a `COND` **inside** the
   * bound rather than around the whole answer, that is the same second index seen from the other
   * side: the bound is under the witness's own quantifier, so a substitution for the witness
   * leaves it alone and a substitution for anything else goes in. Hoisting that conditional out
   * would give a statement of four cases where the answer has two, and the two that differ differ
   * in one argument.
   */
  val AndSubstitute: String = "NUM_SUBST_FORM_AND"
  val OrSubstitute: String = "NUM_SUBST_FORM_OR"
  val ExistsSubstitute: String = "NUM_SUBST_FORM_EXISTS"
  val LessSubstitute: String = "NUM_SUBST_FORM_LESS"
  val AllBelowSubstitute: String = "NUM_SUBST_FORM_ALL_BELOW"
  val ExistsBelowSubstitute: String = "NUM_SUBST_FORM_EXISTS_BELOW"

  /** Every statement this development publishes, as text, for the reason `Peano` gives. */
  val Statements: Vector[(String, String)] = Vector(
    TermCases ->
      ("!n:num. NUM_TERM n = (?t:num. ?p:num. n = NUM_CODE t p /\\ " +
        "(t = 0 \\/ t = 1 /\\ p = 0 \\/ t = 2 /\\ NUM_TERM p \\/ " +
        "(t = 3 \\/ t = 4) /\\ " +
        "(?a:num. ?b:num. p = NUM_PAIR a b /\\ NUM_TERM a /\\ NUM_TERM b)))"),
    TermVariable -> "!i:num. NUM_TERM (NUM_CODE 0 i)",
    TermZero -> "NUM_TERM (NUM_CODE 1 0)",
    TermSuccessor -> "!t:num. NUM_TERM t ==> NUM_TERM (NUM_CODE 2 t)",
    TermSum ->
      ("!a:num b:num. NUM_TERM a ==> NUM_TERM b ==> " +
        "NUM_TERM (NUM_CODE 3 (NUM_PAIR a b))"),
    TermProduct ->
      ("!a:num b:num. NUM_TERM a ==> NUM_TERM b ==> " +
        "NUM_TERM (NUM_CODE 4 (NUM_PAIR a b))"),
    TermNotZero -> "~(NUM_TERM ZERO)",
    FormulaCases ->
      ("!n:num. NUM_FORM n = (?t:num. ?p:num. n = NUM_CODE t p /\\ " +
        "(t = 5 /\\ (?a:num. ?b:num. p = NUM_PAIR a b /\\ NUM_TERM a /\\ NUM_TERM b) \\/ " +
        "t = 6 /\\ NUM_FORM p \\/ " +
        "t = 7 /\\ (?a:num. ?b:num. p = NUM_PAIR a b /\\ NUM_FORM a /\\ NUM_FORM b) \\/ " +
        "t = 8 /\\ (?i:num. ?q:num. p = NUM_PAIR i q /\\ NUM_FORM q)))"),
    FormulaEquality ->
      ("!a:num b:num. NUM_TERM a ==> NUM_TERM b ==> " +
        "NUM_FORM (NUM_CODE 5 (NUM_PAIR a b))"),
    FormulaNegation -> "!p:num. NUM_FORM p ==> NUM_FORM (NUM_CODE 6 p)",
    FormulaImplication ->
      ("!p:num q:num. NUM_FORM p ==> NUM_FORM q ==> " +
        "NUM_FORM (NUM_CODE 7 (NUM_PAIR p q))"),
    FormulaUniversal ->
      "!i:num p:num. NUM_FORM p ==> NUM_FORM (NUM_CODE 8 (NUM_PAIR i p))",
    FormulaNotZero -> "~(NUM_FORM ZERO)",
    NumeralAtZero -> "NUM_NUMERAL ZERO = NUM_CODE 1 0",
    NumeralAtSuccessor -> "!n:num. NUM_NUMERAL (SUC n) = NUM_CODE 2 (NUM_NUMERAL n)",
    NumeralIsTerm -> "!n:num. NUM_TERM (NUM_NUMERAL n)",
    NumeralIsClosed -> "!n:num. NUM_CLOSED (NUM_NUMERAL n)",
    NumeralInjective ->
      "!m:num n:num. NUM_NUMERAL m = NUM_NUMERAL n ==> m = n",
    SubstituteVariable ->
      "!i:num t:num j:num. NUM_SUBST_TERM i t (NUM_CODE 0 j) = COND (j = i) t (NUM_CODE 0 j)",
    SubstituteZero -> "!i:num t:num. NUM_SUBST_TERM i t (NUM_CODE 1 0) = NUM_CODE 1 0",
    SubstituteSuccessor ->
      ("!i:num t:num s:num. NUM_SUBST_TERM i t (NUM_CODE 2 s) = " +
        "NUM_CODE 2 (NUM_SUBST_TERM i t s)"),
    SubstituteSum ->
      ("!i:num t:num a:num b:num. NUM_SUBST_TERM i t (NUM_CODE 3 (NUM_PAIR a b)) = " +
        "NUM_CODE 3 (NUM_PAIR (NUM_SUBST_TERM i t a) (NUM_SUBST_TERM i t b))"),
    SubstituteProduct ->
      ("!i:num t:num a:num b:num. NUM_SUBST_TERM i t (NUM_CODE 4 (NUM_PAIR a b)) = " +
        "NUM_CODE 4 (NUM_PAIR (NUM_SUBST_TERM i t a) (NUM_SUBST_TERM i t b))"),
    FormulaSubstituteEquality ->
      ("!i:num t:num a:num b:num. NUM_SUBST_FORM i t (NUM_CODE 5 (NUM_PAIR a b)) = " +
        "NUM_CODE 5 (NUM_PAIR (NUM_SUBST_TERM i t a) (NUM_SUBST_TERM i t b))"),
    FormulaSubstituteNegation ->
      ("!i:num t:num p:num. NUM_SUBST_FORM i t (NUM_CODE 6 p) = " +
        "NUM_CODE 6 (NUM_SUBST_FORM i t p)"),
    FormulaSubstituteImplication ->
      ("!i:num t:num p:num q:num. NUM_SUBST_FORM i t (NUM_CODE 7 (NUM_PAIR p q)) = " +
        "NUM_CODE 7 (NUM_PAIR (NUM_SUBST_FORM i t p) (NUM_SUBST_FORM i t q))"),
    FormulaSubstituteUniversal ->
      ("!i:num t:num j:num p:num. NUM_SUBST_FORM i t (NUM_CODE 8 (NUM_PAIR j p)) = " +
        "COND (j = i) (NUM_CODE 8 (NUM_PAIR j p)) " +
        "(NUM_CODE 8 (NUM_PAIR j (NUM_SUBST_FORM i t p)))"),
    SubstituteKeepsTerms ->
      ("!i:num t:num s:num. NUM_TERM s ==> NUM_TERM t ==> " +
        "NUM_TERM (NUM_SUBST_TERM i t s)"),
    SubstituteIdle ->
      ("!i:num t:num s:num. NUM_TERM s ==> ~(NUM_FREE_TERM i s) ==> " +
        "NUM_SUBST_TERM i t s = s"),
    FormulaSubstituteKeepsFormulas ->
      ("!i:num t:num p:num. NUM_FORM p ==> NUM_TERM t ==> " +
        "NUM_FORM (NUM_SUBST_FORM i t p)"),
    AxiomInduction -> inductionScheme.statement(AxiomName),
    AxiomCases -> {
      val disjuncts =
        Axioms.map { case (_, code) => s"n:num = ($code)" } :+
          s"(${inductionScheme.disjunct("n:num")})"
      s"!n:num. NUM_PA n = (${disjuncts.mkString(" \\/ ")})"
    },
    AxiomFormula -> "!n:num. NUM_PA n ==> NUM_FORM n",
    FreeVariable -> "!i:num j:num. NUM_FREE_TERM i (NUM_CODE 0 j) = (j = i)",
    FreeZero -> "!i:num. NUM_FREE_TERM i (NUM_CODE 1 0) = F",
    FreeSuccessor -> "!i:num s:num. NUM_FREE_TERM i (NUM_CODE 2 s) = NUM_FREE_TERM i s",
    FreeSum ->
      ("!i:num a:num b:num. NUM_FREE_TERM i (NUM_CODE 3 (NUM_PAIR a b)) = " +
        "(NUM_FREE_TERM i a \\/ NUM_FREE_TERM i b)"),
    FreeProduct ->
      ("!i:num a:num b:num. NUM_FREE_TERM i (NUM_CODE 4 (NUM_PAIR a b)) = " +
        "(NUM_FREE_TERM i a \\/ NUM_FREE_TERM i b)"),
    FormulaFreeEquality ->
      ("!i:num a:num b:num. NUM_FREE_FORM i (NUM_CODE 5 (NUM_PAIR a b)) = " +
        "(NUM_FREE_TERM i a \\/ NUM_FREE_TERM i b)"),
    FormulaFreeNegation ->
      "!i:num p:num. NUM_FREE_FORM i (NUM_CODE 6 p) = NUM_FREE_FORM i p",
    FormulaFreeImplication ->
      ("!i:num p:num q:num. NUM_FREE_FORM i (NUM_CODE 7 (NUM_PAIR p q)) = " +
        "(NUM_FREE_FORM i p \\/ NUM_FREE_FORM i q)"),
    FormulaFreeUniversal ->
      ("!i:num j:num p:num. NUM_FREE_FORM i (NUM_CODE 8 (NUM_PAIR j p)) = " +
        "COND (j = i) F (NUM_FREE_FORM i p)"),
    ClosedCases -> "!t:num. NUM_CLOSED t = (!k:num. ~(NUM_FREE_TERM k t))",
    ClosedZero -> "NUM_CLOSED (NUM_CODE 1 0)",
    ClosedSuccessor -> "!s:num. NUM_CLOSED s ==> NUM_CLOSED (NUM_CODE 2 s)",
    ClosedSum ->
      ("!a:num b:num. NUM_CLOSED a ==> NUM_CLOSED b ==> " +
        "NUM_CLOSED (NUM_CODE 3 (NUM_PAIR a b))"),
    ClosedProduct ->
      ("!a:num b:num. NUM_CLOSED a ==> NUM_CLOSED b ==> " +
        "NUM_CLOSED (NUM_CODE 4 (NUM_PAIR a b))"),
    LogicCases -> {
      val disjuncts = logicalSchemes.map(scheme => s"(${scheme.disjunct("n:num")})")
      s"!n:num. NUM_LOGIC n = (${disjuncts.mkString(" \\/ ")})"
    },
    LogicFormula -> "!n:num. NUM_LOGIC n ==> NUM_FORM n",
    AndCases ->
      ("!p:num q:num. NUM_AND p q = " +
        "NUM_CODE 6 (NUM_CODE 7 (NUM_PAIR p (NUM_CODE 6 q)))"),
    OrCases ->
      "!p:num q:num. NUM_OR p q = NUM_CODE 7 (NUM_PAIR (NUM_CODE 6 p) q)",
    ExistsCases ->
      ("!i:num p:num. NUM_EXISTS i p = " +
        "NUM_CODE 6 (NUM_CODE 8 (NUM_PAIR i (NUM_CODE 6 p)))"),
    LessCases ->
      ("!z:num s:num t:num. NUM_LESS z s t = " +
        "NUM_EXISTS z (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR s (NUM_CODE 2 (NUM_CODE 0 z)))) t))"),
    AllBelowCases ->
      ("!z:num i:num t:num p:num. NUM_ALL_BELOW z i t p = " +
        "NUM_CODE 8 (NUM_PAIR i (NUM_CODE 7 (NUM_PAIR (NUM_LESS z (NUM_CODE 0 i) t) p)))"),
    ExistsBelowCases ->
      ("!z:num i:num t:num p:num. NUM_EXISTS_BELOW z i t p = " +
        "NUM_EXISTS i (NUM_AND (NUM_LESS z (NUM_CODE 0 i) t) p)"),
    AndFormula ->
      "!p:num q:num. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM (NUM_AND p q)",
    OrFormula ->
      "!p:num q:num. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM (NUM_OR p q)",
    ExistsFormula -> "!i:num p:num. NUM_FORM p ==> NUM_FORM (NUM_EXISTS i p)",
    LessFormula ->
      ("!z:num s:num t:num. NUM_TERM s ==> NUM_TERM t ==> " +
        "NUM_FORM (NUM_LESS z s t)"),
    AllBelowFormula ->
      ("!z:num i:num t:num p:num. NUM_TERM t ==> NUM_FORM p ==> " +
        "NUM_FORM (NUM_ALL_BELOW z i t p)"),
    ExistsBelowFormula ->
      ("!z:num i:num t:num p:num. NUM_TERM t ==> NUM_FORM p ==> " +
        "NUM_FORM (NUM_EXISTS_BELOW z i t p)"),
    AndFree ->
      ("!i:num p:num q:num. NUM_FREE_FORM i (NUM_AND p q) = " +
        "(NUM_FREE_FORM i p \\/ NUM_FREE_FORM i q)"),
    OrFree ->
      ("!i:num p:num q:num. NUM_FREE_FORM i (NUM_OR p q) = " +
        "(NUM_FREE_FORM i p \\/ NUM_FREE_FORM i q)"),
    ExistsFree ->
      ("!i:num j:num p:num. NUM_FREE_FORM i (NUM_EXISTS j p) = " +
        "COND (j = i) F (NUM_FREE_FORM i p)"),
    LessFree ->
      ("!i:num z:num s:num t:num. NUM_FREE_FORM i (NUM_LESS z s t) = " +
        "COND (z = i) F (NUM_FREE_TERM i s \\/ NUM_FREE_TERM i t)"),
    AllBelowFree ->
      ("!i:num z:num j:num t:num p:num. NUM_FREE_FORM i (NUM_ALL_BELOW z j t p) = " +
        "COND (j = i) F (COND (z = i) F (NUM_FREE_TERM i t) \\/ NUM_FREE_FORM i p)"),
    ExistsBelowFree ->
      ("!i:num z:num j:num t:num p:num. NUM_FREE_FORM i (NUM_EXISTS_BELOW z j t p) = " +
        "COND (j = i) F (COND (z = i) F (NUM_FREE_TERM i t) \\/ NUM_FREE_FORM i p)"),
    AndSubstitute ->
      ("!i:num t:num p:num q:num. NUM_SUBST_FORM i t (NUM_AND p q) = " +
        "NUM_AND (NUM_SUBST_FORM i t p) (NUM_SUBST_FORM i t q)"),
    OrSubstitute ->
      ("!i:num t:num p:num q:num. NUM_SUBST_FORM i t (NUM_OR p q) = " +
        "NUM_OR (NUM_SUBST_FORM i t p) (NUM_SUBST_FORM i t q)"),
    ExistsSubstitute ->
      ("!i:num t:num j:num p:num. NUM_SUBST_FORM i t (NUM_EXISTS j p) = " +
        "COND (j = i) (NUM_EXISTS j p) (NUM_EXISTS j (NUM_SUBST_FORM i t p))"),
    LessSubstitute ->
      ("!i:num t:num z:num s:num u:num. NUM_SUBST_FORM i t (NUM_LESS z s u) = " +
        "COND (z = i) (NUM_LESS z s u) " +
        "(NUM_LESS z (NUM_SUBST_TERM i t s) (NUM_SUBST_TERM i t u))"),
    AllBelowSubstitute ->
      ("!i:num t:num z:num j:num u:num p:num. " +
        "NUM_SUBST_FORM i t (NUM_ALL_BELOW z j u p) = " +
        "COND (j = i) (NUM_ALL_BELOW z j u p) " +
        "(NUM_ALL_BELOW z j (COND (z = i) u (NUM_SUBST_TERM i t u)) " +
        "(NUM_SUBST_FORM i t p))"),
    ExistsBelowSubstitute ->
      ("!i:num t:num z:num j:num u:num p:num. " +
        "NUM_SUBST_FORM i t (NUM_EXISTS_BELOW z j u p) = " +
        "COND (j = i) (NUM_EXISTS_BELOW z j u p) " +
        "(NUM_EXISTS_BELOW z j (COND (z = i) u (NUM_SUBST_TERM i t u)) " +
        "(NUM_SUBST_FORM i t p))")
  ) ++ Axioms.map { case (name, code) => name -> s"NUM_PA ($code)" } ++
    logicalSchemes.map(scheme => scheme.name -> scheme.statement(LogicName))

  /** Build it over the numbering, in that development's own notation. */
  def construct(
    numbering: Numbering,
    induct: Induct,
    successor: Successor
  ): Either[LogicError, Language] =
    construct(numbering, induct, successor, numbering.theory, numbering.notation)

  /** The same, extending a theory that already holds something else. */
  def construct(
    numbering: Numbering,
    induct: Induct,
    successor: Successor,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Language] = {
    val peano = numbering.peano
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      descent <- Descent.construct(peano, induct)
      recursion <- descent.theorem

      withTerms <- definePredicate(
        numbering, recursion, base, notation, numbering.logic, TermName, StepText, TermClauses)
      (termTheory, termDefinition, termNamed) = withTerms
      termLogic <- numbering.logic.over(termTheory)

      // The formulas are defined over a theory that already has `NUM_TERM`, because their first
      // clause asks for it: an equality of the object language relates two TERMS, and that is a
      // side condition rather than a recursion, which is why it costs the admissibility proof
      // nothing.
      withFormulas <- definePredicate(
        numbering, recursion, termTheory, notation, termLogic,
        FormulaName, FormulaStepText, FormulaClauses)
      (formulaTheory, formulaDefinition, formulaNamed) = withFormulas
      formulaLogic <- numbering.logic.over(formulaTheory)

      // The numerals, which are a primitive recursion rather than a course-of-values one: the
      // numeral for `SUC n` is built from the numeral for `n` and nothing smaller.
      recursionOnNumbers <- numbering.peano.naturals.recursion
      definedNumeral <- Recursion.define(
        formulaLogic,
        numbering.peano.naturals,
        formulaTheory,
        notation,
        recursionOnNumbers,
        NumeralName,
        TyApp(Natural.TypeName, Nil),
        "NUM_CODE 1 0",
        "\\v:num. \\i:num. NUM_CODE 2 v",
        None
      )
      (numeralTheory, numeralDefinition, numeralZero, numeralSuccessor) = definedNumeral
      numeralLogic <- numbering.logic.over(numeralTheory)

      withSubstitution <- defineShaped(
        numbering, recursion, numeralTheory, notation, numeralLogic,
        SubstituteName, SubstituteStepText, numbers,
        List(Term.variable("i", numbers), Term.variable("t", numbers)))
      (termSubstituteTheory, substituteDefinition, substituteNamed) = withSubstitution
      termSubstituteLogic <- numbering.logic.over(termSubstituteTheory)

      withFormulaSubstitution <- defineShaped(
        numbering, recursion, termSubstituteTheory, notation, termSubstituteLogic,
        FormulaSubstituteName, FormulaSubstituteStepText, numbers,
        List(Term.variable("i", numbers), Term.variable("t", numbers)))
      (theory, formulaSubstituteDefinition, formulaSubstituteNamed) = withFormulaSubstitution
      logic <- numbering.logic.over(theory)
      induction <- numbering.peano.naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      definition = termDefinition
      vocabulary <- Vocabulary.of(numbering, theory, notation, logic)
      cases <- vocabulary.checked(TermCases, termNamed)
      formulaCases <- vocabulary.checked(FormulaCases, formulaNamed)
      variable <- introduceTerm(vocabulary, cases, TermVariable)
      zero <- introduceTerm(vocabulary, cases, TermZero)
      successorRule <- introduceTerm(vocabulary, cases, TermSuccessor)
      sum <- introduceTerm(vocabulary, cases, TermSum)
      product <- introduceTerm(vocabulary, cases, TermProduct)
      notZero <- zeroCodesNothing(vocabulary, cases, TermName, TermNotZero)

      equality <- introduceFormula(vocabulary, formulaCases, FormulaEquality)
      negation <- introduceFormula(vocabulary, formulaCases, FormulaNegation)
      implication <- introduceFormula(vocabulary, formulaCases, FormulaImplication)
      universal <- introduceFormula(vocabulary, formulaCases, FormulaUniversal)
      formulaNotZero <- zeroCodesNothing(vocabulary, formulaCases, FormulaName, FormulaNotZero)

      substituteCases = substituteNamed
      numeralAtZero <- vocabulary.checked(NumeralAtZero, numeralZero)
      numeralAtSuccessor <- vocabulary.checked(NumeralAtSuccessor, numeralSuccessor)
      numeralIsTerm <- everyNumeralIsATerm(
        vocabulary, driver, numeralAtZero, numeralAtSuccessor, zero, successorRule)
      numeralInjective <- numeralsAreDistinct(
        vocabulary, successor, numeralAtZero, numeralAtSuccessor)

      projections <- Vector(
        Numbering.PayloadOfCode, Numbering.FirstOfPair, Numbering.SecondOfPair
      ).foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) { (carried, name) =>
        for {
          found <- carried
          fact <- numbering.fact(name)
          rule <- Rewrite.Rule.of(logic, fact)
        } yield found :+ rule
      }
      replaced = List(Term.variable("i", numbers), Term.variable("t", numbers))
      substituteVariable <- shapedAt(
        vocabulary, substituteCases, projections, successor, SubstituteVariable, numbers, replaced)
      substituteZero <- shapedAt(
        vocabulary, substituteCases, projections, successor, SubstituteZero, numbers, replaced)
      substituteSuccessor <- shapedAt(
        vocabulary, substituteCases, projections, successor, SubstituteSuccessor, numbers, replaced)
      substituteSum <- shapedAt(
        vocabulary, substituteCases, projections, successor, SubstituteSum, numbers, replaced)
      substituteProduct <- shapedAt(
        vocabulary, substituteCases, projections, successor, SubstituteProduct, numbers, replaced)

      formulaSubstituteEquality <- shapedAt(
        vocabulary, formulaSubstituteNamed, projections, successor,
        FormulaSubstituteEquality, numbers, replaced)
      formulaSubstituteNegation <- shapedAt(
        vocabulary, formulaSubstituteNamed, projections, successor,
        FormulaSubstituteNegation, numbers, replaced)
      formulaSubstituteImplication <- shapedAt(
        vocabulary, formulaSubstituteNamed, projections, successor,
        FormulaSubstituteImplication, numbers, replaced)
      formulaSubstituteUniversal <- shapedAt(
        vocabulary, formulaSubstituteNamed, projections, successor,
        FormulaSubstituteUniversal, numbers, replaced)

      strong <- numbering.peano.fact(Peano.StrongInduction)
      substituteKeepsTerms <- keepsWellFormed(
        vocabulary,
        SubstituteKeepsTerms,
        Some(vocabulary.predicate),
        vocabulary.substitute,
        strong,
        cases,
        termClause(
          Map(
            TermSuccessor -> successorRule,
            TermSum -> sum,
            TermProduct -> product
          ),
          Map(
            SubstituteVariable -> substituteVariable,
            SubstituteZero -> substituteZero,
            SubstituteSuccessor -> substituteSuccessor,
            SubstituteSum -> substituteSum,
            SubstituteProduct -> substituteProduct
          )
        )
      )
      formulaSubstitute <- LogicError.lift(
        theory.constant(
          FormulaSubstituteName,
          Type.fun(
            TyApp(Natural.TypeName, Nil),
            Type.fun(TyApp(Natural.TypeName, Nil), Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Natural.TypeName, Nil)))
          )
        )
      )
      _ = ()
      formulaSubstituteKeepsFormulas <- keepsWellFormed(
        vocabulary,
        FormulaSubstituteKeepsFormulas,
        Some(vocabulary.formula),
        formulaSubstitute,
        strong,
        formulaCases,
        formulaClause(
          Map(
            FormulaEquality -> equality,
            FormulaNegation -> negation,
            FormulaImplication -> implication,
            FormulaUniversal -> universal
          ),
          Map(
            FormulaSubstituteEquality -> formulaSubstituteEquality,
            FormulaSubstituteNegation -> formulaSubstituteNegation,
            FormulaSubstituteImplication -> formulaSubstituteImplication,
            FormulaSubstituteUniversal -> formulaSubstituteUniversal
          ),
          substituteKeepsTerms
        )
      )
      // Freeness is defined here rather than beside the substitutions because its formula half
      // names `NUM_FREE_TERM`, exactly as the formula substitution names the term one: a step that
      // reads a constant needs that constant already declared, which fixes the order of the four.
      free = List(Term.variable("i", numbers))
      withFree <- defineShaped(
        numbering, recursion, theory, notation, logic, FreeName, FreeStepText, Type.Bool, free)
      (freeTheory, freeDefinition, freeNamed) = withFree
      freeLogic <- numbering.logic.over(freeTheory)

      withFormulaFree <- defineShaped(
        numbering, recursion, freeTheory, notation, freeLogic,
        FormulaFreeName, FormulaFreeStepText, Type.Bool, free)
      (freedom, formulaFreeDefinition, formulaFreeNamed) = withFormulaFree
      freedomLogic <- numbering.logic.over(freedom)
      freeVocabulary <- Vocabulary.of(numbering, freedom, notation, freedomLogic)

      freeVariable <- shapedAt(
        freeVocabulary, freeNamed, projections, successor, FreeVariable, Type.Bool, free)
      freeZero <- shapedAt(
        freeVocabulary, freeNamed, projections, successor, FreeZero, Type.Bool, free)
      freeSuccessor <- shapedAt(
        freeVocabulary, freeNamed, projections, successor, FreeSuccessor, Type.Bool, free)
      freeSum <- shapedAt(
        freeVocabulary, freeNamed, projections, successor, FreeSum, Type.Bool, free)
      freeProduct <- shapedAt(
        freeVocabulary, freeNamed, projections, successor, FreeProduct, Type.Bool, free)

      substituteIsIdle <- keepsWellFormed(
        freeVocabulary,
        SubstituteIdle,
        None,
        freeVocabulary.substitute,
        strong,
        cases,
        idleClause(
          Map(
            FreeVariable -> freeVariable,
            FreeSuccessor -> freeSuccessor,
            FreeSum -> freeSum,
            FreeProduct -> freeProduct
          ),
          Map(
            SubstituteVariable -> substituteVariable,
            SubstituteZero -> substituteZero,
            SubstituteSuccessor -> substituteSuccessor,
            SubstituteSum -> substituteSum,
            SubstituteProduct -> substituteProduct
          )
        )
      )

      formulaFreeEquality <- shapedAt(
        freeVocabulary, formulaFreeNamed, projections, successor,
        FormulaFreeEquality, Type.Bool, free)
      formulaFreeNegation <- shapedAt(
        freeVocabulary, formulaFreeNamed, projections, successor,
        FormulaFreeNegation, Type.Bool, free)
      formulaFreeImplication <- shapedAt(
        freeVocabulary, formulaFreeNamed, projections, successor,
        FormulaFreeImplication, Type.Bool, free)
      formulaFreeUniversal <- shapedAt(
        freeVocabulary, formulaFreeNamed, projections, successor,
        FormulaFreeUniversal, Type.Bool, free)

      withClosed <- defineClosed(freedom, notation, freedomLogic)
      (closedTheory, closedDefinition, closedCasesRaw) = withClosed
      closedLogic <- numbering.logic.over(closedTheory)

      withAxioms <- defineAxioms(closedTheory, notation, closedLogic)
      (axiomTheory, axiomDefinition, axiomCasesRaw) = withAxioms
      axiomLogic <- numbering.logic.over(axiomTheory)
      _ = ()
      axiomVocabulary <- Vocabulary.of(numbering, axiomTheory, notation, axiomLogic)
      axiomCases <- axiomVocabulary.checked(AxiomCases, axiomCasesRaw)
      axiomFacts <- (0 to Axioms.size)
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) { (carried, at) =>
          for {
            found <- carried
            proved <- axiomAt(axiomVocabulary, axiomCases, at)
            name = if (at < Axioms.size) Axioms(at)._1 else AxiomInduction
          } yield found.updated(name, proved)
        }

      // The prover walks the trees composing the introduction rules, and those were proved over
      // theories below this one. A theorem carries its hypotheses and its conclusion and not the
      // theory it was proved in, so they compose here unchanged; what the vocabulary is missing is
      // only a way to look them up by name.
      introductions = Map(
        TermVariable -> variable,
        TermZero -> zero,
        TermSuccessor -> successorRule,
        TermSum -> sum,
        TermProduct -> product,
        FormulaEquality -> equality,
        FormulaNegation -> negation,
        FormulaImplication -> implication,
        FormulaUniversal -> universal,
        FormulaSubstituteKeepsFormulas -> formulaSubstituteKeepsFormulas
      )
      axiomFormula <- everyMemberIsAFormula(
        axiomVocabulary.copy(facts = axiomVocabulary.facts ++ introductions),
        axiomCases,
        axiomTrees.map(_._2),
        Vector(inductionScheme),
        AxiomFormula
      )

      withLogic <- defineLogic(axiomTheory, notation, axiomLogic)
      (logicTheory, logicDefinition, logicCasesRaw) = withLogic
      logicLogic <- numbering.logic.over(logicTheory)
      logicVocabulary <- Vocabulary.of(numbering, logicTheory, notation, logicLogic)
      logicCases <- logicVocabulary.checked(LogicCases, logicCasesRaw)
      closedCases <- logicVocabulary.checked(ClosedCases, closedCasesRaw)
      logicHead <- LogicError.lift(
        logicTheory.constant(LogicName, Type.fun(numbers, Type.Bool))
      )
      logicFacts <- logicalSchemes.zipWithIndex
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
          case (carried, (scheme, at)) =>
            for {
              found <- carried
              proved <- schemeMembership(
                logicVocabulary, logicCases, logicalSchemes.size, at, scheme, logicHead)
            } yield found.updated(scheme.name, proved)
        }
      // After the closure predicate and not beside the numerals, which is where the other numeral
      // facts are: `NUM_CLOSED` is defined here, so the statement cannot be parsed any earlier.
      closures <- closureRules(
        logicVocabulary,
        closedCases,
        Map(
          FreeZero -> freeZero,
          FreeSuccessor -> freeSuccessor,
          FreeSum -> freeSum,
          FreeProduct -> freeProduct
        )
      )
      numeralIsClosed <- everyNumeralIsClosed(
        logicVocabulary,
        driver,
        numeralAtZero,
        numeralAtSuccessor,
        freeZero,
        freeSuccessor,
        closedCases
      )
      logicFormula <- everyMemberIsAFormula(
        logicVocabulary.copy(facts = logicVocabulary.facts ++ introductions),
        logicCases,
        Vector.empty,
        logicalSchemes,
        LogicFormula
      )

      // Last, because each of the six is written with the ones before it and a constant cannot
      // appear in a body until it is in the theory. Nothing above depends on them, so this is the
      // one place in `construct` where the order is the definitions' own rather than the proofs'.
      withConnectives <- defineConnectives(logicTheory, notation, logicLogic)
      (connectiveTheory, connectiveDefinitions, connectiveEquations) = withConnectives
      connectiveLogic <- numbering.logic.over(connectiveTheory)
      connectiveVocabulary <- Vocabulary.of(
        numbering, connectiveTheory, notation, connectiveLogic)
      connectiveCases <- connectiveEquations.toVector
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
          case (carried, (name, theorem)) =>
            for {
              found <- carried
              agreed <- connectiveVocabulary.checked(name, theorem)
            } yield found.updated(name, agreed)
        }
      connectiveFormulas <- formulaRules(
        connectiveVocabulary, connectiveCases, introductions)
      connectiveChecked <- connectiveFormulas.toVector
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
          case (carried, (name, theorem)) =>
            for {
              found <- carried
              agreed <- connectiveVocabulary.checked(name, theorem)
            } yield found.updated(name, agreed)
        }
      // The twelve clauses, after the well-formedness rules and for the same reason those come
      // after the definitions: each is proved by rewriting with the defining equations, so the
      // six have to be in the theory before any of them can be stated.
      connectiveClauseFacts <- connectiveClauses(
        connectiveVocabulary,
        connectiveCases,
        Map(
          FreeVariable -> freeVariable,
          FreeZero -> freeZero,
          FreeSuccessor -> freeSuccessor,
          FreeSum -> freeSum,
          FreeProduct -> freeProduct,
          FormulaFreeEquality -> formulaFreeEquality,
          FormulaFreeNegation -> formulaFreeNegation,
          FormulaFreeImplication -> formulaFreeImplication,
          FormulaFreeUniversal -> formulaFreeUniversal,
          SubstituteVariable -> substituteVariable,
          SubstituteZero -> substituteZero,
          SubstituteSuccessor -> substituteSuccessor,
          SubstituteSum -> substituteSum,
          SubstituteProduct -> substituteProduct,
          FormulaSubstituteEquality -> formulaSubstituteEquality,
          FormulaSubstituteNegation -> formulaSubstituteNegation,
          FormulaSubstituteImplication -> formulaSubstituteImplication,
          FormulaSubstituteUniversal -> formulaSubstituteUniversal
        )
      )
      connectiveClausesChecked <- connectiveClauseFacts.toVector
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
          case (carried, (name, theorem)) =>
            for {
              found <- carried
              agreed <- connectiveVocabulary.checked(name, theorem)
            } yield found.updated(name, agreed)
        }
    } yield new Language(
      numbering,
      connectiveTheory,
      notation,
      connectiveLogic,
      successor,
      Map(
        TermName -> definition,
        FormulaName -> formulaDefinition,
        NumeralName -> numeralDefinition,
        SubstituteName -> substituteDefinition,
        FormulaSubstituteName -> formulaSubstituteDefinition,
        FreeName -> freeDefinition,
        FormulaFreeName -> formulaFreeDefinition,
        ClosedName -> closedDefinition,
        AxiomName -> axiomDefinition,
        LogicName -> logicDefinition
      ) ++ connectiveDefinitions,
      Map(
        TermCases -> cases,
        TermVariable -> variable,
        TermZero -> zero,
        TermSuccessor -> successorRule,
        TermSum -> sum,
        TermProduct -> product,
        TermNotZero -> notZero,
        FormulaCases -> formulaCases,
        FormulaEquality -> equality,
        FormulaNegation -> negation,
        FormulaImplication -> implication,
        FormulaUniversal -> universal,
        FormulaNotZero -> formulaNotZero,
        NumeralAtZero -> numeralAtZero,
        NumeralAtSuccessor -> numeralAtSuccessor,
        NumeralIsTerm -> numeralIsTerm,
        NumeralIsClosed -> numeralIsClosed,
        ClosedZero -> closures(ClosedZero),
        ClosedSuccessor -> closures(ClosedSuccessor),
        ClosedSum -> closures(ClosedSum),
        ClosedProduct -> closures(ClosedProduct),
        NumeralInjective -> numeralInjective,
        SubstituteVariable -> substituteVariable,
        SubstituteZero -> substituteZero,
        SubstituteSuccessor -> substituteSuccessor,
        SubstituteSum -> substituteSum,
        SubstituteProduct -> substituteProduct,
        FormulaSubstituteEquality -> formulaSubstituteEquality,
        FormulaSubstituteNegation -> formulaSubstituteNegation,
        FormulaSubstituteImplication -> formulaSubstituteImplication,
        FormulaSubstituteUniversal -> formulaSubstituteUniversal,
        SubstituteKeepsTerms -> substituteKeepsTerms,
        SubstituteIdle -> substituteIsIdle,
        FormulaSubstituteKeepsFormulas -> formulaSubstituteKeepsFormulas,
        FreeVariable -> freeVariable,
        FreeZero -> freeZero,
        FreeSuccessor -> freeSuccessor,
        FreeSum -> freeSum,
        FreeProduct -> freeProduct,
        FormulaFreeEquality -> formulaFreeEquality,
        FormulaFreeNegation -> formulaFreeNegation,
        FormulaFreeImplication -> formulaFreeImplication,
        FormulaFreeUniversal -> formulaFreeUniversal
      ) ++ axiomFacts
        .updated(AxiomCases, axiomCases)
        .updated(AxiomFormula, axiomFormula)
        .updated(ClosedCases, closedCases)
        .updated(LogicCases, logicCases)
        .updated(LogicFormula, logicFormula) ++ logicFacts ++ connectiveCases ++
        connectiveChecked ++ connectiveClausesChecked
    )
  }

  /**
   * Take a step to a named constant, which is the four moves both predicates make.
   *
   * `Descent` is applied to the step, the admissibility condition is proved, one function
   * satisfying the recursion is **chosen**, and the chosen term is given a name. What comes back is
   * the recursion equation with the constant in it rather than the choice, which is a rewrite with
   * the definition read backwards and is the only place the `select` is visible.
   *
   * Written once because the formulas are the terms with a different step and a different clause
   * table, and the alternative was two copies of a path that ends in `Kernel.defineConstant`.
   */
  private def definePredicate(
    numbering: Numbering,
    recursion: Kernel.Thm,
    base: Theory,
    notation: Notation,
    logic: Logic,
    name: String,
    stepText: String,
    clauses: Vector[Clause]
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] =
    for {
      step <- Parser.term(base, notation, stepText)
      atPropositions = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), recursion)
      instance <- logic.rules.spec(step, atPropositions)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      parts <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      (admissible, _) = parts

      condition <- stepIsAdmissible(numbering, logic, admissible, clauses)
      exists <- logic.rules.mp(opened, condition)

      chosen <- numbering.peano.naturals.classical.witness(exists)
      selected <- chosen.conclusion match {
        case App(_, term) => Right(term)
        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }
      defined <- LogicError.lift(Kernel.defineConstant(base, name, selected))
      (theory, definition) = defined
      wider <- logic.over(theory)

      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
      named <- Conv
        .sym(definition)
        .flatMap(Rewrite.Rule.of(wider, _))
        .flatMap(rule => Rewrite.inTheorem(Vector(rule), reduced))
    } yield (theory, definition, named)

  /** What the derivations below reach for, gathered once, as every development above does. */
  private final case class Vocabulary(
    numbering: Numbering,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    numbers: Type,
    zero: Term,
    successor: Term,
    below: Term,
    atMost: Term,
    code: Term,
    pair: Term,
    predicate: Term,
    formula: Term,
    numeral: Term,
    substitute: Term,
    facts: Map[String, Kernel.Thm]
  ) {

    val rules: Rules = logic.rules

    def coded(tag: Term, payload: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(code, List(tag, payload)))

    def paired(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(pair, List(left, right)))

    def isTerm(subject: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(predicate, subject))

    def isFormula(subject: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(formula, subject))

    /** The predicate a rule is about, by the name of the constant it concludes with. */
    def predicateNamed(name: String): Term = if (name == TermName) predicate else formula

    def fact(name: String): Either[LogicError, Kernel.Thm] =
      facts.get(name).toRight(MissingDefinition(name))

    def statement(name: String): Either[LogicError, Term] =
      Statements
        .collectFirst { case (key, text) if key == name => text }
        .toRight(MissingDefinition(name))
        .flatMap(Parser.proposition(theory, notation, _))

    def checked(name: String, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      statement(name).flatMap { expected =>
        if (theorem.conclusion == expected) Right(theorem)
        else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
      }

    /** `?x. body` at `argument`, beta-reduced, which this file does at four depths. */
    def instantiate(existential: Term, argument: Term): Either[LogicError, Term] =
      for {
        inner <- logic
          .destExistsPredicate(existential)
          .toRight(NotOfForm("an existential", existential))
        applied <- LogicError.lift(Term.app(inner, argument))
        contraction <- Conv.betaRoot(applied)
        body <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
      } yield body

    /** The four disjuncts of a step's body, flattened, in the order the step writes them. */
    def disjuncts(body: Term): Either[LogicError, Vector[Term]] =
      for {
        first <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
        second <- logic.destDisj(first._2).toRight(NotOfForm("a disjunction", first._2))
        third <- logic.destDisj(second._2).toRight(NotOfForm("a disjunction", second._2))
      } yield Vector(first._1, second._1, third._1, third._2)

    /** A proof of the `index`th disjunct, put back into the four-way disjunction. */
    def inject(parts: Vector[Term], index: Int, proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        tail <- logic.mkDisj(parts(2), parts(3))
        rest <- logic.mkDisj(parts(1), tail)
        result <- index match {
          case 0 => rules.disjIntro1(rest, proof)
          case 1 => rules.disjIntro1(tail, proof).flatMap(rules.disjIntro2(parts(0), _))
          case 2 =>
            rules
              .disjIntro1(parts(3), proof)
              .flatMap(rules.disjIntro2(parts(1), _))
              .flatMap(rules.disjIntro2(parts(0), _))
          case _ =>
            rules
              .disjIntro2(parts(2), proof)
              .flatMap(rules.disjIntro2(parts(1), _))
              .flatMap(rules.disjIntro2(parts(0), _))
        }
      } yield result

    /** `NUM_LT x z` from `NUM_LE x y` and `NUM_LT y z`, which every descent here goes through. */
    def descends(
      lower: Term,
      middle: Term,
      upper: Term,
      atMostThm: Kernel.Thm,
      belowThm: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      rules
        .conjIntro(atMostThm, belowThm)
        .flatMap(pieces =>
          fact(Peano.AtMostThenBelow)
            .flatMap(rules.specAll(_, List(lower, middle, upper)))
            .flatMap(rules.mp(_, pieces))
        )
  }

  private object Vocabulary {

    def of(
      numbering: Numbering,
      theory: Theory,
      notation: Notation,
      logic: Logic
    ): Either[LogicError, Vocabulary] = {
      val numbers = TyApp(Natural.TypeName, Nil)
      val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
      val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

      for {
        zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
        successor <- LogicError.lift(
          theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
        )
        below <- LogicError.lift(theory.constant(Peano.StrictOrder, relation))
        atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, relation))
        code <- LogicError.lift(theory.constant(Numbering.CodeName, arithmetic))
        pair <- LogicError.lift(theory.constant(Numbering.PairName, arithmetic))
        predicate <- LogicError.lift(
          theory.constant(TermName, Type.fun(numbers, Type.Bool))
        )
        formula <- LogicError.lift(
          theory.constant(FormulaName, Type.fun(numbers, Type.Bool))
        )
        numeral <- LogicError.lift(
          theory.constant(NumeralName, Type.fun(numbers, numbers))
        )
        substitute <- LogicError.lift(
          theory.constant(
            SubstituteName,
            Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers)))
          )
        )
        mixed <- numbering.peano.fact(Peano.AtMostThenBelow)
        codeRight <- numbering.fact(Numbering.CodeRight)
        codeNotZero <- numbering.fact(Numbering.CodeNotZero)
        pairLeft <- numbering.fact(Numbering.PairLeft)
        pairRight <- numbering.fact(Numbering.PairRight)
      } yield Vocabulary(
        numbering,
        theory,
        notation,
        logic,
        numbers,
        zero,
        successor,
        below,
        atMost,
        code,
        pair,
        predicate,
        formula,
        numeral,
        substitute,
        Map(
          Peano.AtMostThenBelow -> mixed,
          Numbering.CodeRight -> codeRight,
          Numbering.CodeNotZero -> codeNotZero,
          Numbering.PairLeft -> pairLeft,
          Numbering.PairRight -> pairRight
        )
      )
    }
  }

  /* ------------------------------------------------------- the admissibility condition */

  /**
   * The step gives the same answer to two functions that agree below the index.
   *
   * The condition [[Descent]] asks for, and the reason this file is long. It is proved **before**
   * `NUM_TERM` exists and cannot use it: what it is about is the step applied to two arbitrary
   * functions `u` and `v`, and the constant is what comes out afterwards.
   *
   * The shape is one implication proved twice. `Kernel.deductAntisym` turns `p |- q` and `q |- p`
   * into `|- p = q`, so [[carriedAcross]] is written once, for an arbitrary source and target, and
   * called with the two functions in each order. The second call is handed the agreement read
   * backwards, which is the agreement with `Conv.sym` under its own quantifier.
   */
  private def stepIsAdmissible(
    numbering: Numbering,
    logic: Logic,
    admissible: Term,
    clauses: Vector[Clause]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      below <- LogicError.lift(
        numbering.theory.constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      stripped <- Logic.stripForall(admissible)
      u <- stripped._1.headOption.toRight(NotOfForm("a claim about every function", admissible))
      v <- stripped._1.drop(1).headOption
        .toRight(NotOfForm("a claim about two functions", admissible))
      index <- stripped._1.drop(2).headOption
        .toRight(NotOfForm("a claim about every index", admissible))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (agreement, equation) = body
      assumed <- LogicError.lift(Kernel.assume(agreement))
      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      (fromU, fromV) = sides

      forwards <- carriedAcross(
        numbering, logic, below, fromU, fromV, assumed, index, Set(u, v, index), clauses)

      // The same agreement with its two sides exchanged, which the other direction is given.
      backwardsAgreement <- {
        val variable = Conv.freshVariable("m", numbers, Set(u, v, index))
        for {
          comparison <- LogicError.lift(Term.appAll(below, List(variable, index)))
          assumedBelow <- LogicError.lift(Kernel.assume(comparison))
          here <- rules.spec(variable, assumed).flatMap(rules.mp(_, assumedBelow))
          swapped <- Conv.sym(here)
          result <- rules.disch(comparison, swapped).flatMap(rules.gen(variable, _))
        } yield result
      }
      backwards <- carriedAcross(
        numbering, logic, below, fromV, fromU, backwardsAgreement, index, Set(u, v, index), clauses)

      equated = Kernel.deductAntisym(backwards, forwards)
      discharged <- rules.disch(agreement, equated)
      general <- rules.genAll(discharged, List(u, v, index))
      _ <-
        if (general.conclusion == admissible) Right(())
        else Left(NotOfForm("the condition as the recursion states it", general.conclusion))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a condition with nothing assumed", general.conclusion))
    } yield general
  }

  /**
   * The step at one function gives the step at the other, under the agreement.
   *
   * Four cases and only two of them mention the function at all. A variable and a zero are carried
   * across untouched; a successor moves its one recursive answer across the agreement at the
   * payload; a sum or a product moves two, at the components of the payload.
   *
   * **Every move needs the argument to be below the index and that is the whole of why it works.**
   * The payload is below because the code's own equation says `n = NUM_CODE t p` and
   * `Numbering.CodeRight` bounds the payload by the code. Each component is below because the
   * pairing bounds it by the payload and the payload is below the index. `docs/adr/0014` calls that
   * bound the construction's reason and this is the place it is spent.
   */
  private def carriedAcross(
    numbering: Numbering,
    logic: Logic,
    below: Term,
    source: Term,
    target: Term,
    agreement: Kernel.Thm,
    index: FVar,
    avoid: Set[FVar],
    clauses: Vector[Clause]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def instantiate(existential: Term, argument: Term): Either[LogicError, Term] =
      for {
        inner <- logic
          .destExistsPredicate(existential)
          .toRight(NotOfForm("an existential", existential))
        applied <- LogicError.lift(Term.app(inner, argument))
        contraction <- Conv.betaRoot(applied)
        body <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
      } yield body

    def disjuncts(body: Term): Either[LogicError, Vector[Term]] =
      for {
        first <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
        second <- logic.destDisj(first._2).toRight(NotOfForm("a disjunction", first._2))
        third <- logic.destDisj(second._2).toRight(NotOfForm("a disjunction", second._2))
      } yield Vector(first._1, second._1, third._1, third._2)

    def inject(parts: Vector[Term], which: Int, proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        tail <- logic.mkDisj(parts(2), parts(3))
        rest <- logic.mkDisj(parts(1), tail)
        result <- which match {
          case 0 => rules.disjIntro1(rest, proof)
          case 1 => rules.disjIntro1(tail, proof).flatMap(rules.disjIntro2(parts(0), _))
          case 2 =>
            rules
              .disjIntro1(parts(3), proof)
              .flatMap(rules.disjIntro2(parts(1), _))
              .flatMap(rules.disjIntro2(parts(0), _))
          case _ =>
            rules
              .disjIntro2(parts(2), proof)
              .flatMap(rules.disjIntro2(parts(1), _))
              .flatMap(rules.disjIntro2(parts(0), _))
        }
      } yield result

    def opening(existential: Term, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        assumed <- LogicError.lift(Kernel.assume(existential))
        inner <- logic
          .destExistsPredicate(existential)
          .toRight(NotOfForm("an existential", existential))
        variable = Conv.freshVariable(name, numbers, taken ++ Term.freeVariables(existential))
        applied <- LogicError.lift(Term.app(inner, variable))
        contraction <- Conv.betaRoot(applied)
        body <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        instance <- LogicError.lift(Kernel.assume(body))
        reached <- reach(variable, instance, body)
        result <- rules.existsElim(assumed, variable, reached)
      } yield result

    /**
     * A component of the payload is below the index, which is two steps and both are published.
     *
     * The pairing bounds the component by the pair; the case's own equation says the pair IS the
     * payload; and the payload was bounded by the index before the cases were opened. The mixed
     * transitivity of `Peano` is what joins a non-strict bound to a strict one.
     */
    def componentBelow(
      which: String,
      left: Term,
      right: Term,
      component: Term,
      isPair: Kernel.Thm,
      payload: Term,
      payloadBelow: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        atMost <- LogicError.lift(
          numbering.theory.constant(
            Peano.NonStrictOrder,
            Type.fun(numbers, Type.fun(numbers, Type.Bool))
          )
        )
        inPair <- numbering.fact(which).flatMap(rules.specAll(_, List(left, right)))
        headed <- LogicError.lift(Term.app(atMost, component))
        inPayload <- Conv
          .sym(isPair)
          .flatMap(equation => Conv.apTerm(headed, equation))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, inPair)))
        joined <- rules.conjIntro(inPayload, payloadBelow)
        result <- numbering.peano
          .fact(Peano.AtMostThenBelow)
          .flatMap(rules.specAll(_, List(component, payload, index)))
          .flatMap(rules.mp(_, joined))
      } yield result

    /** `u x = v x` wherever `x` is below the index, which is the agreement applied. */
    def agreedAt(argument: Term, belowThm: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules.spec(argument, agreement).flatMap(rules.mp(_, belowThm))

    /**
     * The four disjuncts, each carried from the source's shape to the target's.
     *
     * The first two are the same term on both sides and go across by `disjIntro` alone. The third
     * moves one answer and the fourth moves two, and both moves are `Kernel.eqMp` against the
     * agreement at an argument this derivation has just bounded.
     */
    def eachClause(
      payload: Term,
      payloadBelow: Kernel.Thm,
      disjunction: Kernel.Thm,
      sourceParts: Vector[Term],
      targetParts: Vector[Term],
      taken: Set[FVar]
    ): Either[LogicError, Kernel.Thm] = {

      /**
       * The two components of a pair carried across, moving one answer or both.
       *
       * `AtBoth` and `AtSecond` differ in two places and nowhere else: whether the left component's
       * answer is moved, and whether what sits under the pair's equation is a conjunction of two
       * answers or one. Everything between, the opening of the two witnesses and the bound each
       * component inherits from the payload, is the same.
       */
      def pairedArguments(
        which: Int,
        arguments: Kernel.Thm,
        moveLeft: Boolean
      ): Either[LogicError, Kernel.Thm] =
        for {
          targetArguments <- logic
            .destConj(targetParts(which))
            .toRight(NotOfForm("a conjunction", targetParts(which)))
          moved <- opening(arguments.conclusion, "a", taken) { (left, _, atLeft) =>
            opening(atLeft, "b", taken + left) { (right, atRight, _) =>
              for {
                isPair <- rules.conjElim1(atRight)
                rest <- rules.conjElim2(atRight)

                rightBelow <- componentBelow(
                  Numbering.PairRight, left, right, right, isPair, payload, payloadBelow)
                answers <-
                  if (moveLeft)
                    for {
                      atLeftArgument <- rules.conjElim1(rest)
                      atRightArgument <- rules.conjElim2(rest)
                      leftBelow <- componentBelow(
                        Numbering.PairLeft, left, right, left, isPair, payload, payloadBelow)
                      movedLeft <- agreedAt(left, leftBelow)
                        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atLeftArgument)))
                      movedRight <- agreedAt(right, rightBelow)
                        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atRightArgument)))
                      both <- rules.conjIntro(movedLeft, movedRight)
                    } yield both
                  else
                    agreedAt(right, rightBelow)
                      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, rest)))

                targetOuterArgument <- logic
                  .destExistsPredicate(targetArguments._2)
                  .toRight(NotOfForm("an existential", targetArguments._2))
                targetAtLeft <- instantiate(targetArguments._2, left)
                targetInnerArgument <- logic
                  .destExistsPredicate(targetAtLeft)
                  .toRight(NotOfForm("an existential", targetAtLeft))

                rebuilt <- rules.conjIntro(isPair, answers)
                withRight <- rules.existsIntro(targetInnerArgument, right, rebuilt)
                withLeft <- rules.existsIntro(targetOuterArgument, left, withRight)
              } yield withLeft
            }
          }

          // `opening` assumed a fresh copy of the existential; this is where it meets the one the
          // case actually gives. Without it the witnesses escape their own elimination and the
          // refusal arrives pages later.
          result <- rules.disch(arguments.conclusion, moved).flatMap(rules.mp(_, arguments))
        } yield result

      def atArgument(which: Int): Either[LogicError, Kernel.Thm] =
        for {
          assumed <- LogicError.lift(Kernel.assume(sourceParts(which)))
          result <- clauses(which) match {
            case Clause.Opaque => inject(targetParts, which, assumed)
            case Clause.AtPayload =>
              for {
                tagIs <- rules.conjElim1(assumed)
                applied <- rules.conjElim2(assumed)
                agreed <- agreedAt(payload, payloadBelow)
                moved <- LogicError.lift(Kernel.eqMp(agreed, applied))
                rebuilt <- rules.conjIntro(tagIs, moved)
                placed <- inject(targetParts, which, rebuilt)
              } yield placed
            case shape =>
              for {
                tags <- rules.conjElim1(assumed)
                arguments <- rules.conjElim2(assumed)
                closed <- pairedArguments(which, arguments, shape == Clause.AtBoth)
                rebuilt <- rules.conjIntro(tags, closed)
                placed <- inject(targetParts, which, rebuilt)
              } yield placed
          }
        } yield result

      for {
        tailTerm <- logic.mkDisj(sourceParts(2), sourceParts(3))
        restTerm <- logic.mkDisj(sourceParts(1), tailTerm)
        assumedTail <- LogicError.lift(Kernel.assume(tailTerm))
        assumedRest <- LogicError.lift(Kernel.assume(restTerm))
        third <- atArgument(2)
        fourth <- atArgument(3)
        insideTail <- rules.disjElim(assumedTail, third, fourth)
        second <- atArgument(1)
        insideRest <- rules.disjElim(assumedRest, second, insideTail)
        first <- atArgument(0)
        result <- rules.disjElim(disjunction, first, insideRest)
      } yield result
    }

    opening(source, "t", avoid) { (tag, _, atTag) =>
      opening(atTag, "p", avoid + tag) { (payload, atPayload, _) =>
        for {
          isCode <- rules.conjElim1(atPayload)
          disjunction <- rules.conjElim2(atPayload)

          // The payload is below the index, which every recursive answer moves across.
          rawBound <- numbering
            .fact(Numbering.CodeRight)
            .flatMap(rules.specAll(_, List(tag, payload)))
          headedBelow <- LogicError.lift(Term.app(below, payload))
          payloadBelow <- Conv
            .sym(isCode)
            .flatMap(equation => Conv.apTerm(headedBelow, equation))
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, rawBound)))

          targetAtTag <- instantiate(target, tag)
          targetBody <- instantiate(targetAtTag, payload)
          targetDisjunction <- logic
            .destConj(targetBody)
            .toRight(NotOfForm("a conjunction", targetBody))
          targetParts <- disjuncts(targetDisjunction._2)
          sourceAtTag <- instantiate(source, tag)
          sourceBody <- instantiate(sourceAtTag, payload)
          sourceDisjunction <- logic
            .destConj(sourceBody)
            .toRight(NotOfForm("a conjunction", sourceBody))
          sourceParts <- disjuncts(sourceDisjunction._2)

          settled <- eachClause(
            payload, payloadBelow, disjunction, sourceParts, targetParts, avoid + tag + payload)

          rebuilt <- rules.conjIntro(isCode, settled)
          targetInner <- logic
            .destExistsPredicate(targetAtTag)
            .toRight(NotOfForm("an existential", targetAtTag))
          targetOuter <- logic
            .destExistsPredicate(target)
            .toRight(NotOfForm("an existential", target))
          withPayload <- rules.existsIntro(targetInner, payload, rebuilt)
          result <- rules.existsIntro(targetOuter, tag, withPayload)
          _ = index
        } yield result
      }
    }
  }

  /* ------------------------------------------------------------- the introduction rules */

  /**
   * One tag of [[TermCases]], read in the direction that builds a term rather than takes one apart.
   *
   * Every rule here is the same four steps: instantiate the equation at the code being built, put
   * the tag and the payload into the two existentials, prove the disjunct the tag selects, and
   * carry the whole thing back across the equation. What differs between the five is only which
   * disjunct and what it asks for, which is nothing for a variable and two premises for a sum.
   */
  /**
   * Build `P (NUM_CODE tag payload)` from a proof of the disjunct that tag selects.
   *
   * The four moves both predicates make in the direction that builds rather than takes apart:
   * instantiate the recursion equation at the code, prove the disjunct, put the tag and the payload
   * into the two existentials, and carry the whole thing back across the equation. What differs
   * between the nine rules in this file is only which disjunct and what it asks for.
   */
  private def builtAtCode(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    tag: Term,
    payload: Term,
    index: Int,
    disjunct: Vector[Term] => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic

    for {
      coded <- vocabulary.coded(tag, payload)
      instance <- rules.spec(coded, cases)
      right <- Term
        .destEq(instance.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", instance.conclusion))
      atTag <- vocabulary.instantiate(right, tag)
      body <- vocabulary.instantiate(atTag, payload)
      split <- logic.destConj(body).toRight(NotOfForm("a conjunction", body))
      parts <- vocabulary.disjuncts(split._2)
      proof <- disjunct(parts)
      placed <- vocabulary.inject(parts, index, proof)
      conjoined <- rules.conjIntro(Conv.refl(coded), placed)
      inner <- logic
        .destExistsPredicate(atTag)
        .toRight(NotOfForm("an existential", atTag))
      outer <- logic
        .destExistsPredicate(right)
        .toRight(NotOfForm("an existential", right))
      withPayload <- rules.existsIntro(inner, payload, conjoined)
      withTag <- rules.existsIntro(outer, tag, withPayload)
      result <- Conv
        .sym(instance)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, withTag)))
    } yield result
  }

  /**
   * A payload that is a pair, put back into its disjunct's two existentials.
   *
   * `rest` is whatever sits under the pair's own equation: two answers for a binary constructor,
   * one for the quantifier, whose first component is an index rather than a code. That is the only
   * difference between the three rules that use this, and it is a parameter rather than a branch.
   */
  private def pairedPayload(
    vocabulary: Vocabulary,
    parts: Vector[Term],
    index: Int,
    left: Term,
    right: Term,
    rest: Kernel.Thm,
    tagProof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic

    for {
      split <- logic.destConj(parts(index)).toRight(NotOfForm("a conjunction", parts(index)))
      outer <- logic
        .destExistsPredicate(split._2)
        .toRight(NotOfForm("an existential", split._2))
      atLeft <- vocabulary.instantiate(split._2, left)
      inner <- logic
        .destExistsPredicate(atLeft)
        .toRight(NotOfForm("an existential", atLeft))
      paired <- vocabulary.paired(left, right)
      rebuilt <- rules.conjIntro(Conv.refl(paired), rest)
      withRight <- rules.existsIntro(inner, right, rebuilt)
      withLeft <- rules.existsIntro(outer, left, withRight)
      result <- rules.conjIntro(tagProof, withLeft)
    } yield result
  }

  /**
   * The four introduction rules of [[FormulaCases]], read in the building direction.
   *
   * The same four moves as [[introduceTerm]] over a different table. Two of them are worth a line:
   * the equality asks for two **terms** and not two formulas, which is the one place the two
   * predicates meet; and the quantifier's payload pairs an index with a formula, so only its second
   * component carries a premise.
   */
  private def introduceFormula(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    which: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers

    def numeral(text: String): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, text, numbers)

    /**
     * A rule whose payload is a pair, with whatever premises its components carry.
     *
     * `leftPremise` is an `Option` and that is the quantifier: its first component is a variable
     * **index**, which carries no premise at all, so there is nothing to assume and nothing to
     * discharge. Passing a placeholder instead would mean assuming a term of `num` as though it
     * were a proposition, which is what the first version of this did and what the kernel refused.
     */
    def overAPair(
      tagText: String,
      index: Int,
      leftName: String,
      rightName: String,
      leftPremise: Option[Term => Either[LogicError, Term]],
      rightPremise: Term => Either[LogicError, Term]
    ): Either[LogicError, Kernel.Thm] = {
      val left = Term.variable(leftName, numbers)
      val right = Term.variable(rightName, numbers)
      for {
        tag <- numeral(tagText)
        paired <- vocabulary.paired(left, right)
        onTheLeft <- leftPremise.fold[Either[LogicError, Option[(Term, Kernel.Thm)]]](Right(None))(
          build =>
            for {
              proposition <- build(left)
              assumed <- LogicError.lift(Kernel.assume(proposition))
            } yield Some((proposition, assumed))
        )
        rightTerm <- rightPremise(right)
        rightAssumed <- LogicError.lift(Kernel.assume(rightTerm))
        built <- builtAtCode(
          vocabulary,
          cases,
          tag,
          paired,
          index,
          parts =>
            for {
              rest <- onTheLeft.fold[Either[LogicError, Kernel.Thm]](Right(rightAssumed))(
                pair => rules.conjIntro(pair._2, rightAssumed)
              )
              result <- pairedPayload(
                vocabulary, parts, index, left, right, rest, Conv.refl(tag))
            } yield result
        )
        afterRight <- rules.disch(rightTerm, built)
        discharged <- onTheLeft.fold[Either[LogicError, Kernel.Thm]](Right(afterRight))(
          pair => rules.disch(pair._1, afterRight)
        )
        general <- rules.genAll(discharged, List(left, right))
        result <- vocabulary.checked(which, general)
      } yield result
    }

    which match {
      case FormulaEquality =>
        overAPair("5", 0, "a", "b", Some(vocabulary.isTerm), vocabulary.isTerm)

      case FormulaImplication =>
        overAPair("7", 2, "p", "q", Some(vocabulary.isFormula), vocabulary.isFormula)

      // The index carries no premise, so the rule takes one and generalises two.
      case FormulaUniversal =>
        overAPair("8", 3, "i", "p", None, vocabulary.isFormula)

      case _ =>
        val argument = Term.variable("p", numbers)
        for {
          tag <- numeral("6")
          premise <- vocabulary.isFormula(argument)
          assumed <- LogicError.lift(Kernel.assume(premise))
          built <- builtAtCode(
            vocabulary, cases, tag, argument, 1,
            _ => rules.conjIntro(Conv.refl(tag), assumed))
          discharged <- rules.disch(premise, built)
          general <- rules.gen(argument, discharged)
          result <- vocabulary.checked(FormulaNegation, general)
        } yield result
    }
  }

  private def introduceTerm(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    which: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val numbers = vocabulary.numbers

    def atTagAndPayload(
      tag: Term,
      payload: Term,
      index: Int,
      disjunct: Vector[Term] => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      builtAtCode(vocabulary, cases, tag, payload, index, disjunct)

    def binaryArguments(
      parts: Vector[Term],
      left: Term,
      right: Term,
      leftIsTerm: Kernel.Thm,
      rightIsTerm: Kernel.Thm,
      tagProof: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      rules
        .conjIntro(leftIsTerm, rightIsTerm)
        .flatMap(pairedPayload(vocabulary, parts, 3, left, right, _, tagProof))

    def numeral(text: String): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, text, numbers)

    which match {
      case TermVariable =>
        val index = Term.variable("i", numbers)
        for {
          tag <- numeral("0")
          built <- atTagAndPayload(tag, index, 0, _ => Right(Conv.refl(tag)))
          general <- rules.gen(index, built)
          result <- vocabulary.checked(TermVariable, general)
        } yield result

      case TermZero =>
        for {
          tag <- numeral("1")
          built <- atTagAndPayload(
            tag,
            vocabulary.zero,
            1,
            _ => rules.conjIntro(Conv.refl(tag), Conv.refl(vocabulary.zero))
          )
          result <- vocabulary.checked(TermZero, built)
        } yield result

      case TermSuccessor =>
        val argument = Term.variable("t", numbers)
        for {
          tag <- numeral("2")
          premise <- vocabulary.isTerm(argument)
          assumed <- LogicError.lift(Kernel.assume(premise))
          built <- atTagAndPayload(tag, argument, 2, _ => rules.conjIntro(Conv.refl(tag), assumed))
          discharged <- rules.disch(premise, built)
          general <- rules.gen(argument, discharged)
          result <- vocabulary.checked(TermSuccessor, general)
        } yield result

      case _ =>
        val left = Term.variable("a", numbers)
        val right = Term.variable("b", numbers)
        for {
          tag <- numeral(if (which == TermSum) "3" else "4")
          other <- numeral(if (which == TermSum) "4" else "3")
          paired <- vocabulary.paired(left, right)
          leftPremise <- vocabulary.isTerm(left)
          rightPremise <- vocabulary.isTerm(right)
          leftAssumed <- LogicError.lift(Kernel.assume(leftPremise))
          rightAssumed <- LogicError.lift(Kernel.assume(rightPremise))
          built <- atTagAndPayload(
            tag,
            paired,
            3,
            parts =>
              for {
                sameTag <- LogicError.lift(Term.eq(tag, other))
                tagProof <-
                  if (which == TermSum) rules.disjIntro1(sameTag, Conv.refl(tag))
                  else rules.disjIntro2(sameTag, Conv.refl(tag))
                result <- binaryArguments(
                  parts, left, right, leftAssumed, rightAssumed, tagProof)
              } yield result
          )
          discharged <- rules
            .disch(rightPremise, built)
            .flatMap(rules.disch(leftPremise, _))
          general <- rules.genAll(discharged, List(left, right))
          result <- vocabulary.checked(which, general)
        } yield result
    }
  }

  /**
   * [[TermNotZero]]: nothing codes a term at zero, and the refusal comes from the constructor.
   *
   * Read [[TermCases]] the other way once. If `ZERO` were a term it would be `NUM_CODE t p` for
   * some tag and payload, and `Numbering.CodeNotZero` says no code is zero. No clause of the step
   * mentions zero and none has to.
   */
  private def zeroCodesNothing(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    constant: String,
    statement: String
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    /**
     * Open `?x. body` with a fresh name, **leaving the existential itself assumed**.
     *
     * The assumption is not discharged here and cannot be: `Rules.existsElim` removes the instance
     * from the case's hypotheses, not the existential from its own. A caller that reached the
     * existential as a theorem has to put the two together with `disch` and `mp`, and one that
     * meant it to stay a hypothesis, as the outermost call here does, leaves it.
     */
    def opening(existential: Term, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        assumed <- LogicError.lift(Kernel.assume(existential))
        inner <- logic
          .destExistsPredicate(existential)
          .toRight(NotOfForm("an existential", existential))
        variable = Conv.freshVariable(name, vocabulary.numbers, taken)
        applied <- LogicError.lift(Term.app(inner, variable))
        contraction <- Conv.betaRoot(applied)
        body <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        instance <- LogicError.lift(Kernel.assume(body))
        reached <- reach(variable, instance, body)
        result <- rules.existsElim(assumed, variable, reached)
      } yield result

    for {
      claim <- LogicError.lift(
        Term.app(vocabulary.predicateNamed(constant), vocabulary.zero)
      )
      assumed <- LogicError.lift(Kernel.assume(claim))
      instance <- rules.spec(vocabulary.zero, cases)
      opened <- LogicError.lift(Kernel.eqMp(instance, assumed))
      absurd <- opening(opened.conclusion, "t", Set.empty) { (tag, _, atTag) =>
        opening(atTag, "p", Set(tag)) { (payload, atPayload, _) =>
          for {
            isCode <- rules.conjElim1(atPayload)
            backwards <- Conv.sym(isCode)
            never <- vocabulary
              .fact(Numbering.CodeNotZero)
              .flatMap(rules.specAll(_, List(tag, payload)))
            contradiction <- rules.notElim(never, backwards)
          } yield contradiction
        }
      }
      // `opening` assumes the existential and leaves that assumption standing, because the
      // elimination it does discharges the INSTANCE and not the existential. A caller that already
      // has the existential as a theorem has to meet the two, and this is the third place in this
      // file that is true of.
      closed <- rules.disch(opened.conclusion, absurd).flatMap(rules.mp(_, opened))
      refuted <- rules.notIntro(claim, closed)
      _ <-
        if (refuted.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a refusal with nothing assumed", refuted.conclusion))
      result <- vocabulary.checked(statement, refuted)
    } yield result
  }

  /* ------------------------------------------------------------------------ the numerals */

  /**
   * [[NumeralIsTerm]], by induction, and both cases are one introduction rule.
   *
   * The base is [[TermZero]] carried across the recurrence and the step is [[TermSuccessor]] applied
   * to the hypothesis. Nothing here is about coding: it is the observation that a tower of
   * successors over zero is built by the two rules that build successors over zero.
   */
  private def everyNumeralIsATerm(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    zeroIsTerm: Kernel.Thm,
    successorRule: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    /** The claim at a numeral, carried backwards along the recurrence that produced it. */
    def across(recurrence: Kernel.Thm, proved: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .sym(recurrence)
        .flatMap(equation => Conv.apTerm(vocabulary.predicate, equation))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, proved)))

    for {
      statement <- vocabulary.statement(NumeralIsTerm)
      proved <- driver.proveBy(
        statement,
        _ => across(atZero, zeroIsTerm),
        step =>
          for {
            recurrence <- rules.spec(step.variable, atSuccessor)
            // The hypothesis is `NUM_TERM (NUM_NUMERAL k)`, so its argument is the numeral the
            // successor rule has to be applied to.
            inner <- step.hypothesis.conclusion match {
              case App(_, argument) => Right(argument)
              case other => Left(NotOfForm("a claim about a numeral", other))
            }
            built <- rules.spec(inner, successorRule).flatMap(rules.mp(_, step.hypothesis))
            result <- across(recurrence, built)
          } yield result
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(NumeralIsTerm, proved)
    } yield result
  }

  /**
   * The six well-formedness rules, each proved from what is already published and from the ones
   * proved before it.
   *
   * A code one of these builds is a formula because the code it abbreviates is one, so every proof
   * here is the same four moves: read the published statement, assume its antecedents, compose the
   * rules for the shape, and carry the result back across the defining equation. What differs
   * between the six is only which rules compose, which is why they are a table rather than six
   * derivations.
   *
   * **The order is the definitions' order and for the definitions' reason.** What proves
   * [[AllBelowFormula]] is [[LessFormula]], not a second descent to the tags; the accumulator below
   * is what makes a rule proved here available to the next one. Walking down to the tags each time
   * would work and would be the version that goes wrong quietly, because a comparison expanded by
   * hand in two places is two chances to expand it differently.
   */
  private def formulaRules(
    vocabulary: Vocabulary,
    cases: Map[String, Kernel.Thm],
    published: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic

    /** The code a `NUM_TERM` or a `NUM_FORM` is about. */
    def subjectOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      theorem.conclusion match {
        case App(_, subject) => Right(subject)
        case other => Left(NotOfForm("a predicate applied to a code", other))
      }

    /**
     * One rule applied: its index arguments first, then the codes its premises are about.
     *
     * Every rule in this development concluding `NUM_TERM` or `NUM_FORM` of a built code has that
     * shape, the six below included, which is what lets one combinator serve all of them and is
     * worth preserving in a seventh.
     */
    def by(
      facts: Map[String, Kernel.Thm],
      name: String,
      indices: List[Term],
      premises: List[Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        rule <- facts.get(name).toRight(MissingDefinition(name))
        subjects <- premises.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) {
          case (carried, premise) =>
            for {
              found <- carried
              subject <- subjectOf(premise)
            } yield found :+ subject
        }
        instance <- rules.specAll(rule, indices ++ subjects)
        reached <- premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(instance)) {
          case (carried, premise) => carried.flatMap(rules.mp(_, premise))
        }
      } yield reached

    /** Assume every antecedent of a published statement, in the order it writes them. */
    def peel(
      body: Term,
      taken: List[Kernel.Thm]
    ): Either[LogicError, (List[Kernel.Thm], Term)] =
      logic.destImp(body) match {
        case None => Right((taken.reverse, body))
        case Some((antecedent, rest)) =>
          LogicError
            .lift(Kernel.assume(antecedent))
            .flatMap(assumed => peel(rest, assumed :: taken))
      }

    def rule(
      facts: Map[String, Kernel.Thm],
      name: String,
      casesName: String,
      build: (Vector[FVar], Vector[Kernel.Thm]) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        statement <- vocabulary.statement(name)
        stripped <- Logic.stripForall(statement)
        (binders, body) = stripped
        peeled <- peel(body, Nil)
        (assumed, conclusion) = peeled
        equation <- cases
          .get(casesName)
          .toRight(MissingDefinition(casesName))
          .flatMap(rules.specAll(_, binders.toList))
        inner <- build(binders, assumed.toVector)
        lifted <- Conv.apTerm(vocabulary.formula, equation)
        reversed <- Conv.sym(lifted)
        reached <- LogicError.lift(Kernel.eqMp(reversed, inner))
        // The composition above could be right about a code and wrong about which code, since
        // every step of it is a theorem either way. This is where that is caught.
        _ <- Either.cond(
          reached.conclusion == conclusion,
          (),
          NotOfForm(s"the conclusion published for $name", reached.conclusion))
        discharged <- assumed.reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(reached)) {
          case (carried, assumption) => carried.flatMap(rules.disch(assumption.conclusion, _))
        }
        general <- binders.reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(discharged)) {
          case (carried, binder) => carried.flatMap(rules.gen(binder, _))
        }
      } yield general

    // Named rather than written inline: the shape spans three lines as a type ascription and one
    // as an alias, and what the three arguments are is the thing a reader of the table needs.
    type Build =
      (Map[String, Kernel.Thm], Vector[FVar], Vector[Kernel.Thm]) => Either[LogicError, Kernel.Thm]

    val steps: Vector[(String, String, Build)] = Vector(
      (
        AndFormula,
        AndCases,
        (facts, _, held) =>
          by(facts, FormulaNegation, Nil, List(held(1)))
            .flatMap(right => by(facts, FormulaImplication, Nil, List(held(0), right)))
            .flatMap(whole => by(facts, FormulaNegation, Nil, List(whole)))),
      (
        OrFormula,
        OrCases,
        (facts, _, held) =>
          by(facts, FormulaNegation, Nil, List(held(0)))
            .flatMap(left => by(facts, FormulaImplication, Nil, List(left, held(1))))),
      (
        ExistsFormula,
        ExistsCases,
        (facts, binders, held) =>
          by(facts, FormulaNegation, Nil, List(held(0)))
            .flatMap(inner => by(facts, FormulaUniversal, List(binders(0)), List(inner)))
            .flatMap(whole => by(facts, FormulaNegation, Nil, List(whole)))),
      (
        LessFormula,
        LessCases,
        (facts, binders, held) =>
          for {
            variable <- by(facts, TermVariable, List(binders(0)), Nil)
            stepped <- by(facts, TermSuccessor, Nil, List(variable))
            summed <- by(facts, TermSum, Nil, List(held(0), stepped))
            equated <- by(facts, FormulaEquality, Nil, List(summed, held(1)))
            whole <- by(facts, ExistsFormula, List(binders(0)), List(equated))
          } yield whole),
      (
        AllBelowFormula,
        AllBelowCases,
        (facts, binders, held) =>
          for {
            variable <- by(facts, TermVariable, List(binders(1)), Nil)
            below <- by(facts, LessFormula, List(binders(0)), List(variable, held(0)))
            implied <- by(facts, FormulaImplication, Nil, List(below, held(1)))
            whole <- by(facts, FormulaUniversal, List(binders(1)), List(implied))
          } yield whole),
      (
        ExistsBelowFormula,
        ExistsBelowCases,
        (facts, binders, held) =>
          for {
            variable <- by(facts, TermVariable, List(binders(1)), Nil)
            below <- by(facts, LessFormula, List(binders(0)), List(variable, held(0)))
            joined <- by(facts, AndFormula, Nil, List(below, held(1)))
            whole <- by(facts, ExistsFormula, List(binders(1)), List(joined))
          } yield whole)
    )

    steps.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
      case (carried, (name, casesName, build)) =>
        for {
          found <- carried
          facts = published ++ found
          proved <- rule(facts, name, casesName, (binders, held) => build(facts, binders, held))
        } yield found.updated(name, proved)
    }
  }

  /**
   * `|- COND T a b = a` and `|- COND F a b = b`, at one type.
   *
   * Derived rather than looked up because `COND_TRUE` and `COND_FALSE` carry their guard as a
   * hypothesis, and a rewrite rule is an equation and nothing else. Here rather than in either
   * caller because there are two of them and they ask at different types: [[substituteIn]] wants
   * the conditional between codes, and [[connectiveClauses]] wants it between codes and between
   * propositions, since a freeness clause answers with one and a substitution clause with the
   * other.
   */
  private[theories] def conditionalRules(
    logic: Logic,
    classical: Classical,
    at: Type
  ): Either[LogicError, Vector[Kernel.Thm]] = {
    val rules = logic.rules

    Vector(Classical.CondTrue, Classical.CondFalse)
      .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
        for {
          found <- carried
          truth <- rules.truth
          held <-
            if (name == Classical.CondTrue) Right(truth)
            else
              LogicError
                .lift(Kernel.assume(logic.falsity))
                .flatMap(rules.notIntro(logic.falsity, _))
          guard = if (name == Classical.CondTrue) truth.conclusion else logic.falsity
          left = Term.variable("a", at)
          right = Term.variable("b", at)
          scheme <- classical
            .fact(name)
            .map(Kernel.instType(Map(Classical.TypeVariable -> at), _))
          rule <- rules
            .specAll(scheme, List(guard, left, right))
            .flatMap(rules.mp(_, held))
            .flatMap(rules.genAll(_, List(left, right)))
        } yield found :+ rule
      }
  }

  /**
   * `|- (p \/ F) = p` and `|- (F \/ p) = p`, which nothing in the logic publishes.
   *
   * They are here because of one occurrence in one expansion. [[LessName]] codes `?z. s + S z = t`,
   * so the variable `z` occurs in the code as well as binding it, and the freeness clauses answer
   * about that occurrence before the quantifier's clause takes it back out: what comes out of the
   * rewriting is `(NUM_FREE_TERM i s \/ (z = i)) \/ NUM_FREE_TERM i t` and what a consumer wants
   * names only `s` and `t`. Deciding the guard turns the middle disjunct into `F`, and these two
   * are what remove it. Both are intuitionistic and cost nothing.
   */
  private def disjunctionUnits(logic: Logic): Either[LogicError, Vector[Kernel.Thm]] = {
    val rules = logic.rules
    val proposition: FVar = Term.variable("p", Type.Bool)

    def unit(onRight: Boolean): Either[LogicError, Kernel.Thm] =
      for {
        whole <-
          if (onRight) logic.mkDisj(proposition, logic.falsity)
          else logic.mkDisj(logic.falsity, proposition)
        assumed <- LogicError.lift(Kernel.assume(whole))
        here <- LogicError.lift(Kernel.assume(proposition))
        absurd <- LogicError
          .lift(Kernel.assume(logic.falsity))
          .flatMap(rules.falsityElim(proposition, _))
        forwards <-
          if (onRight) rules.disjElim(assumed, here, absurd)
          else rules.disjElim(assumed, absurd, here)
        backwards <-
          if (onRight) rules.disjIntro1(logic.falsity, here)
          else rules.disjIntro2(logic.falsity, here)
        general <- rules.gen(proposition, Kernel.deductAntisym(backwards, forwards))
      } yield general

    for {
      right <- unit(true)
      left <- unit(false)
    } yield Vector(right, left)
  }

  /**
   * The twelve clauses: where an index occurs free in each of the six, and what a substitution
   * does to it.
   *
   * Each is proved by rewriting both sides of the published statement with the six defining
   * equations and the nine clauses of the family it extends, and comparing the normal forms. Where
   * they do not meet, the statement's own answer says why: a `COND` in it is a guard the rewriting
   * cannot decide, so the derivation assumes the guard and its negation in turn, rewrites again
   * under each decision, and joins the two branches. Nothing else is tried, and a clause whose
   * sides do not meet with every guard decided is refused carrying the refusal the rewriting gave.
   *
   * **Seven of the twelve need that split and five do not, which is not the division this work was
   * planned around.** The expectation was three, the constants that bind an index. What decides it
   * is not binding but whether the published answer carries a conditional the rewriting has to put
   * somewhere: [[ExistsFree]] binds and needs no split, because the quantifier's own freeness
   * clause already produces the `COND` in the shape the statement publishes; [[ExistsSubstitute]]
   * needs one, because the rewriting produces a negation applied to a conditional and a consumer
   * wants a conditional between two negations, which only a case analysis moves between.
   *
   * The guards are read off the statement rather than passed in beside it. A list of them would be
   * a second place to write down which clauses bind what, and the answer is already in the text
   * that gets published.
   */
  private def connectiveClauses(
    vocabulary: Vocabulary,
    cases: Map[String, Kernel.Thm],
    clauses: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val classical = vocabulary.numbering.peano.naturals.classical

    /** The condition of every `COND` in a term, outermost first, without repetition. */
    def guardsIn(subject: Term): Vector[Term] = subject match {
      case App(App(App(Const(Classical.Conditional, _), condition), left), right) =>
        (condition +: (guardsIn(left) ++ guardsIn(right))).distinct
      case App(left, right) => (guardsIn(left) ++ guardsIn(right)).distinct
      case _ => Vector.empty
    }

    /** `g |- g = T` and `~g |- g = F`: one guard, read both ways, as a rewrite rule each. */
    def decide(guard: Term, holds: Boolean): Either[LogicError, Kernel.Thm] =
      if (holds) LogicError.lift(Kernel.assume(guard)).flatMap(rules.eqTruthIntro)
      else
        for {
          negated <- logic.mkNot(guard)
          apart <- LogicError.lift(Kernel.assume(negated))
          assumed <- LogicError.lift(Kernel.assume(guard))
          toFalsity <- rules.notElim(apart, assumed)
          fromFalsity <- LogicError
            .lift(Kernel.assume(logic.falsity))
            .flatMap(rules.falsityElim(guard, _))
          equated <- Conv.sym(Kernel.deductAntisym(toFalsity, fromFalsity))
        } yield equated

    def clause(base: Vector[Kernel.Thm], name: String): Either[LogicError, Kernel.Thm] = {
      def meet(decisions: Vector[Kernel.Thm], left: Term, right: Term) =
        Rewrite.Rule.all(logic, base ++ decisions).flatMap(Rewrite.prove(_, left, right))

      def split(
        remaining: List[Term],
        decisions: Vector[Kernel.Thm],
        left: Term,
        right: Term
      ): Either[LogicError, Kernel.Thm] =
        meet(decisions, left, right) match {
          case met @ Right(_) => met
          case Left(refusal) =>
            remaining match {
              case Nil => Left(refusal)
              case guard :: rest =>
                for {
                  held <- decide(guard, true)
                  positive <- split(rest, decisions :+ held, left, right)
                  apart <- decide(guard, false)
                  negative <- split(rest, decisions :+ apart, left, right)
                  joined <- classical.cases(guard, positive, negative)
                } yield joined
            }
        }

      for {
        statement <- vocabulary.statement(name)
        stripped <- Logic.stripForall(statement)
        (binders, body) = stripped
        sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
        (left, right) = sides
        proved <- split(guardsIn(right).toList, Vector.empty, left, right)
        general <- rules.genAll(proved, binders.toList)
      } yield general
    }

    val families: Vector[(Vector[String], Vector[String])] = Vector(
      (
        Vector(
          FreeVariable, FreeZero, FreeSuccessor, FreeSum, FreeProduct,
          FormulaFreeEquality, FormulaFreeNegation, FormulaFreeImplication, FormulaFreeUniversal),
        Vector(AndFree, OrFree, ExistsFree, LessFree, AllBelowFree, ExistsBelowFree)),
      (
        Vector(
          SubstituteVariable, SubstituteZero, SubstituteSuccessor, SubstituteSum,
          SubstituteProduct, FormulaSubstituteEquality, FormulaSubstituteNegation,
          FormulaSubstituteImplication, FormulaSubstituteUniversal),
        Vector(
          AndSubstitute, OrSubstitute, ExistsSubstitute, LessSubstitute, AllBelowSubstitute,
          ExistsBelowSubstitute))
    )

    for {
      atCodes <- conditionalRules(logic, classical, vocabulary.numbers)
      atPropositions <- conditionalRules(logic, classical, Type.Bool)
      units <- disjunctionUnits(logic)
      defining <- Vector(
        AndCases, OrCases, ExistsCases, LessCases, AllBelowCases, ExistsBelowCases
      ).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
        for {
          found <- carried
          equation <- cases.get(name).toRight(MissingDefinition(name))
        } yield found :+ equation
      }
      proved <- families.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
        case (carried, (family, names)) =>
          for {
            found <- carried
            held <- family.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
              (gathered, name) =>
                for {
                  taken <- gathered
                  fact <- clauses.get(name).toRight(MissingDefinition(name))
                } yield taken :+ fact
            }
            base = held ++ defining ++ atCodes ++ atPropositions ++ units
            reached <- names.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(found)) {
              (gathered, name) =>
                for {
                  taken <- gathered
                  fact <- clause(base, name)
                } yield taken.updated(name, fact)
            }
          } yield reached
      }
    } yield proved
  }

  /**
   * The four closure introduction rules, out of the freeness clauses they correspond to.
   *
   * Each is the same three moves: unfold [[ClosedCases]] on the goal, freshen an index and prove
   * nothing is free at it, and read the freeness clause backwards. Where the clause answers with a
   * disjunction the two premises are joined by De Morgan, which is the only difference between the
   * unary rules and the binary ones.
   */
  private def closureRules(
    vocabulary: Vocabulary,
    closedCases: Kernel.Thm,
    clauses: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val numbers = vocabulary.numbers
    val classical = vocabulary.numbering.peano.naturals.classical
    val theory = vocabulary.theory

    def negationHead: Either[LogicError, Term] =
      LogicError.lift(theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)))

    /** From `X = Y` and `~Y`, that `~X`. */
    def backAcross(equation: Kernel.Thm, held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        negation <- negationHead
        lifted <- Conv.apTerm(negation, equation)
        reversed <- Conv.sym(lifted)
        result <- LogicError.lift(Kernel.eqMp(reversed, held))
      } yield result

    /** From `NUM_CLOSED s`, that `~(NUM_FREE_TERM k s)` at one index. */
    def nowhereAt(subject: Term, closed: Kernel.Thm, index: Term): Either[LogicError, Kernel.Thm] =
      rules
        .spec(subject, closedCases)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, closed)))
        .flatMap(rules.spec(index, _))

    /** From `!k. ~(NUM_FREE_TERM k s)`, that `NUM_CLOSED s`. */
    def closedFrom(subject: Term, nowhere: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules
        .spec(subject, closedCases)
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, nowhere)))

    def unary(
      name: String, clause: String, built: Term => Either[LogicError, Term]
    ): Either[LogicError, Kernel.Thm] =
      for {
        statement <- vocabulary.statement(name)
        stripped <- Logic.stripForall(statement)
        subject <- stripped._1.headOption.toRight(NotOfForm("a claim about a code", statement))
        parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        closed <- LogicError.lift(Kernel.assume(parts._1))
        whole <- built(subject)
        index = Conv.freshVariable("k", numbers, Term.freeVariables(statement))
        inside <- nowhereAt(subject, closed, index)
        equation <- rules.specAll(clauses(clause), List(index, subject))
        outside <- backAcross(equation, inside)
        everywhere <- rules.gen(index, outside)
        reached <- closedFrom(whole, everywhere)
        discharged <- rules.disch(parts._1, reached).flatMap(rules.gen(subject, _))
      } yield discharged

    def binary(
      name: String, clause: String, built: (Term, Term) => Either[LogicError, Term]
    ): Either[LogicError, Kernel.Thm] =
      for {
        statement <- vocabulary.statement(name)
        stripped <- Logic.stripForall(statement)
        left <- stripped._1.headOption.toRight(NotOfForm("a claim about a code", statement))
        right <- stripped._1.drop(1).headOption
          .toRight(NotOfForm("a claim about two codes", statement))
        first <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        leftClosed <- LogicError.lift(Kernel.assume(first._1))
        second <- logic.destImp(first._2).toRight(NotOfForm("an implication", first._2))
        rightClosed <- LogicError.lift(Kernel.assume(second._1))
        whole <- built(left, right)
        index = Conv.freshVariable("k", numbers, Term.freeVariables(statement))
        leftInside <- nowhereAt(left, leftClosed, index)
        rightInside <- nowhereAt(right, rightClosed, index)
        both <- rules.conjIntro(leftInside, rightInside)
        leftTerm <- logic.destNot(leftInside.conclusion)
          .toRight(NotOfForm("a negation", leftInside.conclusion))
        rightTerm <- logic.destNot(rightInside.conclusion)
          .toRight(NotOfForm("a negation", rightInside.conclusion))
        law <- classical.fact(Classical.DeMorganDisjunction)
        joined <- rules
          .specAll(law, List(leftTerm, rightTerm))
          .flatMap(Conv.sym)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, both)))
        equation <- rules.specAll(clauses(clause), List(index, left, right))
        outside <- backAcross(equation, joined)
        everywhere <- rules.gen(index, outside)
        reached <- closedFrom(whole, everywhere)
        discharged <- rules
          .disch(second._1, reached)
          .flatMap(rules.disch(first._1, _))
          .flatMap(rules.genAll(_, List(left, right)))
      } yield discharged

    for {
      zeroStatement <- vocabulary.statement(ClosedZero)
      zeroSubject <- zeroStatement match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a claim about one code", other))
      }
      index = Conv.freshVariable("k", numbers, Term.freeVariables(zeroStatement))
      atZero <- rules.spec(index, clauses(FreeZero))
      subject <- Term.destEq(atZero.conclusion).map(_._1)
        .toRight(NotOfForm("an equation", atZero.conclusion))
      assumedFree <- LogicError.lift(Kernel.assume(subject))
      toFalsity <- LogicError.lift(Kernel.eqMp(atZero, assumedFree))
      refused <- rules.notIntro(subject, toFalsity)
      everywhere <- rules.gen(index, refused)
      zero <- closedFrom(zeroSubject, everywhere)
      _ <- vocabulary.checked(ClosedZero, zero)

      successor <- unary(ClosedSuccessor, FreeSuccessor, inner =>
        Parser.term(vocabulary.theory, vocabulary.notation, "2", numbers)
          .flatMap(tag => vocabulary.coded(tag, inner)))
      _ <- vocabulary.checked(ClosedSuccessor, successor)

      sum <- binary(ClosedSum, FreeSum, (a, b) =>
        for {
          tag <- Parser.term(vocabulary.theory, vocabulary.notation, "3", numbers)
          paired <- vocabulary.paired(a, b)
          coded <- vocabulary.coded(tag, paired)
        } yield coded)
      _ <- vocabulary.checked(ClosedSum, sum)

      product <- binary(ClosedProduct, FreeProduct, (a, b) =>
        for {
          tag <- Parser.term(vocabulary.theory, vocabulary.notation, "4", numbers)
          paired <- vocabulary.paired(a, b)
          coded <- vocabulary.coded(tag, paired)
        } yield coded)
      _ <- vocabulary.checked(ClosedProduct, product)
    } yield Map(
      ClosedZero -> zero,
      ClosedSuccessor -> successor,
      ClosedSum -> sum,
      ClosedProduct -> product
    )
  }

  /**
   * [[NumeralIsClosed]], by the induction the numeral's own recurrence asks for.
   *
   * Both cases go through [[ClosedCases]] rather than around it: the predicate is unfolded to
   * `!k. ~(NUM_FREE_TERM k t)`, the quantified claim is proved for one freshened index, and the
   * equation is read backwards. That is three lines of plumbing at each end and is why the proof
   * itself is one freeness clause per case.
   *
   * The base is [[FreeZero]], that no index occurs in the code of the object language's zero,
   * carried across [[NumeralAtZero]]. The step is [[FreeSuccessor]], that an index occurs in the
   * code of a successor exactly where it occurs in what the successor is of, carried across
   * [[NumeralAtSuccessor]] and closed by the hypothesis at the same index. Nothing here is about
   * coding, in the way that [[NumeralIsTerm]]'s proof is not: a tower of successors over zero
   * mentions no variable because neither of the two things it is built from does.
   */
  private def everyNumeralIsClosed(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    freeInZero: Kernel.Thm,
    freeInSuccessor: Kernel.Thm,
    closedCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers

    /** The argument of a one-place claim, which is the term whose closure is at stake. */
    def argumentOf(claim: Term): Either[LogicError, Term] = claim match {
      case App(_, argument) => Right(argument)
      case other => Left(NotOfForm("a claim about one term", other))
    }

    /** From `X = F`, that `~X`. */
    def notFromFalsity(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        subject <- Term.destEq(equation.conclusion).map(_._1).toRight(
          NotOfForm("an equation", equation.conclusion))
        assumed <- LogicError.lift(Kernel.assume(subject))
        falsity <- LogicError.lift(Kernel.eqMp(equation, assumed))
        refused <- rules.notIntro(subject, falsity)
      } yield refused

    /** From `X = Y` and `~Y`, that `~X`. */
    def notAcross(equation: Kernel.Thm, held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        negation <- LogicError.lift(
          vocabulary.theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)))
        lifted <- Conv.apTerm(negation, equation)
        reversed <- Conv.sym(lifted)
        result <- LogicError.lift(Kernel.eqMp(reversed, held))
      } yield result

    /** From `!k. ~(NUM_FREE_TERM k t)`, that `NUM_CLOSED t`. */
    def closedFrom(subject: Term, nothingFree: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules
        .spec(subject, closedCases)
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, nothingFree)))

    /** From `NUM_CLOSED t`, that `!k. ~(NUM_FREE_TERM k t)`, which is the hypothesis opened up. */
    def nothingFreeIn(proved: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        subject <- argumentOf(proved.conclusion)
        equation <- rules.spec(subject, closedCases)
        opened <- LogicError.lift(Kernel.eqMp(equation, proved))
      } yield opened

    /** `NUM_FREE_TERM k`, the head an occurrence equation is rewritten under. */
    def occurrenceOf(index: Term): Either[LogicError, Term] =
      LogicError
        .lift(vocabulary.theory.constant(
          FreeName, Type.fun(numbers, Type.fun(numbers, Type.Bool))))
        .flatMap(free => LogicError.lift(Term.app(free, index)))

    for {
      statement <- vocabulary.statement(NumeralIsClosed)
      proved <- driver.proveBy(
        statement,
        goal =>
          for {
            subject <- argumentOf(goal)
            index = Conv.freshVariable("k", numbers, Term.freeVariables(goal))
            head <- occurrenceOf(index)
            carried <- Conv.apTerm(head, atZero)
            clause <- rules.spec(index, freeInZero)
            opened <- Conv.trans(carried, clause)
            nowhere <- notFromFalsity(opened)
            everywhere <- rules.gen(index, nowhere)
            result <- closedFrom(subject, everywhere)
          } yield result,
        step =>
          for {
            subject <- argumentOf(step.goal)
            // The hypothesis is `NUM_CLOSED (NUM_NUMERAL k)`, so its argument is the numeral the
            // successor's clause has to be read at.
            inner <- argumentOf(step.hypothesis.conclusion)
            index = Conv.freshVariable("k", numbers, Term.freeVariables(step.goal))
            head <- occurrenceOf(index)
            recurrence <- rules.spec(step.variable, atSuccessor)
            carried <- Conv.apTerm(head, recurrence)
            clause <- rules.specAll(freeInSuccessor, List(index, inner))
            opened <- Conv.trans(carried, clause)
            assumed <- nothingFreeIn(step.hypothesis)
            held <- rules.spec(index, assumed)
            nowhere <- notAcross(opened, held)
            everywhere <- rules.gen(index, nowhere)
            result <- closedFrom(subject, everywhere)
          } yield result
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(NumeralIsClosed, proved)
    } yield result
  }

  /**
   * [[NumeralInjective]], by an induction the driver cannot run.
   *
   * **`Induct.proveBy` is not usable here and the reason is worth stating**, because the statement
   * looks exactly like the ones it does run. That driver inducts on the **last** leading quantifier
   * and leaves the others free, so the hypothesis it hands back is about the **same** other
   * argument as the goal. What this proof needs at the step is the claim at a **different** one:
   * from `NUM_NUMERAL (SUC j) = NUM_NUMERAL (SUC k)` it gets `NUM_NUMERAL j = NUM_NUMERAL k`, and
   * to finish it wants the hypothesis at `j`, not at the `m` it was given. So the induction is run
   * against `Natural.Induction` directly, over the predicate `\n. !m. ...` with the other argument
   * quantified **inside**.
   *
   * Four leaves. Both zero is the assumption read back and both successors is `NUM_CODE_INJECTIVE`
   * peeling one layer; the two mixed leaves are the tags `1` and `2` disagreeing, which is the
   * second thing in this file resting on two numerals of `num` differing.
   */
  private def numeralsAreDistinct(
    vocabulary: Vocabulary,
    successor: Successor,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val subject = Term.variable("m", numbers)
    val bound = Term.variable("n", numbers)

    def numeral(text: String): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, text, numbers)

    def numeralAt(argument: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(vocabulary.numeral, argument))

    /** `!m. NUM_NUMERAL m = NUM_NUMERAL at ==> m = at`, the claim being inducted over. */
    def claimAt(at: Term): Either[LogicError, Term] =
      for {
        left <- numeralAt(subject)
        right <- numeralAt(at)
        premise <- LogicError.lift(Term.eq(left, right))
        conclusion <- LogicError.lift(Term.eq(subject, at))
        body <- logic.mkImp(premise, conclusion)
        result <- logic.mkForall(subject, body)
      } yield result

    /** `NUM_NUMERAL m = NUM_CODE t p`, given what `m` is, which is the two recurrences applied. */
    def asCode(shape: Kernel.Thm, at: Option[Term]): Either[LogicError, Kernel.Thm] =
      for {
        stepped <- Conv.apTerm(vocabulary.numeral, shape)
        recurrence <- at.fold(Right(atZero): Either[LogicError, Kernel.Thm])(
          argument => rules.spec(argument, atSuccessor)
        )
        result <- Conv.trans(stepped, recurrence)
      } yield result

    /** `F` where the two sides are codes with different tags. */
    def tagsDisagree(
      left: Kernel.Thm,
      right: Kernel.Thm,
      equal: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        asCodes <- Conv.sym(left).flatMap(Conv.trans(_, equal)).flatMap(Conv.trans(_, right))
        sides <- Term
          .destEq(asCodes.conclusion)
          .toRight(NotOfForm("an equation", asCodes.conclusion))
        parts <- (sides._1, sides._2) match {
          case (App(App(_, leftTag), leftPayload), App(App(_, rightTag), rightPayload)) =>
            Right((leftTag, leftPayload, rightTag, rightPayload))
          case _ => Left(NotOfForm("two codes", asCodes.conclusion))
        }
        recovered <- vocabulary.numbering
          .fact(Numbering.CodeInjective)
          .flatMap(rules.specAll(_, List(parts._1, parts._2, parts._3, parts._4)))
          .flatMap(rules.mp(_, asCodes))
        pinned <- rules.conjElim1(recovered)
        never <- successor.distinct(parts._1, parts._3)
        result <- rules.notElim(never, pinned)
      } yield result

    /**
     * One leaf of the induction, over the two shapes `m` can have.
     *
     * `hypothesis` is present at the step and absent at the base, and that is the only difference
     * between the two: at the base the successor leaf is refuted by the tags, and at the step the
     * successor leaf peels a layer and asks the hypothesis.
     */
    def leaf(at: Term, right: Kernel.Thm, hypothesis: Option[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        claim <- claimAt(at)
        stripped <- Logic.stripForall(claim)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every number", claim))
        parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        (premise, conclusion) = parts
        assumed <- LogicError.lift(Kernel.assume(premise))

        cases <- vocabulary.numbering.peano.naturals
          .fact(Natural.ZeroOrSuccessor)
          .flatMap(rules.spec(index, _))
        split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
        (isZero, hasPredecessor) = split

        fromZero <- for {
          shape <- LogicError.lift(Kernel.assume(isZero))
          settled <-
            if (hypothesis.isEmpty) Right(shape)
            else
              for {
                left <- asCode(shape, None)
                absurd <- tagsDisagree(left, right, assumed)
                anything <- rules.falsityElim(conclusion, absurd)
              } yield anything
        } yield settled

        fromSuccessor <- withPredecessor(vocabulary, hasPredecessor, Set(index)) {
          (predecessor, shape) =>
            for {
              left <- asCode(shape, Some(predecessor))
              settled <- hypothesis match {
                case None =>
                  for {
                    absurd <- tagsDisagree(left, right, assumed)
                    anything <- rules.falsityElim(conclusion, absurd)
                  } yield anything
                case Some(inductive) =>
                  for {
                    asCodes <- Conv
                      .sym(left)
                      .flatMap(Conv.trans(_, assumed))
                      .flatMap(Conv.trans(_, right))
                    sides <- Term
                      .destEq(asCodes.conclusion)
                      .toRight(NotOfForm("an equation", asCodes.conclusion))
                    parts <- (sides._1, sides._2) match {
                      case (App(App(_, lt), lp), App(App(_, rt), rp)) => Right((lt, lp, rt, rp))
                      case _ => Left(NotOfForm("two codes", asCodes.conclusion))
                    }
                    recovered <- vocabulary.numbering
                      .fact(Numbering.CodeInjective)
                      .flatMap(rules.specAll(_, List(parts._1, parts._2, parts._3, parts._4)))
                      .flatMap(rules.mp(_, asCodes))
                    payloads <- rules.conjElim2(recovered)
                    shorter <- rules.spec(predecessor, inductive).flatMap(rules.mp(_, payloads))
                    lifted <- Conv.apTerm(vocabulary.successor, shorter)
                    result <- Conv.trans(shape, lifted)
                  } yield result
              }
            } yield settled
        }

        settled <- rules.disjElim(cases, fromZero, fromSuccessor)
        _ <-
          if (settled.conclusion == conclusion) Right(())
          else Left(NotOfForm("what the leaf has to reach", settled.conclusion))
        result <- rules.disch(premise, settled).flatMap(rules.gen(index, _))
      } yield result

    for {
      zeroTerm <- numeral("0")
      predicate <- claimAt(bound).flatMap(body => LogicError.lift(Term.abs(bound, body)))
      induction <- vocabulary.numbering.peano.naturals.fact(Natural.Induction)
      instance <- rules.spec(predicate, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      base <- leaf(vocabulary.zero, atZero, None)
      _ <-
        if (base.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the base the induction asks for", base.conclusion))

      stepStripped <- Logic.stripForall(stepTerm)
      variable <- stepStripped._1.headOption
        .toRight(NotOfForm("a claim about every number", stepTerm))
      stepParts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      assumedStep <- LogicError.lift(Kernel.assume(stepParts._1))
      lifted <- LogicError.lift(Term.app(vocabulary.successor, variable))
      atLifted <- rules.spec(variable, atSuccessor)
      step <- leaf(lifted, atLifted, Some(assumedStep))
      _ <-
        if (step.conclusion == stepParts._2) Right(())
        else Left(NotOfForm("the step the induction asks for", step.conclusion))
      generalStep <- rules.disch(stepParts._1, step).flatMap(rules.gen(variable, _))

      everywhere <- rules.conjIntro(base, generalStep).flatMap(rules.mp(opened, _))
      instantiated <- rules.spec(bound, everywhere).flatMap(rules.spec(subject, _))
      general <- rules.genAll(instantiated, List(subject, bound))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", general.conclusion))
      result <- vocabulary.checked(NumeralInjective, general)
      _ = zeroTerm
    } yield result
  }

  /** Open `?k. n = SUC k` and hand the predecessor and the equation to the caller. */
  private def withPredecessor(
    vocabulary: Vocabulary,
    existential: Term,
    taken: Set[FVar]
  )(
    reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(existential))
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      variable = Conv.freshVariable(
        "k",
        vocabulary.numbers,
        taken ++ Term.freeVariables(existential)
      )
      applied <- LogicError.lift(Term.app(predicate, variable))
      contraction <- Conv.betaRoot(applied)
      body <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      instance <- LogicError.lift(Kernel.assume(body))
      reached <- reach(variable, instance)
      result <- rules.existsElim(assumed, variable, reached)
    } yield result
  }

  /* --------------------------------------------------------------------- the substitution */

  /**
   * A recursion over codes with parameters, which is [[definePredicate]] with two things added.
   *
   * The step has its parameters free, so what `Descent` produces is a function **for each** tuple
   * of them; abstracting them after the choice is what turns it into a constant, and it is the
   * arrangement `Recursion.define` already uses for the sequence of `NUM_PROD`.
   *
   * `answers` is what the recursion returns and is the second. The substitutions answer with a
   * code, so theirs is `num`; freeness answers with a proposition, so its is `bool`. Nothing in the
   * construction or in [[shapedIsAdmissible]] below reads that type except to take `COND` at it:
   * the guards are equations about `s` either way, and the bound a guard gives is a bound on `s`
   * rather than on what the branch produces. Written once because the alternative is two hundred
   * lines differing in `numbers` against `Type.Bool`, which go stale in one direction.
   */
  private[theories] def defineShaped(
    numbering: Numbering,
    recursion: Kernel.Thm,
    base: Theory,
    notation: Notation,
    logic: Logic,
    name: String,
    stepText: String,
    answers: Type,
    parameters: List[FVar]
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] = {
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      step <- Parser.term(base, notation, stepText)
      atAnswers = Kernel.instType(Map(Classical.TypeVariable -> answers), recursion)
      instance <- logic.rules.spec(step, atAnswers)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      parts <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))

      condition <- shapedIsAdmissible(numbering, logic, parts._1, answers)
      exists <- logic.rules.mp(opened, condition)

      chosen <- numbering.peano.naturals.classical.witness(exists)
      selected <- chosen.conclusion match {
        case App(_, term) => Right(term)
        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }
      body <- LogicError.lift(Term.absAll(parameters, selected))
      defined <- LogicError.lift(Kernel.defineConstant(base, name, body))
      (theory, definition) = defined
      wider <- logic.over(theory)

      // The name goes in by CONGRUENCE and not by rewriting, which is the difference between a
      // parameterised recursion and a closed one. `definePredicate` above rewrites with the
      // definition read backwards and is safe because `NUM_TERM = select ...` is CLOSED. Here the
      // chosen term has `i` and `t` free, a rewrite rule makes its free variables matchable, and
      // the first attempt unified `i` with the recursion's own index: what came out was
      // `NUM_SUBST_TERM i t i = ...`, which is a theorem and is not the one intended.
      //
      // Against the UNREDUCED `P (select P)` there is exactly one occurrence of the chosen term, as
      // the argument, so one `Conv.apTerm` puts the name there and nothing else can move.
      predicate <- logic
        .destExistsPredicate(exists.conclusion)
        .toRight(NotOfForm("an existential", exists.conclusion))
      unfolded <- Conv.unfold(definition, parameters)
      opened <- Conv
        .sym(unfolded)
        .flatMap(equation => Conv.apTerm(predicate, equation))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))
        )

      // What the recursion gives is quantified over its own index alone, with the two parameters
      // FREE. They are generalised here so that the caller sees `!i t s.` and can specialise all
      // three; without it the first thing a caller does is specialise the index at the parameter,
      // and what comes back is a theorem about `NUM_SUBST_TERM i t i`.
      named <- logic.rules.genAll(opened, parameters)
      _ = wider
    } yield (theory, definition, named)
  }

  /**
   * The substitution's step gives the same answer to two functions agreeing below the index.
   *
   * The same obligation the syntactic predicates carry and a different proof, because what is being
   * compared is an equality of **numbers** rather than of propositions. The two sides are one nest
   * of conditionals with the same guards, so the proof splits on each guard in turn: where it holds
   * both sides reduce to their own branch and the two branches differ only by the function, and
   * where it fails both drop to the next.
   *
   * Every recursive call sits under a guard that says what shape `s` has, and the bound comes from
   * that shape rather than from a tag. That is the whole reason the guards are written as equations.
   */
  private[theories] def shapedIsAdmissible(
    numbering: Numbering,
    logic: Logic,
    admissible: Term,
    answers: Type
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val classical = numbering.peano.naturals.classical

    for {
      conditional <- LogicError.lift(
        numbering.theory.constant(
          Classical.Conditional,
          Type.fun(Type.Bool, Type.fun(answers, Type.fun(answers, answers)))
        )
      )
      below <- LogicError.lift(
        numbering.theory.constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      condTrue <- classical
        .fact(Classical.CondTrue)
        .map(Kernel.instType(Map(Classical.TypeVariable -> answers), _))
      condFalse <- classical
        .fact(Classical.CondFalse)
        .map(Kernel.instType(Map(Classical.TypeVariable -> answers), _))
      middle <- classical.fact(Classical.ExcludedMiddle)
      codeRight <- numbering.fact(Numbering.CodeRight)
      pairLeft <- numbering.fact(Numbering.PairLeft)
      pairRight <- numbering.fact(Numbering.PairRight)
      mixed <- numbering.peano.fact(Peano.AtMostThenBelow)

      stripped <- Logic.stripForall(admissible)
      left <- stripped._1.headOption.toRight(NotOfForm("a claim about a function", admissible))
      right <- stripped._1.drop(1).headOption
        .toRight(NotOfForm("a claim about two functions", admissible))
      subject <- stripped._1.drop(2).headOption
        .toRight(NotOfForm("a claim about an index", admissible))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (agreementTerm, equationTerm) = body
      agreement <- LogicError.lift(Kernel.assume(agreementTerm))
      sides <- Term.destEq(equationTerm).toRight(NotOfForm("an equation", equationTerm))

      proof <- {
        def destCond(term: Term): Option[(Term, Term, Term)] = term match {
          case App(App(App(head, guard), yes), no) if head == conditional => Some((guard, yes, no))
          case _ => None
        }

        /** `x < s`, read off a guard that says what shape `s` has. */
        def boundOf(argument: Term, guard: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            shape <- Term
              .destEq(guard.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", guard.conclusion))
            coded <- shape match {
              case App(App(_, tag), payload) => Right((tag, payload))
              case other => Left(NotOfForm("a code", other))
            }
            headed <- LogicError.lift(Term.app(below, coded._2))
            raw <- rules.specAll(codeRight, List(coded._1, coded._2))
            payloadBelow <- Conv
              .sym(guard)
              .flatMap(equation => Conv.apTerm(headed, equation))
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, raw)))
            result <-
              if (argument == coded._2) Right(payloadBelow)
              else
                coded._2 match {
                  case App(App(_, first), second) =>
                    val which = if (argument == first) pairLeft else pairRight
                    for {
                      inPair <- rules.specAll(which, List(first, second))
                      pieces <- rules.conjIntro(inPair, payloadBelow)
                      settled <- rules
                        .specAll(mixed, List(argument, coded._2, subject))
                        .flatMap(rules.mp(_, pieces))
                    } yield settled
                  case other => Left(NotOfForm("a pair", other))
                }
          } yield result

        /** Two branches that differ only by the function, related argument by argument. */
        def congruent(a: Term, b: Term, guard: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          if (a == b) Right(Conv.refl(a))
          else
            (a, b) match {
              case (App(f, x), App(g, y)) if f == left && g == right && x == y =>
                boundOf(x, guard).flatMap(bound =>
                  rules.spec(x, agreement).flatMap(rules.mp(_, bound))
                )
              case (App(f, x), App(g, y)) =>
                for {
                  overFunction <- congruent(f, g, guard).flatMap(Conv.apThm(_, x))
                  overArgument <- congruent(x, y, guard).flatMap(Conv.apTerm(g, _))
                  result <- Conv.trans(overFunction, overArgument)
                } yield result
              // Under a binder, which `Truth`'s step has and no step in this file does: the truth
              // of a formula is a function of the environment, so its branches are abstractions
              // over it, and the quantifier's branch applies the recursion under `!n.`. The
              // variable opened here is fresh against both sides and against every assumption,
              // which is the side condition `Kernel.abs` checks: the agreement and the guard
              // mention the functions and the index and nothing bound inside a branch.
              case (Abs(ta, _), Abs(tb, _)) if ta == tb =>
                val taken = Term.freeVariables(a) ++ Term.freeVariables(b) ++
                  (agreement.hypotheses ++ guard.hypotheses ++
                    List(agreement.conclusion, guard.conclusion)).flatMap(Term.freeVariables)
                val opened = Conv.freshVariable("v", ta, taken)
                for {
                  one <- LogicError.lift(Term.app(a, opened))
                  other <- LogicError.lift(Term.app(b, opened))
                  inside <- (Term.betaReduce(one), Term.betaReduce(other)) match {
                    case (Some(x), Some(y)) => congruent(x, y, guard)
                    case _ => Left(NotOfForm("an abstraction that opens", a))
                  }
                  closed <- LogicError.lift(Kernel.abs(opened, inside))
                } yield closed
              case _ => Left(NotOfForm(s"two branches that differ only by the function", a))
            }

        /** The two nests of conditionals, compared one guard at a time. */
        def matching(one: Term, other: Term): Either[LogicError, Kernel.Thm] =
          (destCond(one), destCond(other)) match {
            case (Some((guard, yes, no)), Some((second, otherYes, otherNo))) if guard == second =>
              for {
                cases <- rules.spec(guard, middle)
                whenTrue <- for {
                  held <- LogicError.lift(Kernel.assume(guard))
                  first <- rules.specAll(condTrue, List(guard, yes, no)).flatMap(rules.mp(_, held))
                  next <- rules
                    .specAll(condTrue, List(guard, otherYes, otherNo))
                    .flatMap(rules.mp(_, held))
                  inner <- congruent(yes, otherYes, held)
                  reversed <- Conv.sym(next)
                  result <- Conv.trans(first, inner).flatMap(Conv.trans(_, reversed))
                } yield result
                whenFalse <- for {
                  denied <- logic.mkNot(guard).flatMap(term => LogicError.lift(Kernel.assume(term)))
                  first <- rules.specAll(condFalse, List(guard, yes, no)).flatMap(rules.mp(_, denied))
                  next <- rules
                    .specAll(condFalse, List(guard, otherYes, otherNo))
                    .flatMap(rules.mp(_, denied))
                  inner <- matching(no, otherNo)
                  reversed <- Conv.sym(next)
                  result <- Conv.trans(first, inner).flatMap(Conv.trans(_, reversed))
                } yield result
                settled <- rules.disjElim(cases, whenTrue, whenFalse)
              } yield settled
            case _ =>
              if (one == other) Right(Conv.refl(one))
              else Left(NotOfForm("two nests of conditionals with the same guards", one))
          }

        matching(sides._1, sides._2)
      }

      discharged <- rules.disch(agreementTerm, proof)
      general <- rules.genAll(discharged, List(left, right, subject))
      _ <-
        if (general.conclusion == admissible) Right(())
        else Left(NotOfForm("the condition as the recursion states it", general.conclusion))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a condition with nothing assumed", general.conclusion))
    } yield general
  }

  /**
   * One tag of the substitution, unfolded until the conditionals are gone.
   *
   * The recursion equation is a nest of four conditionals and is not what a caller wants; what a
   * caller wants is what the substitution does to a code of a given shape. Both are the same
   * theorem and the work between them is deciding four guards.
   *
   * **The projections are removed first, by rewriting rather than by congruence.** After
   * `NUM_PAYLOAD (NUM_CODE k p)` becomes `p` and `NUM_FST (NUM_PAIR a b)` becomes `a`, every guard
   * reads `NUM_CODE j p = NUM_CODE k p` and is decided by comparing two numerals: equal tags make
   * it a reflexivity, different ones make `NUM_CODE_INJECTIVE` and `Successor.distinct` refuse it.
   * That is the third thing in this development resting on two numerals of `num` differing.
   */
  private def shapedAt(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    projections: Vector[Rewrite.Rule],
    successor: Successor,
    statement: String,
    answers: Type,
    parameters: List[FVar]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers

    def numeral(text: String): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, text, numbers)

    def single(name: String): FVar = Term.variable(name, numbers)

    // `None` is a payload that is the literal zero rather than a variable, which is the clause for
    // the object language's zero in both recursions. It used to be a variable named "unused" here
    // and a second table below that turned it back into a numeral by matching on the statement's
    // name; a clause added without an entry in that second table then built a theorem about a free
    // variable called `unused` and was refused pages later, by the published statement.
    val shape: Either[LogicError, (String, Option[Either[FVar, (FVar, FVar)]], List[FVar])] =
      statement match {
        case SubstituteVariable =>
          val j = single("j")
          Right(("0", Some(Left(j)), List(j)))
        case SubstituteZero => Right(("1", None, Nil))
        case SubstituteSuccessor =>
          val inner = single("s")
          Right(("2", Some(Left(inner)), List(inner)))
        case SubstituteSum | SubstituteProduct =>
          val a = single("a")
          val b = single("b")
          Right((if (statement == SubstituteSum) "3" else "4", Some(Right((a, b))), List(a, b)))

        case FormulaSubstituteEquality =>
          val a = single("a")
          val b = single("b")
          Right(("5", Some(Right((a, b))), List(a, b)))
        case FormulaSubstituteNegation =>
          val inner = single("p")
          Right(("6", Some(Left(inner)), List(inner)))
        case FormulaSubstituteImplication =>
          val a = single("p")
          val b = single("q")
          Right(("7", Some(Right((a, b))), List(a, b)))
        case FormulaSubstituteUniversal =>
          val a = single("j")
          val b = single("p")
          Right(("8", Some(Right((a, b))), List(a, b)))

        case FreeVariable =>
          val j = single("j")
          Right(("0", Some(Left(j)), List(j)))
        case FreeZero => Right(("1", None, Nil))
        case FreeSuccessor =>
          val inner = single("s")
          Right(("2", Some(Left(inner)), List(inner)))
        case FreeSum | FreeProduct =>
          val a = single("a")
          val b = single("b")
          Right((if (statement == FreeSum) "3" else "4", Some(Right((a, b))), List(a, b)))

        case FormulaFreeEquality =>
          val a = single("a")
          val b = single("b")
          Right(("5", Some(Right((a, b))), List(a, b)))
        case FormulaFreeNegation =>
          val inner = single("p")
          Right(("6", Some(Left(inner)), List(inner)))
        case FormulaFreeImplication =>
          val a = single("p")
          val b = single("q")
          Right(("7", Some(Right((a, b))), List(a, b)))
        case FormulaFreeUniversal =>
          val a = single("j")
          val b = single("p")
          Right(("8", Some(Right((a, b))), List(a, b)))

        case other => Left(MissingDefinition(other))
      }

    for {
      parts <- shape
      (tagText, payloadShape, extra) = parts
      tag <- numeral(tagText)
      payload <- payloadShape match {
        case None => numeral("0")
        case Some(Left(single)) => Right(single: Term)
        case Some(Right((a, b))) => vocabulary.paired(a, b)
      }
      coded <- vocabulary.coded(tag, payload)
      instance <- rules.specAll(cases, parameters.map(variable => variable: Term) :+ coded)
      cleaned <- Rewrite.inTheorem(projections, instance)

      settled <- settleGuards(vocabulary.numbering, vocabulary.logic, successor, answers, cleaned)
      general <- rules.genAll(settled, parameters ++ extra)
      result <- vocabulary.checked(statement, general)
    } yield result
  }

  /**
   * A recursion equation over a code of a given shape, with the nest of shape tests taken off.
   *
   * What `shapedAt` does once the projections are gone, and what `Truth` does to its own two
   * recursions, so it is written once. Every guard in these nests is an equation between two codes,
   * so each is either a reflexivity or refuted by the tags differing. A conditional whose guard is
   * neither is part of the ANSWER rather than of the shape test and is left standing.
   */
  private[theories] def settleGuards(
    numbering: Numbering,
    logic: Logic,
    successor: Successor,
    answers: Type,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val classical = numbering.peano.naturals.classical

    /**
     * Decide one guard, or say it is not one.
     *
     * `None` means the conditional is part of the **answer** rather than part of the shape test,
     * which is the variable clause's `COND (j = i) t (NUM_CODE 0 j)`: whether the index matches is
     * not something settled here, and the published statement carries it. Without that stop
     * the walk descends into it and asks two indices to be codes.
     */
    def decide(guard: Term): Either[LogicError, Option[Either[Kernel.Thm, Kernel.Thm]]] =
      Term.destEq(guard) match {
        case Some((one, other)) if one == other => Right(Some(Left(Conv.refl(one))))
        case Some((App(App(_, leftTag), leftPayload), App(App(_, rightTag), rightPayload))) =>
          for {
            assumed <- LogicError.lift(Kernel.assume(guard))
            recovered <- numbering
              .fact(Numbering.CodeInjective)
              .flatMap(rules.specAll(_, List(leftTag, leftPayload, rightTag, rightPayload)))
              .flatMap(rules.mp(_, assumed))
            pinned <- rules.conjElim1(recovered)
            never <- successor.distinct(leftTag, rightTag)
            contradiction <- rules.notElim(never, pinned)
            refuted <- rules.notIntro(guard, contradiction)
          } yield Some(Right(refuted))
        case _ => Right(None)
      }

    /** Walk the nest, taking the branch each guard selects, until no conditional is left. */
    def reduced(equation: Kernel.Thm, conditional: Term, trueRule: Kernel.Thm, falseRule: Kernel.Thm)
      : Either[LogicError, Kernel.Thm] = {
      val right = Term.destEq(equation.conclusion).map(_._2)
      right match {
        case Some(App(App(App(head, guard), yes), no)) if head == conditional =>
          for {
            decided <- decide(guard)
            result <- decided match {
              case None => Right(equation)
              case Some(outcome) =>
                for {
                  stepped <- outcome match {
                    case Left(held) =>
                      rules.specAll(trueRule, List(guard, yes, no)).flatMap(rules.mp(_, held))
                    case Right(denied) =>
                      rules.specAll(falseRule, List(guard, yes, no)).flatMap(rules.mp(_, denied))
                  }
                  moved <- Conv.trans(equation, stepped)
                  settled <- reduced(moved, conditional, trueRule, falseRule)
                } yield settled
            }
          } yield result
        case _ => Right(equation)
      }
    }

    for {
      conditional <- LogicError.lift(
        numbering.theory.constant(
          Classical.Conditional,
          Type.fun(Type.Bool, Type.fun(answers, Type.fun(answers, answers)))
        )
      )
      trueRule <- classical
        .fact(Classical.CondTrue)
        .map(Kernel.instType(Map(Classical.TypeVariable -> answers), _))
      falseRule <- classical
        .fact(Classical.CondFalse)
        .map(Kernel.instType(Map(Classical.TypeVariable -> answers), _))
      settled <- reduced(equation, conditional, trueRule, falseRule)
    } yield settled
  }

  /* ----------------------------------------------- substitution keeps what it is given */

  /**
   * [[SubstituteKeepsTerms]], by course-of-values induction on the code.
   *
   * Four cases, one per clause of `NUM_TERM_CASES`, and each is the same four moves: read the tag
   * off, put the code into the literal form the substitution's equation is stated at, read what the
   * substitution gives there, and show that is a term. Only the two recursive clauses touch the
   * induction hypothesis, and each of them first has to show the sub-code is **below** the code,
   * which is the constructor's bound and, under a pair, the pairing's as well.
   */
  private def keepsWellFormed(
    vocabulary: Vocabulary,
    statementName: String,
    predicate: Option[Term],
    substitute: Term,
    strong: Kernel.Thm,
    termCases: Kernel.Thm,
    clauseAt: (Site, Int) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val classical = vocabulary.numbering.peano.naturals.classical

    for {
      statement <- vocabulary.statement(statementName)
      stripped <- Logic.stripForall(statement)

      // The statement's OWN three variables, because `Logic.stripForall` freshens: building the
      // predicate over a variable named `i` here and a statement that binds `x` there produces a
      // theorem about the wrong thing, and the refusal arrives at the first `mp`.
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", statement))
      replacement <- stripped._1.drop(1).headOption
        .toRight(NotOfForm("a claim about every replacement", statement))
      subject <- stripped._1.drop(2).headOption
        .toRight(NotOfForm("a claim about every code", statement))

      body <- LogicError.lift(Term.abs(subject, stripped._2))
      instance <- rules.spec(body, strong)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))

      step <- {
        for {
          stepStripped <- Logic.stripForall(premises._1)
          code <- stepStripped._1.headOption
            .toRight(NotOfForm("a claim about every code", premises._1))
          parts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
          smaller <- LogicError.lift(Kernel.assume(parts._1))
          inner <- logic.destImp(parts._2).toRight(NotOfForm("an implication", parts._2))
          isTerm <- LogicError.lift(Kernel.assume(inner._1))
          tail <- logic.destImp(inner._2).toRight(NotOfForm("an implication", inner._2))
          sideCondition <- LogicError.lift(Kernel.assume(tail._1))
          goal = tail._2

          opening <- rules.spec(code, termCases).flatMap(equation =>
            LogicError.lift(Kernel.eqMp(equation, isTerm))
          )

          settled <- withWitnesses(vocabulary, opening, Set(index, replacement, code)) {
            (tag, payload, atPayload) =>
              for {
                isCode <- rules.conjElim1(atPayload)
                disjunction <- rules.conjElim2(atPayload)

                parts <- vocabulary.disjuncts(disjunction.conclusion)
                site = Site(
                  vocabulary, predicate, substitute, code, tag, payload, index, replacement,
                  isCode, isTerm, sideCondition, smaller, parts)
                atVariable <- clauseAt(site, 0)
                atZero <- clauseAt(site, 1)
                atSuccessor <- clauseAt(site, 2)
                atBinary <- clauseAt(site, 3)

                tailTerm <- logic.mkDisj(parts(2), parts(3))
                restTerm <- logic.mkDisj(parts(1), tailTerm)
                assumedTail <- LogicError.lift(Kernel.assume(tailTerm))
                assumedRest <- LogicError.lift(Kernel.assume(restTerm))
                insideTail <- rules.disjElim(assumedTail, atSuccessor, atBinary)
                insideRest <- rules.disjElim(assumedRest, atZero, insideTail)
                reached <- rules.disjElim(disjunction, atVariable, insideRest)
                _ <-
                  if (reached.conclusion == goal) Right(())
                  else Left(NotOfForm("what the case has to reach", reached.conclusion))
              } yield reached
          }

          discharged <- rules
            .disch(tail._1, settled)
            .flatMap(rules.disch(inner._1, _))
            .flatMap(rules.disch(parts._1, _))
            .flatMap(rules.gen(code, _))
        } yield discharged
      }

      everywhere <- rules.mp(opened, step)
      general <- rules.genAll(everywhere, List(index, replacement))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", general.conclusion))
      result <- vocabulary.checked(statementName, general)
    } yield result
  }

  /** Open `?x. ?y. body` with two fresh names and hand both to the caller. */
  private def withWitnesses(
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    avoid: Set[FVar]
  )(
    reach: (FVar, FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def open(theorem: Kernel.Thm, name: String, taken: Set[FVar]) =
      for {
        predicate <- logic
          .destExistsPredicate(theorem.conclusion)
          .toRight(NotOfForm("an existential", theorem.conclusion))
        variable = Conv.freshVariable(
          name,
          vocabulary.numbers,
          taken ++ Term.freeVariables(theorem.conclusion)
        )
        applied <- LogicError.lift(Term.app(predicate, variable))
        contraction <- Conv.betaRoot(applied)
        instance <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        assumed <- LogicError.lift(Kernel.assume(instance))
      } yield (variable, assumed)

    for {
      outer <- open(existential, "k", avoid)
      inner <- open(outer._2, "p", avoid + outer._1)
      reached <- reach(outer._1, inner._1, inner._2)
      closedInner <- rules.existsElim(outer._2, inner._1, reached)
      result <- rules.existsElim(existential, outer._1, closedInner)
    } yield result
  }

  /**
   * Everything one clause of a well-formedness induction is handed, gathered once.
   *
   * The scaffolding either proof runs is identical: strong induction over the code, the `_CASES`
   * equation opened at two witnesses, four disjuncts, and the same four moves inside each. What
   * differs is only what the four clauses DO, so the scaffolding is written once and the clauses
   * are a function of this.
   *
   * The four moves are the methods below. Read the tag off and put the code into the literal form
   * the substitution's equation is stated at ([[atLiteral]]); read what the substitution gives
   * there ([[valueAt]]); show the sub-code is below the code ([[belowCode]]) and ask the induction
   * hypothesis ([[inductive]]); and carry the answer back to the goal ([[carried]]).
   */
  private final case class Site(
    vocabulary: Vocabulary,
    predicate: Option[Term],
    substitute: Term,
    code: FVar,
    tag: FVar,
    payload: FVar,
    index: Term,
    replacement: Term,
    isCode: Kernel.Thm,
    subjectIsWellFormed: Kernel.Thm,
    sideCondition: Kernel.Thm,
    smaller: Kernel.Thm,
    parts: Vector[Term]
  ) {

    val rules: Rules = vocabulary.rules
    val logic: Logic = vocabulary.logic
    val classical: Classical = vocabulary.numbering.peano.naturals.classical

    /** `NUM_SUBST_... i t x`, as a term. */
    def substituted(argument: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(substitute, List(index, replacement, argument)))

    /**
     * The head of the claim, where the claim has one.
     *
     * A clause set proving that a predicate survives the substitution needs it; one proving an
     * **equation** about the substitution has no predicate at all, and calls [[itself]] instead.
     * That is why it is optional rather than a term every caller must invent.
     */
    def claimHead: Either[LogicError, Term] =
      predicate.toRight(NotOfForm("a claim with a predicate at its head", code))

    /** The claim being proved, at a term. */
    def wellFormed(argument: Term): Either[LogicError, Term] =
      claimHead.flatMap(head => LogicError.lift(Term.app(head, argument)))

    /** `x < code`, from the shape the case gives. */
    def belowCode(argument: Term, shape: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        coded <- Term
          .destEq(shape.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", shape.conclusion))
        pieces <- coded match {
          case App(App(_, literal), inside) => Right((literal, inside))
          case other => Left(NotOfForm("a code", other))
        }
        headed <- LogicError.lift(Term.app(vocabulary.below, pieces._2))
        raw <- vocabulary.numbering
          .fact(Numbering.CodeRight)
          .flatMap(rules.specAll(_, List(pieces._1, pieces._2)))
        payloadBelow <- Conv
          .sym(shape)
          .flatMap(equation => Conv.apTerm(headed, equation))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, raw)))
        result <-
          if (argument == pieces._2) Right(payloadBelow)
          else
            pieces._2 match {
              case App(App(_, first), second) =>
                val which = if (argument == first) Numbering.PairLeft else Numbering.PairRight
                for {
                  inPair <- vocabulary.numbering
                    .fact(which)
                    .flatMap(rules.specAll(_, List(first, second)))
                  joined <- rules.conjIntro(inPair, payloadBelow)
                  reached <- vocabulary.numbering.peano
                    .fact(Peano.AtMostThenBelow)
                    .flatMap(rules.specAll(_, List(argument, pieces._2, code)))
                    .flatMap(rules.mp(_, joined))
                } yield reached
              case other => Left(NotOfForm("a pair", other))
            }
      } yield result

    /** The induction hypothesis at a sub-code, with both premises discharged. */
    def inductive(
      argument: Term,
      shape: Kernel.Thm,
      argumentIsWellFormed: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      inductiveWith(argument, shape, argumentIsWellFormed, sideCondition)

    /**
     * The same, where the hypothesis's second premise is about the sub-code rather than the code.
     *
     * [[inductive]] hands it [[sideCondition]] unchanged, which is right where that condition is
     * about the **replacement**: `NUM_TERM t` says nothing about which code is being walked. It is
     * wrong where the condition is about the **subject**, as a freeness condition is: what the
     * hypothesis wants at a sub-code is that the index is not free in THAT, and the caller is the
     * only one that can produce it, one freeness clause at a time.
     */
    def inductiveWith(
      argument: Term,
      shape: Kernel.Thm,
      argumentIsWellFormed: Kernel.Thm,
      second: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        bound <- belowCode(argument, shape)
        here <- rules.spec(argument, smaller).flatMap(rules.mp(_, bound))
        result <- rules.mp(here, argumentIsWellFormed).flatMap(rules.mp(_, second))
      } yield result

    /** `NUM_FREE_TERM i`, the head a freeness clause is read under. */
    def freeHead: Either[LogicError, Term] =
      LogicError
        .lift(vocabulary.theory.constant(
          FreeName, Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, Type.Bool))))
        .flatMap(free => LogicError.lift(Term.app(free, index)))

    /** From `X = Y` and `~X`, that `~Y`. */
    def forwardNot(equation: Kernel.Thm, held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        negation <- LogicError.lift(
          vocabulary.theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)))
        lifted <- Conv.apTerm(negation, equation)
        result <- LogicError.lift(Kernel.eqMp(lifted, held))
      } yield result

    /**
     * What the code's freeness condition says about the inside of this shape.
     *
     * [[sideCondition]] is `~(NUM_FREE_TERM i code)`; the shape says what the code is, and the
     * clause says what freeness in that shape unfolds to. Composing the two carries the condition
     * inwards, which is the step every inductive case of an idleness proof begins with.
     */
    def notInside(shape: Kernel.Thm, clause: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        head <- freeHead
        carried <- Conv.apTerm(head, shape)
        joined <- Conv.trans(carried, clause)
        result <- forwardNot(joined, sideCondition)
      } yield result

    /** A conditional whose guard is known to fail, taken to its second branch. */
    def denied(value: Kernel.Thm, denial: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        conditional <- Term
          .destEq(value.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", value.conclusion))
        split <- conditional match {
          case App(App(App(_, guard), yes), no) => Right((guard, yes, no))
          case other => Left(NotOfForm("a conditional", other))
        }
        scheme <- classical
          .fact(Classical.CondFalse)
          .map(Kernel.instType(Map(Classical.TypeVariable -> vocabulary.numbers), _))
        taken <- rules
          .specAll(scheme, List(split._1, split._2, split._3))
          .flatMap(rules.mp(_, denial))
        moved <- Conv.trans(value, taken)
      } yield moved

    /** Put what the hypothesis gave back under the constructor the clause rebuilt. */
    def underConstructor(value: Kernel.Thm, inner: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        built <- Term
          .destEq(value.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", value.conclusion))
        head <- built match {
          case App(applied, _) => Right(applied)
          case other => Left(NotOfForm("a constructor applied to something", other))
        }
        lifted <- Conv.apTerm(head, inner)
        joined <- Conv.trans(value, lifted)
      } yield joined

    /** The code written with a literal tag, which the substitution's equations are stated at. */
    def atLiteral(tagIs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .apTerm(vocabulary.code, tagIs)
        .flatMap(Conv.apThm(_, payload))
        .flatMap(Conv.trans(isCode, _))

    /** The same with the payload opened into a pair as well. */
    def atLiteralPair(tagIs: Kernel.Thm, isPair: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        withTag <- atLiteral(tagIs)
        literal <- Term.destEq(withTag.conclusion).map(_._2) match {
          case Some(App(App(_, value), _)) => Right(value)
          case _ => Left(NotOfForm("a code", withTag.conclusion))
        }
        head <- LogicError.lift(Term.app(vocabulary.code, literal))
        result <- Conv.apTerm(head, isPair).flatMap(Conv.trans(withTag, _))
      } yield result

    /** What the substitution gives at this shape. */
    def valueAt(shape: Kernel.Thm, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      LogicError
        .lift(Term.appAll(substitute, List(index, replacement)))
        .flatMap(head => Conv.apTerm(head, shape))
        .flatMap(Conv.trans(_, equation))

    /** The goal, from a claim about what the substitution gives. */
    def carried(value: Kernel.Thm, proved: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .sym(value)
        .flatMap(equation => claimHead.flatMap(head => Conv.apTerm(head, equation)))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, proved)))

    /** The subject itself is well formed, carried back along a value that is the subject. */
    def unchanged(value: Kernel.Thm, shape: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .trans(value, Conv.sym(shape).getOrElse(shape))
        .flatMap(equation =>
          Conv
            .sym(equation)
            .flatMap(reversed =>
              claimHead.flatMap(head => Conv.apTerm(head, reversed)))
            .flatMap(reversed => LogicError.lift(Kernel.eqMp(reversed, subjectIsWellFormed)))
        )

    /**
     * The equation goal at this shape: what the substitution gives IS the code it was given.
     *
     * The counterpart of [[unchanged]] for a clause set whose claim is an equation rather than a
     * predicate. There is nothing to carry across: the value and the shape meet directly.
     */
    def itself(value: Kernel.Thm, shape: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.trans(value, Conv.sym(shape).getOrElse(shape))

    /** A clause whose answer is a conditional, decided both ways. */
    def bothWays(
      value: Kernel.Thm,
      whenHeld: (Kernel.Thm, Term) => Either[LogicError, Kernel.Thm],
      whenDenied: (Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        conditional <- Term
          .destEq(value.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", value.conclusion))
        split <- conditional match {
          case App(App(App(_, guard), yes), no) => Right((guard, yes, no))
          case other => Left(NotOfForm("a conditional", other))
        }
        numbers = vocabulary.numbers
        middle <- classical.fact(Classical.ExcludedMiddle)
        cases <- rules.spec(split._1, middle)
        condTrue <- classical
          .fact(Classical.CondTrue)
          .map(Kernel.instType(Map(Classical.TypeVariable -> numbers), _))
        condFalse <- classical
          .fact(Classical.CondFalse)
          .map(Kernel.instType(Map(Classical.TypeVariable -> numbers), _))
        whenTrue <- for {
          held <- LogicError.lift(Kernel.assume(split._1))
          taken <- rules
            .specAll(condTrue, List(split._1, split._2, split._3))
            .flatMap(rules.mp(_, held))
          moved <- Conv.trans(value, taken)
          result <- whenHeld(moved, split._2)
        } yield result
        whenFalse <- for {
          denied <- logic.mkNot(split._1).flatMap(term => LogicError.lift(Kernel.assume(term)))
          taken <- rules
            .specAll(condFalse, List(split._1, split._2, split._3))
            .flatMap(rules.mp(_, denied))
          moved <- Conv.trans(value, taken)
          result <- whenDenied(moved, split._3)
        } yield result
        settled <- rules.disjElim(cases, whenTrue, whenFalse)
      } yield settled
  }

  /* ------------------------------------------------------------------ the two clause tables */

  /**
   * The four clauses of [[SubstituteKeepsTerms]], as a function of the site.
   *
   * A variable becomes the replacement or stays itself, and both are terms by a premise; zero stays
   * itself; a successor and a binary constructor ask the induction hypothesis at their sub-codes
   * and rebuild with the introduction rule.
   */
  private def termClause(
    introductions: Map[String, Kernel.Thm],
    equations: Map[String, Kernel.Thm]
  )(site: Site, which: Int): Either[LogicError, Kernel.Thm] = {
    val rules = site.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(site.parts(which)))
      result <- which match {
        case 0 =>
          for {
            shape <- site.atLiteral(assumed)
            equation <- rules.specAll(
              equations(SubstituteVariable), List(site.index, site.replacement, site.payload))
            value <- site.valueAt(shape, equation)
            settled <- site.bothWays(
              value,
              (moved, _) => site.carried(moved, site.sideCondition),
              (moved, _) => site.unchanged(moved, shape)
            )
          } yield settled

        case 1 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            payloadIs <- rules.conjElim2(assumed)
            shape <- site.atLiteralPair(tagIs, payloadIs)
            equation <- rules.specAll(
              equations(SubstituteZero), List(site.index, site.replacement))
            value <- site.valueAt(shape, equation)
            settled <- site.unchanged(value, shape)
          } yield settled

        case 2 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            payloadIsTerm <- rules.conjElim2(assumed)
            shape <- site.atLiteral(tagIs)
            equation <- rules.specAll(
              equations(SubstituteSuccessor),
              List(site.index, site.replacement, site.payload))
            value <- site.valueAt(shape, equation)
            shorter <- site.inductive(site.payload, shape, payloadIsTerm)
            inside <- site.substituted(site.payload)
            built <- rules.spec(inside, introductions(TermSuccessor)).flatMap(rules.mp(_, shorter))
            settled <- site.carried(value, built)
          } yield settled

        case _ =>
          for {
            tags <- rules.conjElim1(assumed)
            arguments <- rules.conjElim2(assumed)
            split <- site.logic
              .destDisj(tags.conclusion)
              .toRight(NotOfForm("a disjunction", tags.conclusion))
            three <- LogicError
              .lift(Kernel.assume(split._1))
              .flatMap(binaryClause(site, arguments, _, TermSum, equations(SubstituteSum),
                introductions(TermSum)))
            four <- LogicError
              .lift(Kernel.assume(split._2))
              .flatMap(binaryClause(site, arguments, _, TermProduct, equations(SubstituteProduct),
                introductions(TermProduct)))
            settled <- rules.disjElim(tags, three, four)
          } yield settled
      }
    } yield result
  }

  /**
   * The four clauses of [[SubstituteIdle]], as a function of the site.
   *
   * Every case begins the same way, by carrying the code's freeness condition inwards through the
   * clause of `NUM_FREE_TERM` that matches the shape, and that is the whole difference from
   * [[termClause]] beside it: there the second premise of the induction hypothesis is about the
   * replacement and is passed down untouched, here it is about the subject and has to be rebuilt
   * at every sub-code.
   *
   * The variable case is the one that does not recurse and is where the condition earns its
   * keep. `NUM_FREE_TERM i (NUM_CODE 0 j)` is `j = i`, so the condition IS the denial of the
   * substitution's guard, and the conditional goes to its second branch without a case split.
   * `termClause` splits there because it has no such condition and must handle both answers; this
   * one cannot reach the first answer at all, which is the content of the lemma seen locally.
   */
  private def idleClause(
    freeness: Map[String, Kernel.Thm],
    equations: Map[String, Kernel.Thm]
  )(site: Site, which: Int): Either[LogicError, Kernel.Thm] = {
    val rules = site.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(site.parts(which)))
      result <- which match {
        case 0 =>
          for {
            shape <- site.atLiteral(assumed)
            equation <- rules.specAll(
              equations(SubstituteVariable), List(site.index, site.replacement, site.payload))
            value <- site.valueAt(shape, equation)
            clause <- rules.specAll(freeness(FreeVariable), List(site.index, site.payload))
            apart <- site.notInside(shape, clause)
            taken <- site.denied(value, apart)
            settled <- site.itself(taken, shape)
          } yield settled

        case 1 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            payloadIs <- rules.conjElim2(assumed)
            shape <- site.atLiteralPair(tagIs, payloadIs)
            equation <- rules.specAll(
              equations(SubstituteZero), List(site.index, site.replacement))
            value <- site.valueAt(shape, equation)
            settled <- site.itself(value, shape)
          } yield settled

        case 2 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            payloadIsTerm <- rules.conjElim2(assumed)
            shape <- site.atLiteral(tagIs)
            equation <- rules.specAll(
              equations(SubstituteSuccessor),
              List(site.index, site.replacement, site.payload))
            value <- site.valueAt(shape, equation)
            clause <- rules.specAll(freeness(FreeSuccessor), List(site.index, site.payload))
            inside <- site.notInside(shape, clause)
            shorter <- site.inductiveWith(site.payload, shape, payloadIsTerm, inside)
            rebuilt <- site.underConstructor(value, shorter)
            settled <- site.itself(rebuilt, shape)
          } yield settled

        case _ =>
          for {
            tags <- rules.conjElim1(assumed)
            arguments <- rules.conjElim2(assumed)
            split <- site.logic
              .destDisj(tags.conclusion)
              .toRight(NotOfForm("a disjunction", tags.conclusion))
            three <- LogicError
              .lift(Kernel.assume(split._1))
              .flatMap(binaryIdleClause(
                site, arguments, _, equations(SubstituteSum), freeness(FreeSum)))
            four <- LogicError
              .lift(Kernel.assume(split._2))
              .flatMap(binaryIdleClause(
                site, arguments, _, equations(SubstituteProduct), freeness(FreeProduct)))
            settled <- rules.disjElim(tags, three, four)
          } yield settled
      }
    } yield result
  }

  /**
   * The sum and the product of [[SubstituteIdle]], which differ only in the two facts handed in.
   *
   * The freeness clause here answers with a **disjunction**, so the condition carried inwards is
   * `~(a \/ b)` and De Morgan is what turns it into the two the hypothesis wants. That is the one
   * step this case has and the successor's does not.
   */
  private def binaryIdleClause(
    site: Site,
    arguments: Kernel.Thm,
    tagIs: Kernel.Thm,
    equation: Kernel.Thm,
    freenessClause: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = site.rules

    withWitnesses(
      site.vocabulary,
      arguments,
      Set(site.code, site.tag, site.payload) ++ Term.freeVariables(site.index) ++
        Term.freeVariables(site.replacement)
    ) { (left, right, atRight) =>
      for {
        isPair <- rules.conjElim1(atRight)
        both <- rules.conjElim2(atRight)
        leftIsTerm <- rules.conjElim1(both)
        rightIsTerm <- rules.conjElim2(both)
        shape <- site.atLiteralPair(tagIs, isPair)
        instance <- rules.specAll(equation, List(site.index, site.replacement, left, right))
        value <- site.valueAt(shape, instance)

        clause <- rules.specAll(freenessClause, List(site.index, left, right))
        neither <- site.notInside(shape, clause)
        parted <- site.classical
          .fact(Classical.DeMorganDisjunction)
          .flatMap(law =>
            site.logic
              .destNot(neither.conclusion)
              .toRight(NotOfForm("a negation", neither.conclusion))
              .flatMap(inner =>
                site.logic
                  .destDisj(inner)
                  .toRight(NotOfForm("a disjunction", inner))
                  .flatMap(halves => rules.specAll(law, List(halves._1, halves._2))))
              .flatMap(instanceOfLaw =>
                LogicError.lift(Kernel.eqMp(instanceOfLaw, neither))))
        notLeft <- rules.conjElim1(parted)
        notRight <- rules.conjElim2(parted)

        leftDone <- site.inductiveWith(left, shape, leftIsTerm, notLeft)
        rightDone <- site.inductiveWith(right, shape, rightIsTerm, notRight)

        paired <- LogicError
          .lift(Term.app(site.vocabulary.pair, left))
          .flatMap(_ => Conv.apTerm(site.vocabulary.pair, leftDone))
          .flatMap(half => LogicError.lift(Kernel.mkComb(half, rightDone)))
        built <- Term
          .destEq(value.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", value.conclusion))
        head <- built match {
          case App(applied, _) => Right(applied)
          case other => Left(NotOfForm("a constructor applied to a pair", other))
        }
        lifted <- Conv.apTerm(head, paired)
        joined <- Conv.trans(value, lifted)
        settled <- site.itself(joined, shape)
      } yield settled
    }
  }

  /**
   * A clause whose payload is a pair and whose two components both go through the hypothesis.
   *
   * Shared by the terms' sum and product and by the formulas' implication, which differ only in the
   * equation and the introduction rule they are handed.
   */
  private def binaryClause(
    site: Site,
    arguments: Kernel.Thm,
    tagIs: Kernel.Thm,
    which: String,
    equation: Kernel.Thm,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = site.rules

    withWitnesses(
      site.vocabulary,
      arguments,
      Set(site.code, site.tag, site.payload) ++ Term.freeVariables(site.index) ++
        Term.freeVariables(site.replacement)
    ) { (left, right, atRight) =>
      for {
        isPair <- rules.conjElim1(atRight)
        both <- rules.conjElim2(atRight)
        leftIsWellFormed <- rules.conjElim1(both)
        rightIsWellFormed <- rules.conjElim2(both)
        shape <- site.atLiteralPair(tagIs, isPair)
        instance <- rules.specAll(equation, List(site.index, site.replacement, left, right))
        value <- site.valueAt(shape, instance)
        leftDone <- site.inductive(left, shape, leftIsWellFormed)
        rightDone <- site.inductive(right, shape, rightIsWellFormed)
        leftTerm <- site.substituted(left)
        rightTerm <- site.substituted(right)
        built <- rules
          .specAll(introduction, List(leftTerm, rightTerm))
          .flatMap(rules.mp(_, leftDone))
          .flatMap(rules.mp(_, rightDone))
        settled <- site.carried(value, built)
        _ = which
      } yield settled
    }
  }

  /**
   * The four clauses of [[FormulaSubstituteKeepsFormulas]].
   *
   * Two differ from the terms' in a way worth naming. The **equality** clause asks nothing of the
   * induction hypothesis: its two arguments are terms, so what keeps them terms is
   * [[SubstituteKeepsTerms]], which is a finished lemma rather than a hypothesis. The
   * **quantifier** clause is the one with a conditional, and where the index matches the formula
   * comes back untouched, so it is well formed by the premise rather than by anything rebuilt.
   */
  private def formulaClause(
    introductions: Map[String, Kernel.Thm],
    equations: Map[String, Kernel.Thm],
    keepsTerms: Kernel.Thm
  )(site: Site, which: Int): Either[LogicError, Kernel.Thm] = {
    val rules = site.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(site.parts(which)))
      result <- which match {
        case 0 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            arguments <- rules.conjElim2(assumed)
            settled <- withWitnesses(
              site.vocabulary,
              arguments,
              Set(site.code, site.tag, site.payload) ++ Term.freeVariables(site.index) ++
                Term.freeVariables(site.replacement)
            ) { (left, right, atRight) =>
              for {
                isPair <- rules.conjElim1(atRight)
                both <- rules.conjElim2(atRight)
                leftIsTerm <- rules.conjElim1(both)
                rightIsTerm <- rules.conjElim2(both)
                shape <- site.atLiteralPair(tagIs, isPair)
                instance <- rules.specAll(
                  equations(FormulaSubstituteEquality),
                  List(site.index, site.replacement, left, right))
                value <- site.valueAt(shape, instance)

                // The hypothesis is not asked: both arguments are TERMS, and what keeps a term a
                // term is a lemma rather than this induction.
                leftDone <- rules
                  .specAll(keepsTerms, List(site.index, site.replacement, left))
                  .flatMap(rules.mp(_, leftIsTerm))
                  .flatMap(rules.mp(_, site.sideCondition))
                rightDone <- rules
                  .specAll(keepsTerms, List(site.index, site.replacement, right))
                  .flatMap(rules.mp(_, rightIsTerm))
                  .flatMap(rules.mp(_, site.sideCondition))

                // The TERM substitution, not this site's: an equality's arguments are terms and
                // the clause hands them to the other function. Using the site's own is what the
                // first version did and the refusal printed both.
                leftTerm <- LogicError.lift(Term.appAll(
                  site.vocabulary.substitute, List(site.index, site.replacement, left)))
                rightTerm <- LogicError.lift(Term.appAll(
                  site.vocabulary.substitute, List(site.index, site.replacement, right)))
                built <- rules
                  .specAll(introductions(FormulaEquality), List(leftTerm, rightTerm))
                  .flatMap(rules.mp(_, leftDone))
                  .flatMap(rules.mp(_, rightDone))
                reached <- site.carried(value, built)
              } yield reached
            }
          } yield settled

        case 1 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            payloadIsFormula <- rules.conjElim2(assumed)
            shape <- site.atLiteral(tagIs)
            equation <- rules.specAll(
              equations(FormulaSubstituteNegation),
              List(site.index, site.replacement, site.payload))
            value <- site.valueAt(shape, equation)
            shorter <- site.inductive(site.payload, shape, payloadIsFormula)
            inside <- site.substituted(site.payload)
            built <- rules
              .spec(inside, introductions(FormulaNegation))
              .flatMap(rules.mp(_, shorter))
            settled <- site.carried(value, built)
          } yield settled

        case 2 =>
          for {
            tagIs <- rules.conjElim1(assumed)
            arguments <- rules.conjElim2(assumed)
            settled <- binaryClause(
              site, arguments, tagIs, FormulaImplication,
              equations(FormulaSubstituteImplication), introductions(FormulaImplication))
          } yield settled

        case _ =>
          for {
            tagIs <- rules.conjElim1(assumed)
            arguments <- rules.conjElim2(assumed)
            settled <- withWitnesses(
              site.vocabulary,
              arguments,
              Set(site.code, site.tag, site.payload) ++ Term.freeVariables(site.index) ++
                Term.freeVariables(site.replacement)
            ) { (bound, inner, atInner) =>
              for {
                isPair <- rules.conjElim1(atInner)
                innerIsFormula <- rules.conjElim2(atInner)
                shape <- site.atLiteralPair(tagIs, isPair)
                instance <- rules.specAll(
                  equations(FormulaSubstituteUniversal),
                  List(site.index, site.replacement, bound, inner))
                value <- site.valueAt(shape, instance)
                reached <- site.bothWays(
                  value,
                  // The quantifier binds the variable: the formula comes back untouched.
                  (moved, _) => site.unchanged(moved, shape),
                  (moved, _) =>
                    for {
                      shorter <- site.inductive(inner, shape, innerIsFormula)
                      substituted <- site.substituted(inner)
                      built <- rules
                        .specAll(introductions(FormulaUniversal), List(bound, substituted))
                        .flatMap(rules.mp(_, shorter))
                      settled <- site.carried(moved, built)
                    } yield settled
                )
              } yield reached
            }
          } yield settled
      }
    } yield result
  }

  /* ----------------------------------------------------------- the axioms of the theory */

  /**
   * `NUM_PA` defined, which is one disjunction and no recursion.
   *
   * Seven disjuncts: six codes and one existential over an index and a formula. The definition is
   * built from the same builders the axioms are written with, so what is defined and what a reader
   * checks are the same text.
   */
  private def defineAxioms(
    base: Theory,
    notation: Notation,
    logic: Logic
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] = {
    val disjuncts =
      Axioms.map { case (_, code) => s"n = ($code)" } :+
        s"(${inductionScheme.disjunct("n")})"
    defineByCases(
      base, notation, logic, AxiomName, s"\\n:num. ${disjuncts.mkString(" \\/ ")}", List("n"))
  }

  /**
   * One axiom's membership, which is the definition read in the direction that admits rather than
   * decides.
   *
   * Six of the seven are an equation between a code and itself, so the whole proof is a
   * reflexivity put into the right disjunct. The seventh is the scheme and carries the formula's
   * well-formedness into an existential.
   */
  /* ------------------------------------------------- a disjunction of schemes, in general */

  /** The `count` disjuncts of a right-nested disjunction. */
  private def disjunctsOf(
    logic: Logic,
    term: Term,
    count: Int
  ): Either[LogicError, Vector[Term]] =
    if (count == 1) Right(Vector(term))
    else
      logic
        .destDisj(term)
        .toRight(NotOfForm("a disjunction", term))
        .flatMap(split => disjunctsOf(logic, split._2, count - 1).map(split._1 +: _))

  /** The right-nested disjunction of a run of disjuncts. */
  private def nestOf(logic: Logic, run: Vector[Term]): Either[LogicError, Term] =
    run.toList.reverse match {
      case Nil => Left(MissingDefinition("at least one disjunct"))
      case last :: rest =>
        rest.foldLeft[Either[LogicError, Term]](Right(last))((carried, one) =>
          carried.flatMap(logic.mkDisj(one, _))
        )
    }

  /**
   * A proof of the `which`th disjunct, put back into the nest.
   *
   * The nest is right-associated, so the proof enters at its own position and is then wrapped once
   * for each disjunct **before** it. Getting the two directions the wrong way round is what the
   * first version did, and what came back was a disjunction of the right disjuncts in the wrong
   * shape, which `Kernel.eqMp` refused with both nests printed in full.
   */
  private def injectedAt(
    logic: Logic,
    rules: Rules,
    parts: Vector[Term],
    which: Int,
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      entered <-
        if (which == parts.size - 1) Right(proof)
        else nestOf(logic, parts.drop(which + 1)).flatMap(rules.disjIntro1(_, proof))
      result <- (0 until which).reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(entered)) {
        (carried, before) => carried.flatMap(rules.disjIntro2(parts(before), _))
      }
    } yield result

  /**
   * One scheme's membership, which is its published statement read as a way into the disjunction.
   *
   * A scheme's disjunct is `?b1 ... bn. prem1 /\ ... /\ premk /\ n = <the code>` and its statement
   * is `!b1 ... bn. prem1 ==> ... ==> premk ==> <the set> <the code>`. The two carry the same
   * information in the two shapes a caller wants, and this walks from the second to the first:
   * assume each premise, conjoin them onto the reflexivity of the code, put the result under the
   * existentials by [[Rules.existsIntro]] from the innermost binder outwards, inject it into the
   * nest, and discharge.
   *
   * Written once for every scheme there is. The axioms of PA have one and the logical axioms are
   * nothing but schemes, so the alternative was this derivation written nine times with the arity
   * changed, which is the shape of duplication this file has already paid for once.
   */
  private def schemeMembership(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    count: Int,
    which: Int,
    scheme: Scheme,
    head: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    /** Peel `howMany` implications, giving their antecedents and what is left. */
    def peeled(term: Term, howMany: Int): Either[LogicError, (List[Term], Term)] =
      if (howMany == 0) Right((Nil, term))
      else
        logic
          .destImp(term)
          .toRight(NotOfForm("an implication", term))
          .flatMap { case (antecedent, rest) =>
            peeled(rest, howMany - 1).map { case (found, last) => (antecedent :: found, last) }
          }

    for {
      statement <- vocabulary.statement(scheme.name)
      stripped <- Logic.stripForall(statement)
      witnesses = stripped._1
      _ <-
        if (witnesses.size == scheme.binders.size) Right(())
        // Through `Prose.count` because the singular is reachable here and nothing above would show
        // it: of the nine schemes this file builds, `NUM_LOGIC`'s reflexivity of equality binds
        // exactly one variable, so a mismatch on that one read "a claim binding 1 variables".
        else {
          val wanted = s"a claim binding ${Prose.count(scheme.binders.size, "variable")}"
          Left(NotOfForm(wanted, statement))
        }
      split <- peeled(stripped._2, scheme.premises.size)
      (antecedents, conclusion) = split
      assumed <- antecedents.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
        (carried, antecedent) =>
          for {
            found <- carried
            made <- LogicError.lift(Kernel.assume(antecedent))
          } yield found :+ made
      }
      code <- conclusion match {
        case App(function, argument) if function == head => Right(argument)
        case other => Left(NotOfForm("a claim about a code", other))
      }
      instance <- rules.spec(code, cases)
      right <- Term
        .destEq(instance.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", instance.conclusion))
      parts <- disjunctsOf(logic, right, count)

      // The disjunct opened one binder at a time, so that each level's predicate is what
      // `existsIntro` has to be given at that level.
      levels <- witnesses.foldLeft[Either[LogicError, Vector[Term]]](Right(Vector(parts(which)))) {
        (carried, witness) =>
          for {
            found <- carried
            next <- vocabulary.instantiate(found.last, witness)
          } yield found :+ next
      }
      conjoined <- assumed.foldRight[Either[LogicError, Kernel.Thm]](Right(Conv.refl(code))) {
        (premise, carried) => carried.flatMap(rules.conjIntro(premise, _))
      }
      under <- witnesses.indices.reverse.foldLeft[Either[LogicError, Kernel.Thm]](
        Right(conjoined)
      ) { (carried, at) =>
        for {
          held <- carried
          predicate <- logic
            .destExistsPredicate(levels(at))
            .toRight(NotOfForm("an existential", levels(at)))
          result <- rules.existsIntro(predicate, witnesses(at), held)
        } yield result
      }
      placed <- injectedAt(logic, rules, parts, which, under)
      settled <- Conv
        .sym(instance)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, placed)))
      discharged <- antecedents.foldRight[Either[LogicError, Kernel.Thm]](Right(settled)) {
        (antecedent, carried) => carried.flatMap(rules.disch(antecedent, _))
      }
      closed <- rules.genAll(discharged, witnesses.toList)
      checked <- vocabulary.checked(scheme.name, closed)
    } yield checked
  }

  /** `NUM_CLOSED`, and the equation that says what it is. */
  private def defineClosed(
    base: Theory,
    notation: Notation,
    logic: Logic
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] =
    defineByCases(
      base, notation, logic, ClosedName, "\\t:num. !k:num. ~(NUM_FREE_TERM k t)", List("t"))

  /**
   * The six code-builders, each defined over the theory the ones before it produced.
   *
   * The order is forced rather than chosen: [[LessName]] is written with [[ExistsName]],
   * [[AllBelowName]] with [[LessName]], and [[ExistsBelowName]] with all three of
   * [[ExistsName]], [[AndName]] and [[LessName]]. A constant cannot appear in the body defining
   * another until it is in the theory, so the sequence below is the dependency order read off.
   *
   * Every one goes through [[defineByCases]] and therefore costs nothing: what comes back is the
   * definition unfolded at variables and generalised, which is an equation the kernel produced
   * from a definition and no axiom. That is the same reason [[ClosedCases]] and [[LogicCases]] are
   * free, and `LanguageSpec` asserts the six join them rather than leaving it to be read.
   */
  private def defineConnectives(
    base: Theory,
    notation: Notation,
    logic: Logic
  ): Either[LogicError, (Theory, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] = {
    val bodies: Vector[(String, String, String, List[String])] = Vector(
      (
        AndName,
        AndCases,
        "\\p:num q:num. NUM_CODE 6 (NUM_CODE 7 (NUM_PAIR p (NUM_CODE 6 q)))",
        List("p", "q")),
      (
        OrName,
        OrCases,
        "\\p:num q:num. NUM_CODE 7 (NUM_PAIR (NUM_CODE 6 p) q)",
        List("p", "q")),
      (
        ExistsName,
        ExistsCases,
        "\\i:num p:num. NUM_CODE 6 (NUM_CODE 8 (NUM_PAIR i (NUM_CODE 6 p)))",
        List("i", "p")),
      (
        LessName,
        LessCases,
        "\\z:num s:num t:num. NUM_EXISTS z (NUM_CODE 5 (NUM_PAIR " +
          "(NUM_CODE 3 (NUM_PAIR s (NUM_CODE 2 (NUM_CODE 0 z)))) t))",
        List("z", "s", "t")),
      (
        AllBelowName,
        AllBelowCases,
        "\\z:num i:num t:num p:num. NUM_CODE 8 (NUM_PAIR i " +
          "(NUM_CODE 7 (NUM_PAIR (NUM_LESS z (NUM_CODE 0 i) t) p)))",
        List("z", "i", "t", "p")),
      (
        ExistsBelowName,
        ExistsBelowCases,
        "\\z:num i:num t:num p:num. NUM_EXISTS i (NUM_AND (NUM_LESS z (NUM_CODE 0 i) t) p)",
        List("z", "i", "t", "p"))
    )

    bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm], Map[String, Kernel.Thm])]](
      Right((base, Map.empty, Map.empty))
    ) { case (carried, (name, casesName, text, subjects)) =>
      for {
        state <- carried
        (theory, definitions, cases) = state
        built <- defineByCases(theory, notation, logic, name, text, subjects)
        (wider, definition, equation) = built
      } yield (
        wider,
        definitions.updated(name, definition),
        cases.updated(casesName, equation))
    }
  }

  /** `NUM_LOGIC`, a disjunction of eight schemes, and the equation that says what it is. */
  private def defineLogic(
    base: Theory,
    notation: Notation,
    logic: Logic
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] = {
    val disjuncts = logicalSchemes.map(scheme => s"(${scheme.disjunct("n")})")
    defineByCases(
      base, notation, logic, LogicName, s"\\n:num. ${disjuncts.mkString(" \\/ ")}", List("n"))
  }

  /**
   * A constant defined by a body, with the equation at a variable published beside it.
   *
   * Nine definitions here are of this shape and none of them is a recursion, but they are two
   * kinds of thing and the count alone hides that.
   *
   * **Three are predicates**: `NUM_CLOSED`, `NUM_PA` and `NUM_LOGIC`. What makes a set of codes
   * decidable is that its definition does not descend into one, and each of the three says so by
   * being a formula with its subject free. That is the property `docs/adr/0013` needs and it is
   * why they are here rather than under [[definePredicate]].
   *
   * **Six build codes**: the derived connectives, from [[AndName]] to [[ExistsBelowName]]. They are
   * not decidable sets and the sentence above says nothing about them; what they share with the
   * three is only the shape of the definition, which is why one routine serves both. Each is a
   * function into `num`, and what says it is well behaved is not the absence of a recursion but the
   * `NUM_FORM_` fact published about it.
   */
  private[theories] def defineByCases(
    base: Theory,
    notation: Notation,
    logic: Logic,
    name: String,
    text: String,
    subjectNames: List[String]
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] =
    for {
      body <- Parser.term(base, notation, text)
      defined <- LogicError.lift(Kernel.defineConstant(base, name, body))
      (theory, definition) = defined
      wider <- logic.over(theory)
      subjects = subjectNames.map(name => Term.variable(name, TyApp(Natural.TypeName, Nil)))
      unfolded <- Conv.unfold(definition, subjects)
      general <- wider.rules.genAll(unfolded, subjects)
    } yield (theory, definition, general)

  /**
   * One axiom of PA's membership, which is the definition read in the direction that admits.
   *
   * Six of the seven are an equation between a code and itself, so the whole proof is a
   * reflexivity put into the right disjunct. The seventh is the induction scheme and goes through
   * [[schemeMembership]], which the logical axioms use for every one of theirs.
   */
  private def axiomAt(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    which: Int
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers

    if (which < Axioms.size)
      for {
        statement <- vocabulary.statement(Axioms(which)._1)
        code <- Parser.term(vocabulary.theory, vocabulary.notation, Axioms(which)._2, numbers)
        instance <- rules.spec(code, cases)
        right <- Term
          .destEq(instance.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", instance.conclusion))
        parts <- disjunctsOf(logic, right, Axioms.size + 1)
        placed <- injectedAt(logic, rules, parts, which, Conv.refl(code))
        settled <- Conv
          .sym(instance)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, placed)))
        checked <-
          if (settled.conclusion == statement) Right(settled)
          else
            Left(NotOfForm(s"the statement published for ${Axioms(which)._1}", settled.conclusion))
      } yield checked
    else
      LogicError
        .lift(vocabulary.theory.constant(AxiomName, Type.fun(numbers, Type.Bool)))
        .flatMap(head =>
          schemeMembership(vocabulary, cases, Axioms.size + 1, which, inductionScheme, head)
        )
  }

  /** The theorems standing for a scheme's holes, kept apart by which of the two they are. */
  private final case class Holes(
    formulas: Map[String, Kernel.Thm],
    terms: Map[String, Kernel.Thm]
  )

  private object Holes {
    val none: Holes = Holes(Map.empty, Map.empty)
  }

  /**
   * Every member of a set of codes is a formula, which walks the same trees the codes came from.
   *
   * The shape is a case analysis over the set's own equation read in the deciding direction. A
   * fixed code is an equation between `n` and that code, so the work is to prove the code is a
   * formula and carry the proof across. A scheme opens its existentials, takes its conditions out
   * of the conjunction, and those conditions are exactly the theorems its holes need.
   *
   * Written once for both sets. PA is six fixed codes and one scheme; the logical axioms are eight
   * schemes and no fixed code; and the walk does not care which it is looking at beyond the two
   * cases below.
   *
   * The two provers are separate rather than one function over `Obj` because a node is a term or a
   * formula and nothing else decides which, and the holes are kept in two maps for the same reason.
   * Written as one, a term node reaching a formula position is a type error nowhere: the constants
   * have the same type and the same arity, and the kernel would be the first thing to notice. That
   * already happened once in this file, in the formula substitution's equality clause, and it took
   * a refusal pages away to find.
   */
  private def everyMemberIsAFormula(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    fixed: Vector[Obj],
    schemes: Vector[Scheme],
    statementName: String
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers

    def code(expression: Obj): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, render(expression), numbers)

    def index(name: String): Either[LogicError, Term] =
      Parser.term(vocabulary.theory, vocabulary.notation, name, numbers)

    def refuse(what: String, expression: Obj): Either[LogicError, Kernel.Thm] =
      code(expression).flatMap(subject => Left(NotOfForm(what, subject)))

    /**
     * A rule taken at its arguments and then given its premises, in the order it states them.
     *
     * The arguments go in by position, which is the call `AGENTS.md` warns about and is safe here
     * for a reason worth stating rather than assuming: every binder is over `num`, so a reversal
     * would type, but what comes back is checked against the published statement at the end, and a
     * reversal cannot reach it.
     */
    def applied(
      name: String,
      arguments: List[Term],
      premises: List[Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        rule <- vocabulary.fact(name)
        taken <- rules.specAll(rule, arguments)
        result <- premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(taken))(
          (carried, premise) => carried.flatMap(rules.mp(_, premise))
        )
      } yield result

    def wellFormedTerm(expression: Obj, holes: Holes): Either[LogicError, Kernel.Thm] =
      expression match {
        case Obj.Var(at) => index(at).flatMap(at => applied(TermVariable, List(at), Nil))
        case Obj.Zero    => vocabulary.fact(TermZero)
        case Obj.Succ(inner) =>
          for {
            proved <- wellFormedTerm(inner, holes)
            subject <- code(inner)
            result <- applied(TermSuccessor, List(subject), List(proved))
          } yield result
        case Obj.Sum(left, right)  => binaryTerm(TermSum, left, right, holes)
        case Obj.Prod(left, right) => binaryTerm(TermProduct, left, right, holes)
        case Obj.TermHole(name)    => holes.terms.get(name).toRight(MissingDefinition(name))
        case other                 => refuse("a term of the object language", other)
      }

    def binaryTerm(
      name: String,
      left: Obj,
      right: Obj,
      holes: Holes
    ): Either[LogicError, Kernel.Thm] =
      for {
        first <- wellFormedTerm(left, holes)
        second <- wellFormedTerm(right, holes)
        one <- code(left)
        two <- code(right)
        result <- applied(name, List(one, two), List(first, second))
      } yield result

    def wellFormedFormula(expression: Obj, holes: Holes): Either[LogicError, Kernel.Thm] =
      expression match {
        case Obj.Eq(left, right) =>
          for {
            first <- wellFormedTerm(left, holes)
            second <- wellFormedTerm(right, holes)
            one <- code(left)
            two <- code(right)
            result <- applied(FormulaEquality, List(one, two), List(first, second))
          } yield result
        case Obj.Not(inner) =>
          for {
            proved <- wellFormedFormula(inner, holes)
            subject <- code(inner)
            result <- applied(FormulaNegation, List(subject), List(proved))
          } yield result
        case Obj.Implies(left, right) =>
          for {
            first <- wellFormedFormula(left, holes)
            second <- wellFormedFormula(right, holes)
            one <- code(left)
            two <- code(right)
            result <- applied(FormulaImplication, List(one, two), List(first, second))
          } yield result
        case Obj.Forall(at, inner) =>
          for {
            proved <- wellFormedFormula(inner, holes)
            bound <- index(at)
            subject <- code(inner)
            result <- applied(FormulaUniversal, List(bound, subject), List(proved))
          } yield result
        case Obj.Hole(name) =>
          holes.formulas.get(name).toRight(MissingDefinition(name))
        case Obj.Substituted(at, replacement, inner) =>
          for {
            proved <- wellFormedFormula(inner, holes)
            carried <- wellFormedTerm(replacement, holes)
            bound <- index(at)
            into <- code(replacement)
            subject <- code(inner)
            result <- applied(
              FormulaSubstituteKeepsFormulas,
              List(bound, into, subject),
              List(proved, carried)
            )
          } yield result
        case other => refuse("a formula of the object language", other)
      }

    /** `|- NUM_FORM c` and `n = c` assumed give `n = c |- NUM_FORM n`. */
    def carried(equation: Kernel.Thm, wellFormed: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        congruent <- Conv.apTerm(vocabulary.formula, equation)
        reversed <- Conv.sym(congruent)
        result <- LogicError.lift(Kernel.eqMp(reversed, wellFormed))
      } yield result

    /** The first `howMany` conjuncts of a right-nested conjunction, and what is left. */
    def conjuncts(
      theorem: Kernel.Thm,
      howMany: Int
    ): Either[LogicError, (List[Kernel.Thm], Kernel.Thm)] =
      if (howMany == 0) Right((Nil, theorem))
      else
        for {
          head <- rules.conjElim1(theorem)
          rest <- rules.conjElim2(theorem)
          split <- conjuncts(rest, howMany - 1)
        } yield (head :: split._1, split._2)

    val subject = Term.variable("n", numbers)

    /**
     * One scheme's case: its existentials opened, its conditions taken out, its tree proved.
     *
     * The conditions come back in the order the scheme states them, so which theorem discharges
     * which hole is read off [[Condition]] rather than guessed. A condition that discharges no hole
     * is skipped here and is not unused: it is what the object theory needs and what this proof
     * does not.
     */
    def schemeCase(assumed: Kernel.Thm, scheme: Scheme): Either[LogicError, Kernel.Thm] = {
      val witnesses = scheme.binders.map(name => Term.variable(name, numbers))

      def opened(
        held: Kernel.Thm,
        remaining: List[FVar]
      ): Either[LogicError, Kernel.Thm] = remaining match {
        case Nil =>
          for {
            split <- conjuncts(held, scheme.premises.size)
            (conditions, equation) = split
            holes = scheme.premises.zip(conditions).foldLeft(Holes.none) {
              case (carried, (Condition.IsFormula(hole), proved)) =>
                carried.copy(formulas = carried.formulas.updated(hole, proved))
              case (carried, (Condition.IsTerm(hole), proved)) =>
                carried.copy(terms = carried.terms.updated(hole, proved))
              case (carried, _) => carried
            }
            proved <- wellFormedFormula(scheme.tree, holes)
            result <- carried(equation, proved)
          } yield result
        case witness :: rest =>
          for {
            body <- vocabulary.instantiate(held.conclusion, witness)
            inner <- LogicError.lift(Kernel.assume(body))
            reached <- opened(inner, rest)
            result <- rules.existsElim(held, witness, reached)
          } yield result
      }

      opened(assumed, witnesses)
    }

    def caseAt(assumed: Kernel.Thm, at: Int): Either[LogicError, Kernel.Thm] =
      if (at < fixed.size)
        for {
          proved <- wellFormedFormula(fixed(at), Holes.none)
          result <- carried(assumed, proved)
        } yield result
      else schemeCase(assumed, schemes(at - fixed.size))

    /**
     * The nest, taken one disjunct at a time.
     *
     * `Rules.disjElim` discharges each case's own disjunct, so a case is built from an assumption
     * of it and nothing has to be discharged by hand. The recursion stops where the term is no
     * longer a disjunction, which is the last.
     */
    def eliminate(theorem: Kernel.Thm, at: Int): Either[LogicError, Kernel.Thm] =
      logic.destDisj(theorem.conclusion) match {
        case None => caseAt(theorem, at)
        case Some((first, rest)) =>
          for {
            firstAssumed <- LogicError.lift(Kernel.assume(first))
            left <- caseAt(firstAssumed, at)
            restAssumed <- LogicError.lift(Kernel.assume(rest))
            right <- eliminate(restAssumed, at + 1)
            result <- rules.disjElim(theorem, left, right)
          } yield result
      }

    for {
      instance <- rules.spec(subject, cases)
      membership <- Term
        .destEq(instance.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", instance.conclusion))
      assumed <- LogicError.lift(Kernel.assume(membership))
      disjunction <- LogicError.lift(Kernel.eqMp(instance, assumed))
      eliminated <- eliminate(disjunction, 0)
      implied <- rules.disch(membership, eliminated)
      closed <- rules.gen(subject, implied)
      checked <- vocabulary.checked(statementName, closed)
    } yield checked
  }
}
