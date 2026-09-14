package garden.xeno.symbolum.kernel

/**
 * The inference rules, and the only place a theorem can come from.
 *
 * [[Thm]] is a class whose constructor is private to this object, so a value of that type exists
 * only because one of the functions below produced it, and a cast cannot manufacture one: the
 * comment on [[Thm]] records why an opaque type was not enough. Everything else in the system,
 * every tactic, every decision procedure, the computer algebra system, may be arbitrarily wrong:
 * the worst it can do is fail to produce a theorem, or produce one that is true but useless.
 *
 * That is the whole correctness argument, and it is worth being precise about what it rests on:
 *
 *  - the ten inference rules below are the rules of higher-order logic with equality, and the
 *    three theory extensions beside them are declared: two are conservative and the third,
 *    [[assertAxiom]], is the only operation here that adds to what must be believed;
 *  - terms are well-typed by construction, so no rule has to re-check what it was handed;
 *  - substitution cannot capture, which is a property of the representation provided every term
 *    that enters is locally closed; each rule checks that where a term comes in rather than
 *    assuming it, because the body an abstraction's extractor hands out is not.
 *
 * == What this does not cover ==
 *
 * A theorem does not record the theory it was proved against. What stands in for that is carried by
 * the constants a theorem mentions, and it reaches half the cases.
 *
 * **The half that is closed, since `docs/adr/0008`.** A constant made by [[defineConstant]] carries
 * the term that defined it, and the `abs` and `rep` of [[defineType]] carry the predicate the type
 * was carved from, so two constants are the same constant only when the name, the type **and** that
 * origin agree. Two theories that define one name differently hand out two different terms, and
 * [[trans]] declines to chain their theorems by the `==` the rules already perform: no rule was
 * changed to make that happen. Until 2026-09-10 this was a derivation of `|- T = F` from two
 * theorems the kernel was right to produce, and `SoundnessAttackSpec` no longer runs that
 * derivation. It asserts the refusal and the clause its message has to carry, that two theories
 * defining a name the same way still chain, and the valid inference this costs, which is that a
 * theorem about a declared `c` no longer combines with one about a `c` defined elsewhere.
 *
 * **The half that is open: a constant declared and then given its meaning by an axiom.**
 * [[Theory.declareConstant]] writes nothing into `Theory.origins`, and [[Theory.constant]] reads
 * that map, so such a constant carries no origin and two absent origins compare equal. Two theories
 * that declare one name and assert different axioms about it are each consistent, their two `c`s
 * are the same term, and symmetry and transitivity chain `|- c = T` with `|- c = F` into `|- T = F`
 * exactly as before. It is the shape the developments here are built in rather than a corner: the
 * operations `RealSpec` asserts are declared rather than defined are the ones the sixteen axioms
 * give their meaning to, and `Classical.Select` is declared and axiomatised the same way. An
 * adversarial audit found this on 2026-09-10, no test pins it, and it is unrepaired.
 *
 * The origin cannot reach that half, a declared constant having no defining term to carry. A
 * lineage on every theorem would, which Isabelle checks at every binary rule, and one global theory
 * makes it unnecessary, which is why HOL Light has neither. `docs/adr/0008` measured the first and
 * rejected it on cost: [[refl]], [[assume]] and [[beta]] are the three rules that admit a term from
 * outside, about 240 call sites between them, and [[refl]] would stop being total.
 *
 * One thing outside the kernel reduces the exposure without closing it: a development built **over**
 * another rather than beside it has one chain and one `c`, which is why `Real.construct` and
 * `Natural.construct` take the theory they extend. `NaturalSpec` builds the naturals over the reals
 * over `Classical`, states a proposition neither standard development can state, and pins the axiom
 * count of the result; it also measures what staying siblings costs, both ways round, in that
 * neither standard theory can read the other's theorems at all.
 *
 * Nor does any of this say the axioms of a theory are consistent. That is the caller's
 * responsibility and the reason [[Theory.axioms]] is readable.
 */
object Kernel {

  /**
   * A proved sequent: hypotheses on the left, conclusion on the right.
   *
   * A class with a constructor nobody outside this package can call, so the only way to obtain one
   * is to derive it. The hypotheses are kept sorted and duplicate-free, so two derivations of the
   * same sequent by different routes produce equal values.
   *
   * **It was an opaque type over a pair until 2026-09-10, and that was not enough.** An opaque type
   * is a compile-time fiction: it erases to what it wraps, so `(Nil, p).asInstanceOf[Kernel.Thm]`
   * compiled and ran and produced `|- p` out of nothing. `TrustBoundaryTwinSpec` asserted the half
   * that held, that the assignment does not typecheck, and the cast went round it. A class does not
   * erase, so the same cast is now a `ClassCastException`.
   *
   * **And that sentence used to go on to say more than it should.** It said the boundary is
   * "enforced by the runtime rather than by the compiler alone, which is the difference between a
   * wall and a convention". The runtime enforces the **type**, which is why the cast throws. It
   * does not enforce the **construction**: `private[Kernel]` is a Scala access rule and the
   * constructor it compiles to is `public` in the bytecode, so a caller willing to use reflection
   * builds a theorem with no cast, no access check and nothing raised. `TrustBoundaryTwinSpec`
   * measures both halves rather than describing them.
   *
   * That is the threshold this argument stops at, and what lies past it is `modules/checker` rather
   * than anything here. A forged theorem carries a derivation, and a second reading of that
   * derivation refuses one that does not add up; since 2026-09-11 it also refuses one that adds up
   * by naming an axiom the theory never asserted, which was the one shape that got through. Neither
   * of those defences is the kernel's, and saying so is the point: **a theorem is trustworthy here
   * because of how it was made, and a caller that did not make it should check it.**
   *
   * OCaml's abstract types, which HOL Light's `thm` is one of, are in the same position and worse
   * off: `Obj.magic` defeats them, nothing at runtime notices, and there is no derivation to
   * re-read afterwards. The cast is stopped here and the forge is not, which is one step better
   * than the tradition rather than a different kind of guarantee.
   */
  final class Thm private[Kernel] (
    val hypotheses: List[Term],
    val conclusion: Term,
    val derivation: Derivation
  ) {

    /** The sequent as `h1, h2 |- c`. */
    def display: String = Printer.show(hypotheses, conclusion)

    override def toString: String = display

    /**
     * Two theorems are equal when they are the same sequent, whatever route derived them.
     *
     * The derivation takes no part, and must not: the rules compare theorems to drop a duplicate
     * hypothesis and to discharge one, and two proofs of one sequent have to be interchangeable
     * there. What a derivation records is how this one was reached, not what it says.
     */
    override def equals(other: Any): Boolean = other match {
      case that: Thm => hypotheses == that.hypotheses && conclusion == that.conclusion
      case _ => false
    }

    override def hashCode(): Int = 31 * hypotheses.hashCode() + conclusion.hashCode()
  }

  /* ------------------------------------------------------------ primitive rules */

  /**
   * `|- t = t`
   *
   * The one rule that takes a term and cannot report a refusal, because it returns a theorem
   * rather than the possibility of one. A term that is not locally closed reaches [[equation]]
   * below and raises, which is the right outcome rather than a soft spot: nothing built through
   * the constructors is open, so only a caller that destructured a binder and handed the body back
   * arrives here, and what it gets is a stopped process instead of a theorem.
   */
  def refl(term: Term): Thm =
    new Thm(Nil, equation(term, term), Derivation.Reflexivity(term))

  /**
   * `G |- a = b` and `D |- b = c` give `G, D |- a = c`
   */
  def trans(left: Thm, right: Thm): Either[KernelError, Thm] =
    sidesOf(left.conclusion).flatMap { case (a, b) =>
      sidesOf(right.conclusion).flatMap { case (middle, c) =>
        if (b != middle) Left(TermsDiffer(b, middle, "transitivity"))
        else
          Right(
            new Thm(
              union(left.hypotheses, right.hypotheses),
              equation(a, c),
              Derivation.Transitivity(left, right)
            )
          )
      }
    }

  /**
   * `G |- f = g` and `D |- x = y` give `G, D |- f x = g y`
   *
   * The two applications are built through the checking constructor, so a pair of equations that
   * cannot be combined is refused here rather than producing a term of the wrong type.
   */
  def mkComb(function: Thm, argument: Thm): Either[KernelError, Thm] =
    sidesOf(function.conclusion).flatMap { case (f, g) =>
      sidesOf(argument.conclusion).flatMap { case (x, y) =>
        for {
          left <- Term.app(f, x)
          right <- Term.app(g, y)
        } yield new Thm(
          union(function.hypotheses, argument.hypotheses),
          equation(left, right),
          Derivation.Congruence(function, argument)
        )
      }
    }

  /**
   * `G |- s = t` gives `G |- (\x. s) = (\x. t)`, provided `x` is not free in `G`
   *
   * The side condition is the whole content of the rule. Without it, `x = 0 |- x = 0` would give
   * `x = 0 |- (\x. x) = (\x. 0)`, a statement about all values from an assumption about one.
   */
  def abs(variable: FVar, theorem: Thm): Either[KernelError, Thm] = {
    // `filter` rather than `exists`, and the difference is the refusal rather than the rule: the
    // side condition is the same either way, and the ones that matched are what a caller needs in
    // order to know which hypothesis to restate or discharge.
    val blocking = theorem.hypotheses.filter(Term.occursFree(variable, _))

    if (blocking.nonEmpty)
      Left(VariableIsFreeInHypotheses(variable, blocking))
    else
      // The two sides come out of a theorem, so they are locally closed and neither abstraction can
      // refuse. Threaded rather than forced anyway: the day one of these rules stops holding that
      // premise is the day the forcing would turn a refusal into a theorem.
      sidesOf(theorem.conclusion).flatMap { case (lhs, rhs) =>
        for {
          left <- Term.abs(variable, lhs)
          right <- Term.abs(variable, rhs)
        } yield new Thm(
          theorem.hypotheses,
          equation(left, right),
          Derivation.Abstraction(variable, theorem)
        )
      }
  }

  /**
   * `|- (\x. t) u = t[u/x]`
   */
  def beta(term: Term): Either[KernelError, Thm] =
    if (!Term.isLocallyClosed(term)) Left(NotLocallyClosed(term))
    else Term.betaReduce(term) match {
      case Some(reduced) =>
        Right(new Thm(Nil, equation(term, reduced), Derivation.BetaStep(term)))
      case None => Left(NotABetaRedex(term))
    }

  /**
   * `p |- p`
   */
  def assume(proposition: Term): Either[KernelError, Thm] =
    if (!Term.isLocallyClosed(proposition)) Left(NotLocallyClosed(proposition))
    else if (Term.isProposition(proposition))
      Right(new Thm(List(proposition), proposition, Derivation.Assumption(proposition)))
    else Left(NotAProposition(proposition, Term.typeOf(proposition)))

  /**
   * `G |- p = q` and `D |- p` give `G, D |- q`
   */
  def eqMp(equivalence: Thm, antecedent: Thm): Either[KernelError, Thm] =
    sidesOf(equivalence.conclusion).flatMap { case (p, q) =>
      if (p != antecedent.conclusion)
        Left(TermsDiffer(p, antecedent.conclusion, "modus ponens on an equation"))
      else
        Right(
          new Thm(
            union(equivalence.hypotheses, antecedent.hypotheses),
            q,
            Derivation.EqualityElimination(equivalence, antecedent)
          )
        )
    }

  /**
   * `G |- p` and `D |- q` give `(G - q), (D - p) |- p = q`
   *
   * This is where implication between propositions comes from, and with it the deduction theorem
   * once implication is defined.
   */
  def deductAntisym(left: Thm, right: Thm): Thm = {
    val hypotheses = union(
      left.hypotheses.filterNot(_ == right.conclusion),
      right.hypotheses.filterNot(_ == left.conclusion)
    )
    new Thm(
      hypotheses,
      equation(left.conclusion, right.conclusion),
      Derivation.Antisymmetry(left, right)
    )
  }

  /**
   * Replace free variables throughout a theorem, hypotheses included.
   *
   * Sound without a side condition, and without renaming anything: a free variable is a name and
   * a bound one is an index, so nothing being substituted can fall under a binder that binds it.
   */
  def inst(substitution: Map[FVar, Term], theorem: Thm): Either[KernelError, Thm] =
    for {
      hypotheses <- traverse(theorem.hypotheses)(Term.substitute(substitution, _))
      conclusion <- Term.substitute(substitution, theorem.conclusion)
    } yield new Thm(normalise(hypotheses), conclusion, Derivation.Instantiation(substitution, theorem))

  /**
   * Replace type variables throughout a theorem, hypotheses included.
   *
   * This can identify two free variables that differed only in their type. That is a
   * specialisation of a statement that already held for every value of both, so it is sound; see
   * [[Term.substituteTypes]].
   */
  def instType(substitution: Map[String, Type], theorem: Thm): Thm = {
    val hypotheses = theorem.hypotheses.map(Term.substituteTypes(substitution, _))
    new Thm(
      normalise(hypotheses),
      Term.substituteTypes(substitution, theorem.conclusion),
      Derivation.TypeInstantiation(substitution, theorem)
    )
  }

  /* ------------------------------------------------------- extending a theory */

  /**
   * Introduce `name` as an abbreviation for `definition`, and prove `|- name = definition`.
   *
   * Conservative, which is what the two conditions buy:
   *
   *  - the definition is closed, so the constant denotes one value rather than a value per
   *    assignment to a free variable;
   *  - every type variable in the definition occurs in its type, so instantiating the constant's
   *    type determines the definition completely. Without this a constant could be defined by a
   *    body mentioning a type variable its type does not, and two instantiations of it would be
   *    two different values under one name, which is a contradiction with an extra step.
   */
  def defineConstant(
    theory: Theory,
    name: String,
    definition: Term
  ): Either[KernelError, (Theory, Thm)] = {
    val free = Term.freeVariables(definition)
    val definitionType = Term.typeOf(definition)
    val escaping = Term.typeVariables(definition) -- Type.variables(definitionType)

    for {
      _ <- theory.checkTerm(definition)
      _ <- if (free.isEmpty) Right(()) else Left(DefinitionIsNotClosed(free.toSet[Term]))
      _ <- if (escaping.isEmpty) Right(()) else Left(TypeVariablesEscape(escaping))
      extended <- theory.declareConstant(name, definitionType)
      constant <- extended.constant(name, definitionType)
      // The constant this returns is the one the extended theory hands out, origin and all, so the
      // defining theorem is about the constant a caller will build from that theory and not about
      // one that merely shares its name. See `docs/adr/0008`.
      withOrigin = extended.copy(
        definitions = extended.definitions.updated(name, definition),
        origins = extended.origins.updated(name, definition)
      )
      identified <- withOrigin.constant(name, definitionType)
    } yield (
      withOrigin,
      new Thm(Nil, equation(identified, definition), Derivation.Definition(name, definition))
    )
  }

  /**
   * Assert `proposition` without proof, and record it in the theory.
   *
   * The only operation in the kernel that is not conservative, and named so that it reads as what
   * it is at the call site. Everything a system built on this can prove rests on the propositions
   * that went through here, and [[Theory.axioms]] is the list of them.
   */
  def assertAxiom(theory: Theory, proposition: Term): Either[KernelError, (Theory, Thm)] =
    for {
      _ <- theory.checkTerm(proposition)
      _ <- if (Term.isProposition(proposition)) Right(())
           else Left(NotAProposition(proposition, Term.typeOf(proposition)))
      // Closed, like a definition. An axiom with a free variable is a schema every instance of
      // which is asserted, and the way one arrives is a typo: the parser reads an unknown
      // letter-initial name as a variable, so `ng x` where `neg x` was meant states something
      // about an arbitrary function and prints indistinguishably from the axiom that was meant.
      _ <- if (Term.freeVariables(proposition).isEmpty) Right(())
           else Left(DefinitionIsNotClosed(Term.freeVariables(proposition).toSet[Term]))
    } yield (
      theory.copy(axioms = (theory.axioms :+ proposition).distinct),
      new Thm(Nil, proposition, Derivation.Axiom(proposition))
    )

  /**
   * A new type, in bijection with the part of an existing one that a predicate picks out.
   *
   * Transcribed by hand from HOL Light's `new_basic_type_definition`, following Harrison's account
   * and `fusion.ml`. `docs/adr/0006` records the decision, the alternatives rejected, and the
   * attacks this has to turn away; what follows is why each check is here rather than what each
   * one does.
   *
   * Given `P : A -> bool` and a theorem that something satisfies it, this declares a type operator
   * whose arity is the number of type variables in `P`, two constants between the new type and `A`,
   * and returns the two theorems that say they are a bijection onto `P`'s extension:
   *
   * {{{
   *   |- abs (rep a) = a
   *   |- P r <=> rep (abs r) = r
   * }}}
   *
   * **Nothing is asserted.** The new type is inhabited because a witness was supplied, and the two
   * theorems are the definition of the abstraction rather than assumptions about it, so
   * [[Theory.axioms]] does not move. That is the whole reason this is in the kernel: every
   * alternative reaches the same two theorems by asserting them.
   *
   * **The witness is a theorem, not an existential.** This kernel knows equality and nothing else,
   * so `?` is a definitional extension living above it and cannot appear in a primitive rule. A
   * caller holding `|- ?x. P x` eliminates it in the layer that has the connectives and hands the
   * witness down, which is where that reasoning belongs.
   *
   * **The witness itself appears in neither theorem**, and that is not an oversight. It is used to
   * establish that `P`'s extension is not empty and for nothing else, which is why a type variable
   * occurring in it but not in `P` cannot escape into the result: there is nowhere for it to go.
   * The arity is read from `P` alone, in a fixed order, so a caller does not choose it.
   *
   * **A check order that differs from upstream, deliberately.** HOL Light refuses the two constant
   * names before it declares the type operator, because `new_type` mutates a global and a later
   * failure would leave it behind. Here every step returns a new theory and a failed step discards
   * it, so nothing is left behind and the order is free; what it changes is which refusal a caller
   * hears when both the type name and `abs` are taken, and that is the whole of the difference.
   *
   * **The hypothesis check is the one that would be easy to leave out.** A witness holding under an
   * assumption would make the type inhabited under that assumption, while the theorems that come
   * back carry none: the assumption would be discharged into silence, and an empty predicate could
   * then be given a bijection with a type. `Theory.axioms` would still read as it did.
   */
  def defineType(
    theory: Theory,
    typeName: String,
    absName: String,
    repName: String,
    witness: Thm
  ): Either[KernelError, (Theory, (Thm, Thm))] = {
    val (hypotheses, conclusion) = (witness.hypotheses, witness.conclusion)

    for {
      _ <- if (hypotheses.isEmpty) Right(()) else Left(TheoremHasHypotheses(hypotheses))

      // The witness has to be a theorem of *this* theory. A `Theory` is a value here rather than
      // the single global one HOL Light has, so a theorem can be built against one signature and
      // handed to another, and stopping that is what [[Theory.checkTerm]] is for. Upstream has no
      // analogue and there was none to transcribe: with one global theory the constants of a
      // theorem are in the signature by construction. Without it, a predicate naming a constant
      // this theory does not declare defined a type whose characterising theorem the same theory
      // then refused as an axiom, which is an invariant broken rather than a falsehood proved.
      // After the hypothesis check, so that a witness with both faults is refused for the
      // assumption, which is the worse of the two.
      _ <- theory.checkTerm(conclusion)

      applied <- conclusion match {
        case App(predicate, argument) => Right((predicate, argument))
        case other => Left(NotAnApplication(other))
      }
      (predicate, argument) = applied

      free = Term.freeVariables(predicate)
      _ <- if (free.isEmpty) Right(()) else Left(DefinitionIsNotClosed(free.toSet[Term]))

      // Sorted, so that the arity and the order of the arguments are a function of the predicate
      // and not of the order a set happened to iterate in. Two runs of the same definition have to
      // produce the same type.
      parameters = Term.typeVariables(predicate).toList.sorted
      abstractType = TyApp(typeName, parameters.map(TyVar.apply))
      representingType = Term.typeOf(argument)

      withType <- theory.declareTypeOperator(typeName, parameters.length)
      withAbs <- withType.declareConstant(absName, Type.fun(representingType, abstractType))
      declared <- withAbs.declareConstant(repName, Type.fun(abstractType, representingType))

      // The predicate is what these two are: a second type defined over a different predicate gets
      // two constants of the same name that are not these, so theorems about the two types do not
      // combine. `docs/adr/0008` is the record, and the alternative is that
      // `|- abs (rep a) = a` from one of them chains with a characterisation from the other.
      extended = declared.copy(
        origins = declared.origins.updated(absName, predicate).updated(repName, predicate)
      )

      abs <- extended.constant(absName, Type.fun(representingType, abstractType))
      rep <- extended.constant(repName, Type.fun(abstractType, representingType))

      a = Term.variable("a", abstractType)
      r = Term.variable("r", representingType)

      absOfRep <- Term.app(rep, a).flatMap(Term.app(abs, _))
      repOfAbs <- Term.app(abs, r).flatMap(Term.app(rep, _))
      holds <- Term.app(predicate, r)
    } yield (
      extended,
      (
        new Thm(
          Nil,
          equation(absOfRep, a),
          Derivation.TypeDefinition(
            typeName,
            absName,
            repName,
            witness,
            Derivation.Half.AbstractionOfRepresentation
          )
        ),
        new Thm(
          Nil,
          equation(holds, equation(repOfAbs, r)),
          Derivation.TypeDefinition(
            typeName,
            absName,
            repName,
            witness,
            Derivation.Half.Characterisation
          )
        )
      )
    )
  }

  /* ------------------------------------------------------------------ internals */

  private def sidesOf(term: Term): Either[KernelError, (Term, Term)] =
    Term.destEq(term).toRight(NotAnEquation(term))

  /**
   * Build an equation between two terms already known to have the same type.
   *
   * Every use below has just taken the two sides out of an equation, or built them from one, so
   * the check inside [[Term.eq]] cannot fail. Reaching the other branch means a rule above
   * constructed something it should not have.
   */
  private def equation(lhs: Term, rhs: Term): Term =
    Term.eq(lhs, rhs) match {
      case Right(term) => term
      case Left(error) => throw new KernelInvariantViolation(error.message)
    }

  /* Reached from [[refl]] when a caller supplies a term that is not locally closed, and from a
   * rule that built something it should not have. The two are told apart by the message. */

  private def union(left: List[Term], right: List[Term]): List[Term] = normalise(left ++ right)

  private def normalise(hypotheses: List[Term]): List[Term] =
    hypotheses.distinct.sorted(using Term.ordering)

  private def traverse(
    terms: List[Term]
  )(f: Term => Either[KernelError, Term]): Either[KernelError, List[Term]] =
    terms.foldRight(Right(Nil): Either[KernelError, List[Term]]) { (term, acc) =>
      for {
        rest <- acc
        head <- f(term)
      } yield head :: rest
    }
}
