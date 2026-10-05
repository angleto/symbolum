package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.LinearFact.Kind

/**
 * Linear arithmetic: goals about `<` that follow from adding the hypotheses up.
 *
 * `!x y z. x < y /\ y < z ==> x < z` is transitivity, which is an axiom. `!x y. x < y ==> x + 1 <
 * y + 1` is not, and neither is `!x y z w. x < y /\ z < w ==> x + z < y + w`, and both come out of
 * the same procedure: move every inequality to the form `0 < e`, add up the ones that help, and
 * show by ring reasoning that the sum is the goal.
 *
 * == The asymmetry this is built on ==
 *
 * Finding which hypotheses to add is a search, and it is untrusted: it runs over linear forms
 * extracted from the terms, in ordinary arithmetic, with no theorem in sight. Checking is what
 * costs nothing, and it is where the kernel is: the chosen hypotheses are added with a derived
 * rule, and [[Ring]] proves that the sum is what the goal needed. A wrong answer from the search
 * makes the ring step fail, so the worst it can do is fail to find a proof.
 *
 * == What it decides ==
 *
 * The linear fragment, and it decides that fragment rather than a corner of it: hypotheses that are
 * strict inequalities, non-strict ones or equalities, and a conclusion of any of the three. Such an
 * implication is valid exactly when the goal's difference is a non-negative rational combination of
 * the hypotheses' differences plus a non-negative constant, or when the hypotheses cannot all hold
 * at once, and [[Farkas]] answers both questions with the same linear program. A multiplier is used
 * by proving the numeral positive and cancelling the common denominator at the end, both of which
 * are theorems in [[Order]], so `2 * x < 2 * y ==> x < y` is proved by multiplying through by two
 * rather than by halving anything.
 *
 * The shapes are not separate procedures. An equality hypothesis is weighed with either sign, since
 * what its multiplier multiplies is zero; an equality conclusion is bounded on both sides and
 * closed by antisymmetry, which is two runs of the same route; and a conjunctive conclusion is each
 * conjunct and then the introduction rule, which is the shape a corpus of measurements is written
 * in. What needs care is strictness: a combination weighing only non-strict facts proves nothing
 * strict, so `x <= y ==> x < y` is refused, and that refusal is what pins the distinction.
 *
 * == What it does not do ==
 *
 * It sees a linear form over atoms, and a product of two unknowns is one atom. What reaches past
 * that is the products, in two rounds and neither of them free: when the linear attempt fails the
 * facts are multiplied in pairs, and when the goal still names an atom no pair reached, those
 * pairs are multiplied by the facts once more. Nothing multiplies two products together, so degree
 * three is where it stops and `0 < w /\ 0 < x /\ 0 < y /\ 0 < z ==> 0 < w * x * y * z` is refused.
 * The refusal there names the atom and how many factors it has rather than asking for a
 * non-negative combination of four positives, which is not something anybody can write.
 *
 * The denominators it reads are the constant ones, and one reader in this file decides which: a
 * numeral, a negated one, an inverse of a non-zero numeral, and a quotient of two of those. So
 * `x / 3` and `x / (2 / 3)` are `x` at a coefficient, while `x / y` and `x / 0` are atoms: `inv 0`
 * is a term the theory says nothing about, and turning `x / y` into a coefficient would need
 * `~(y = 0)`, which is `Field`'s to charge for.
 *
 * And it is about the reals: over the integers `x < y` gives `x + 1 <= y`, which is false here, so
 * a goal about the integers is a different statement rather than a harder one. All three are shapes
 * it declines rather than shapes it gets wrong.
 */
final class Linarith private (
  val order: Order,
  private val moveRight: Kernel.Thm,
  private val moveLeft: Kernel.Thm,
  private val addPositive: Kernel.Thm,
  /**
   * The two bounds on the escalation, held here rather than read off the companion.
   *
   * They were constants the code reached for directly until 2026-09-11, which made them
   * unmeasurable: the card that opened them said a limit calibrated on two corpora that do not
   * touch it is calibrated on nothing, and the only way to find out what a limit cuts is to build
   * the same procedure with the limit somewhere else and ask the same goals. `LinarithLimitsSpec`
   * is that corpus and it exists because these are fields.
   *
   * [[Linarith.Facts]] and [[Linarith.Cubes]] are still where the chosen values and their arguments
   * live, and [[Linarith.construct]] uses them, so nothing that does not care has changed.
   */
  val factLimit: Int,
  val cubeLimit: Int
) {

  val reals: RealTheory = order.reals
  val ring: Ring = order.ring

  private val rules = reals.logic.rules

  /**
   * Prove a goal written in the notation of the theory THIS INSTANCE was built over, which need
   * not be the caller's.
   *
   * The text goes through `reals.proposition`, so the signature it is read against is
   * `reals.theory`. A letter-initial name that signature does not hold is not a syntax error
   * here: it is well-typed as a free variable. So a caller that hands this a text written in its
   * own development's notation is answered `Right`, with no hypotheses, by a theorem about a
   * variable rather than about its constant, and the conclusion PRINTS as the text it wrote,
   * because a variable is printed no differently from a constant. Comparing the conclusion
   * against the same text parsed again does not separate the two readings either, since that
   * parse reads the name the same way. What separates them is whether the name is in
   * `reals.theory.constants`.
   *
   * Nothing catches it because nothing is unsound: a free variable is instantiable, so the
   * theorem is true of every instance, the intended constant included. It is simply not the
   * claim that was asked for, and the mismatch surfaces later, wherever that theorem meets a
   * rule expecting one stated over the caller's own constants.
   *
   * Handing it a better theory is not the fix, because for a link in the chain the order is
   * structural: a development constructs its Linarith before it declares anything.
   * `Limit.construct` builds one over `magnitude.order`, so `converges` and `lim` are outside it
   * by construction and no argument could have put them in. A goal naming anything of the
   * caller's own is parsed in the caller's signature and handed to the `Term` overload below,
   * which is what `Limit` already does for every goal of its that mentions `Sum`.
   *
   * `LinarithSpec` holds the reading and the constant check that separates the two.
   */
  def prove(text: String): Either[LogicError, Kernel.Thm] =
    reals.proposition(text).flatMap(prove)

  /**
   * Prove `!vars. h1 /\ ... /\ hn ==> c`, or a goal with no hypotheses at all.
   *
   * The antecedents may equally be curried, `h1 ==> ... ==> hn ==> c`, and the mixed shape is
   * read too: `split` peels every antecedent rather than one, which is what `CurriedGoalSpec`
   * exists for and what lets this entry point be handed the statements `Order` writes its own
   * lemmas in. The choice is the caller's and it is not free, because what comes back keeps the
   * shape that was asked for: the conjoined goal wants a `conjIntro` and one `mp`, the curried
   * one wants an `mp` per antecedent, and assembling for the wrong one is refused by `Rules.mp`
   * rather than here.
   *
   * The quantifiers come off, the antecedent is assumed and taken apart, the search picks which
   * of its parts to add, and the result is discharged and closed again. What comes back is checked
   * against the goal as stated: a version of this file rebuilt the antecedent right-nested and
   * returned, as a success, a theorem about a conjunction the goal did not contain. An audit
   * found it, and the check is what makes that class of mistake a `Left` rather than a wrong
   * answer.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      shape = split(stripped._2)
      proved <- proveBody(shape)
      general <- generalise(proved, stripped._1)

      // The conclusion was compared with the goal from the start, and the HYPOTHESIS LIST was not.
      // An assembly defect that fails to discharge an assumption returns `h |- goal` where the
      // caller expects `|- goal`, and a caller that reads the conclusion and ignores the turnstile
      // cannot tell the two apart. That is exactly the failure `Field.conditions` exists to make
      // visible, and this procedure had no equivalent: it charges nothing by design, so a
      // hypothesis on the way out is a defect and never a price.
      //
      // Named by an audit on 2026-09-10 as the narrow hazard that survives the argument for why the
      // file's length is not one. It costs a comparison against the empty list.
      result <-
        if (general.hypotheses.nonEmpty)
          LogicError.lift(Left(TheoremHasHypotheses(general.hypotheses)))
        else if (general.conclusion == goal) Right(general)
        else Left(NotOfForm("the goal as stated", general.conclusion))
    } yield result

  /**
   * Which of a goal's hypotheses the proof actually rests on, and with what weight.
   *
   * A sequent carries the premises that were assumed rather than the ones that were needed, which
   * is an upper bound and the known limit of using hypotheses as a domain model: a theorem can
   * carry a premise its derivation never touched. Here the bound is exact, because the certificate
   * names its own support: a hypothesis weighed by zero took no part in the proof, and the ones
   * left are what the conclusion rests on.
   *
   * That is the diagnostic half of this procedure and the one an article wants. Told that five
   * premises give a conclusion, the useful answer is which three of them did, and this is that
   * answer for the linear fragment.
   *
   * The theorem is built first and thrown away, so a goal that does not follow gets a refusal here
   * rather than a list of weights for a proof nobody has.
   *
   * The premises come back as the procedure sees them, which for a goal with leading quantifiers
   * means with the variables it opened them into rather than the names in the source: bound
   * variables have no names in a term at all. A goal written with free variables, which is what a
   * claim about named quantities is, comes back in its own words.
   */
  def support(text: String): Either[LogicError, Linarith.Support] =
    reals.proposition(text).flatMap(support)

  /** The same, for a goal already read. */
  def support(goal: Term): Either[LogicError, Linarith.Support] =
    for {
      _ <- prove(goal)
      stripped <- Logic.stripForall(goal)
      shape = split(stripped._2)
      written <- traverse(shape.hypotheses)(LinearFact.of(reals, _))

      // The squares are carried here and reported BESIDE the hypotheses, which is
      // `docs/adr/0032` point 4 and is two decisions rather than one. Carried, because the
      // certificate this rebuilds has to be one the proof could have used: a goal settled with a
      // completed square has none over the hypotheses alone, and without them this would refuse a
      // goal `prove` has just proved, with the message below saying exactly that.
      //
      // Reported, and in a field of their own. Among the hypotheses they would be quiet and
      // wrong, since the question this answers is which of the goal's OWN premises it rests on
      // and nobody wrote a square; dropped entirely they would make a proof that spent one report
      // an empty list, which reads as "no hypothesis was needed" and is indistinguishable from
      // the answer for a goal that needed none. The second field is what tells those two apart,
      // and it is why this returns a [[Linarith.Support]] rather than the bare vector it returned
      // until 2026-09-18.
      completed = squares(shape.conclusion, written)
      facts = written ++ completed.map(_._1)

      certificate <- LinearForm.goal(reals, shape.conclusion) match {
        case Some((form, strict)) =>
          Certificate.find(facts, form, strict)
            .orElse(Certificate.find(facts, LinearForm.zero, strict = true))
            .toRight(NotOfForm("a certificate for a goal that was just proved", shape.conclusion))

        case None =>
          Certificate.find(facts, LinearForm.zero, strict = true)
            .toRight(NotOfForm("a certificate for a goal that was just proved", shape.conclusion))
      }
      // The multipliers index into the pool in the order it was built, which is the hypotheses
      // and then the squares, so the split is `written.length` and not a search for which is
      // which. `LinearFact.of` is applied to the hypotheses in order and `completed` is appended
      // to that, which is the same construction `proveBody` gives the certificate.
      weights = certificate.multipliers
      spentOnHypotheses = shape.hypotheses
        .zip(weights)
        .collect { case (hypothesis, weight) if weight != 0 => (hypothesis, weight) }
      spentOnSquares = completed
        .map(_._2.conclusion)
        .zip(weights.drop(shape.hypotheses.length))
        .collect { case (square, weight) if weight != 0 => (square, weight) }
    } yield Linarith.Support(spentOnHypotheses, spentOnSquares)

  /* -------------------------------------------------------------------- proof */

  /**
   * A goal with its quantifiers off: the antecedents as written, their conjuncts, the consequent.
   *
   * **Antecedents, plural, since 2026-09-10.** This peeled exactly one, so
   * `!x y. 0 < x /\ 0 < y ==> 0 < x + y` was decided in milliseconds and
   * `!x y. 0 < x ==> 0 < y ==> 0 < x + y` was not read at all. They are the same statement, and the
   * second is the shape **this repository writes its own lemmas in**: `Order.addPositive` is
   * literally the second one, and `Order.scala` has fifty-three occurrences of `==>`. The entry
   * point could not be handed the statements of the theorems standing beside it.
   *
   * `hypotheses` is the conjuncts of every antecedent in order, and `assumeAll` produces the
   * assumed theorems in that same order, because the certificate's multipliers index into it.
   */
  private final case class Shape(
    antecedents: Vector[Term],
    hypotheses: Vector[Term],
    conclusion: Term
  )

  private def proveBody(shape: Shape): Either[LogicError, Kernel.Thm] =
    for {
      facts <- traverse(shape.hypotheses)(LinearFact.of(reals, _))
      assumed <- assumeAll(shape.antecedents)

      // `read` before `naming`, so that a goal whose degree is out of reach keeps the message that
      // names the degree: `naming` overrides whatever it is handed when it has something specific
      // to say, and what it has to say there is that the goal was NOT decided.
      proved <- (attempt(facts, assumed, shape.conclusion) match {
        case Right(theorem) => Right(theorem)
        case Left(refusal) => byRefutation(facts, assumed, shape.conclusion, refusal)
      }).left.map(read(shape, _)).left.map(naming(facts, shape.conclusion, _))

      // Innermost first, so that `p ==> q ==> r` is rebuilt in the order it was written. Getting
      // this backwards would produce a theorem about a different statement, and `prove` compares
      // what it built against the goal for exactly that reason.
      discharged <- shape.antecedents.foldRight(Right(proved): Either[LogicError, Kernel.Thm]) {
        (antecedent, acc) => acc.flatMap(rules.disch(antecedent, _))
      }
    } yield discharged

  /**
   * A refusal with the obstacle named, when the obstacle is a degree the products do not reach.
   *
   * The default says the goal is not a non-negative combination of the hypotheses. That is true of
   * every goal this refuses and it is what a caller hears when nothing more specific is available,
   * which is the right default and the wrong answer for a goal whose only problem is its degree:
   * `0 < w /\ 0 < x /\ 0 < y /\ 0 < z ==> 0 < w * x * y * z` is not a claim anybody can restate as
   * a combination of those four hypotheses, and telling them to try is telling them to fail again.
   *
   * The products reach degree three, so an atom of four factors is out and the refusal says which
   * atom and how many factors it has. That is the same discipline as [[LinearForm.unreadable]], one
   * limit further along: a caller repairs one thing at a time and cannot repair a thing nobody
   * named.
   *
   * **And there are two obstacles here rather than one, which is what `docs/adr/0032` records and
   * what this said the wrong one of until 2026-09-18.** The pool the products are built from is
   * the goal's hypotheses and nothing else, so a goal with none has an empty pool, and an empty
   * set has no products at any degree. Telling that caller the hypotheses multiplied reach three
   * is a true sentence about a set with nothing in it, and it sends them to restate a goal for a
   * degree when what is missing is a premise. So the message splits on whether the pool is empty,
   * and the degree is named only where there was something to multiply.
   *
   * The same discipline again, and the reason it is worth the branch rather than a longer
   * sentence covering both: a reader acts on the first thing a refusal names, and "degree" and
   * "no hypotheses" send them to different places.
   *
   * **A third obstacle is not a product at all.** When every product out of reach is one unknown
   * times itself, the squares cover all of them, and what stops the goal is what it asks beyond its
   * squares: `x * x >= 1` less the square `x * x` is `-1 >= 0`. The refusal names that remainder
   * rather than a product, since the product it named until 2026-09-28 was one the procedure had
   * already handled.
   */
  private def naming(
    facts: Vector[LinearFact],
    conclusion: Term,
    refusal: LogicError
  ): LogicError = {
    val base = facts.flatMap(_.form.atoms).toSet
    val pairs = for { left <- base; right <- base } yield LinearForm.productAtom(reals, left, right)
    val triples =
      for { pair <- pairs; right <- base } yield LinearForm.productAtom(reals, pair, right)
    val reachable = base ++ pairs ++ triples
    val goalAtoms = LinearForm.goal(reals, conclusion).map(_._1.atoms).getOrElse(Set.empty)

    // Only a product, and only when nothing more specific was already said. An atom of one factor
    // out of reach is `inv x` or a quotient, which [[LinearForm.unreadable]] names better and
    // by its own name, and a message about its degree would be both wrong and a step backwards
    // from one that was right.
    //
    // The `> 1` is also why neither of the two refusals below that print a count ever says `a
    // product of 1 unknowns`:
    // the atom they name is the one this find selected, so the number they print is at least two
    // and no counter is wanted. Both messages read the same `factorsOf` and both are covered by
    // the one guard, which is worth saying because there is one guard and two sentences.
    //
    // Which atom to name, when several are out of reach, is the one the procedure is furthest from.
    // An atom of more than two factors comes first, since neither source of squares reaches past
    // degree two and every other obstacle is secondary to it. Then a product of different unknowns
    // before a square of one: naming `x * x` in `x * x + y * y >= 2 * (x * y)`, which is what term
    // order did until the verification of card `bacfaba5` on 2026-09-26, sent the caller to repair
    // the half the procedure had already handled. A square is found last and is never named: when
    // it is all there is, the refusal below names what the goal asks beyond the squares instead.
    def isSquare(atom: Term): Boolean = LinearForm.factorsOf(atom) match {
      case Vector(left, right) => left == right
      case _ => false
    }
    val products = goalAtoms
      .diff(reachable)
      .toVector
      .sorted(using Term.ordering)
      .filter(atom => LinearForm.factorsOf(atom).length > 1)
    val outOfReach = products
      .find(atom => LinearForm.factorsOf(atom).length > 2)
      .orElse(products.find(atom => !isSquare(atom)))
      .orElse(products.headOption)

    // A certificate that was found means the search had what it needed, so a sentence about the
    // degree would replace the one true thing known with a false one.
    val found = refusal match {
      case _: NotRebuilt => true
      case _ => false
    }

    // What the goal asks beyond its own squares: its form less every square the decomposition finds
    // in it, which is exact, so what is left is the part no square covers. For `x * x >= 1` it is
    // `-1 >= 0`, and the constant is the obstacle.
    def beyondSquares: Option[String] =
      LinearForm.goal(reals, conclusion).flatMap { case (form, strict) =>
        val rest = SumOfSquares.of(form, LinearForm.factorsOf).foldLeft(form) { (left, square) =>
          left + -square.base.times(square.base, LinearForm.productAtom(reals, _, _)).scaled(square.weight)
        }
        termOf(rest).toOption.map(term => s"${reals.show(term)} ${if (strict) ">" else ">="} 0")
      }

    outOfReach match {
      case _ if found => refusal

      // Every product out of reach is one unknown times itself, so the order above had nothing
      // better to name, and a square is what both sources of squares cover: naming it sent the
      // caller to repair the half the procedure had handled, measured on `x * x >= 1` on 2026-09-28
      // (card `9fefbf75`). What is missing is what the goal asks once its squares are completed, and
      // whether there were hypotheses to give it decides how the sentence ends.
      case Some(atom) if isSquare(atom) && LinearForm.obstacleIn(reals, conclusion).isEmpty =>
        beyondSquares.fold(refusal) { rest =>
          NotOfForm(
            "a goal its squares settle: every product in it is one unknown times itself, which " +
              s"the completed squares cover, and what it asks beyond them is $rest, " +
              (if (facts.isEmpty) "which no square gives and no hypothesis is there to give"
               else "which no non-negative combination of its hypotheses and their products gives"),
            conclusion
          )
        }

      // Without hypotheses the squares are the only facts there are, so the sentence says what they
      // reach. It said until `docs/adr/0056` that the only one was a square completed over one
      // unknown times itself, which stopped being true in the change that made `x * y` reachable.
      case Some(atom) if LinearForm.obstacleIn(reals, conclusion).isEmpty && facts.isEmpty =>
        val degree = LinearForm.factorsOf(atom).length
        NotOfForm(
          s"a goal with a hypothesis, or one a sum of squares settles: ${reals.show(atom)} is a " +
            s"product of $degree unknowns, and this goal has no hypotheses at all, so the pool " +
            "the products are built from is empty and no degree of them exists. Without " +
            "hypotheses the only facts available are squares of linear forms over the goal's " +
            "atoms, and " +
            (if (degree > 2) "those reach degree two"
             else "this goal's quadratic part is not a sum of them with what its strictness needs"),
          conclusion
        )

      case Some(atom) if LinearForm.obstacleIn(reals, conclusion).isEmpty =>
        NotOfForm(
          s"a goal whose degree the products reach: ${reals.show(atom)} is a product of " +
            s"${LinearForm.factorsOf(atom).length} unknowns, and the hypotheses " +
            "multiplied reach three",
          conclusion
        )
      case _ => refusal
    }
  }

  /**
   * The conclusion from the facts as they stand, and then from the facts times each other.
   *
   * Two of the three attempts a goal gets, in the order of what they cost. [[byRefutation]] is the
   * third and calls this one, which is why it is not part of it: a case of a refutation is a fact
   * set with one more hypothesis in it, and it is settled the ordinary way or not at all.
   */
  private def attempt(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    prove(facts, assumed, conclusion) match {
      case Right(theorem) => Right(theorem)
      case Left(refusal) =>
        bySquares(facts, assumed, conclusion, refusal) match {
          case Right(theorem) => Right(theorem)
          case Left(carried) => byProducts(facts, assumed, conclusion, carried)
        }
    }

  /**
   * The squares a goal's own quadratic atoms make available, as facts with the theorems for them.
   *
   * **This is the one source of facts here that is not generated by the goal's text**, and it is
   * what `docs/adr/0032` decides. Everything else in this procedure multiplies what it was handed:
   * [[productsOf]] pairs the hypotheses, [[byCubes]] multiplies those pairs by the hypotheses
   * again, and [[fromCase]] and [[byDenial]] add a disjunct or a denial read off the goal. A goal
   * with **no hypotheses** therefore has an empty pool, and an empty pool has no products at any
   * degree: `a * (2 - a) <= 1` was refused for that reason and not for a degree, which is the
   * measurement that record is taken with.
   *
   * What it emits comes from two sources, and each fact is `Order.SQUARE_NONNEG` at one argument.
   * The first completes the square over one unknown: over an atom `x * x` carrying `alpha` and the
   * atom `x` carrying `beta` in the same form, `0 <= (x + beta / (2 * alpha)) * (x + ...)`. The
   * second, since `docs/adr/0056`, is [[SumOfSquares]]: the form's Gram matrix over the unknowns and
   * the constant, decomposed in exact arithmetic, which reaches the cross terms the first cannot, so
   * `x * x + y * y >= 2 * (x * y)` is settled by `0 <= (x - y) * (x - y)`. Both are linear algebra
   * rather than a search, because over monomials of degree one the Gram matrix is unique; what would
   * want a semidefinite program is a degree past two, and neither source reaches it.
   *
   * **Nothing has to normalise the theorem before it is read.** [[LinearForm.of]] multiplies a
   * product of two unknowns out rather than keying it whole, so `(x + c) * (x + c)` arrives as
   * `x * x` at one, `x` at `2 * c` and the constant `c * c`, over the very atom keys the goal
   * already uses. That is the half of the design that makes this small, and it is a property of
   * that reader rather than of this function.
   *
   * The forms looked at are the goal's and the hypotheses', because a square is worth having
   * wherever a quadratic atom appears and the completion is decided by the coefficients around it.
   * A candidate that cannot be built is dropped rather than reported: it is an extra fact nobody
   * asked for, so failing to make one is not a refusal of the goal.
   */
  private def squares(
    conclusion: Term,
    facts: Vector[LinearFact]
  ): Vector[(LinearFact, Kernel.Thm)] = {
    val forms = LinearForm.goal(reals, conclusion).map(_._1).toVector ++ facts.map(_.form)

    val completions = for {
      form <- forms
      atom <- form.atoms.toVector.sorted(using Term.ordering)
      factors = LinearForm.factorsOf(atom)
      if factors.length == 2 && factors(0) == factors(1)
      leading = form.at(atom)
      if !leading.isZero
    } yield (factors(0), form.at(factors(0)) / (leading + leading))

    val completed = completions.distinct.map { case (base, shift) =>
      if (shift.isZero) Right(base)
      else Linarith.constant(reals, shift).flatMap(Linarith.sum(reals, base, _))
    }

    val summed = forms
      .flatMap(SumOfSquares.of(_, LinearForm.factorsOf))
      .map(_.base)
      .distinct
      .map(termOf)

    val built = (completed ++ summed).flatMap { argument =>
      (for {
        term <- argument
        lemma <- order.squareNonNegative
        instance <- specialise(lemma, List(term))
        fact <- LinearFact.of(reals, instance.conclusion)
      } yield (fact, instance)).toOption
    }

    built.distinctBy(_._1.form)
  }

  /**
   * A linear form as a term the form reader reads back as that form: each unknown at its
   * coefficient, in the order the atoms sort in, and the constant last when it is not zero.
   *
   * A negative coefficient after the first is written as a subtraction, so the base of the square
   * `x * x + y * y >= 2 * (x * y)` is settled with prints as `x - y` and not as `x + --1 * y`. That
   * is for the reader of `Linarith.Support.squares`, which carries this term; the form reader
   * gives the same form back either way.
   */
  private def termOf(form: LinearForm): Either[LogicError, Term] = {
    def scaled(coefficient: Rational, atom: Term): Either[LogicError, Term] =
      if (coefficient == Rational.one) Right(atom)
      else Linarith.constant(reals, coefficient).flatMap(Linarith.product(reals, _, atom))

    val parts = form.atoms.toVector.sorted(using Term.ordering).map(atom => (form.at(atom), Option(atom))) ++
      (if (form.constant.isZero) Vector.empty else Vector((form.constant, None)))

    def part(coefficient: Rational, atom: Option[Term]): Either[LogicError, Term] =
      atom.fold(Linarith.constant(reals, coefficient))(scaled(coefficient, _))

    parts.headOption match {
      case None => Linarith.constant(reals, Rational.zero)
      case Some((coefficient, atom)) =>
        parts.tail.foldLeft(part(coefficient, atom)) { case (acc, (next, nextAtom)) =>
          if (next.isNegative)
            acc.flatMap(left => part(-next, nextAtom).flatMap(Linarith.difference(reals, left, _)))
          else acc.flatMap(left => part(next, nextAtom).flatMap(Linarith.sum(reals, left, _)))
        }
    }
  }

  /**
   * The goal once more with those squares in the pool, and the refusal from before if it fails.
   *
   * Cheaper than the products, which is why it runs first: one specialisation per quadratic atom
   * against a schedule that is quadratic and then cubic in the pool. A goal the plain linear
   * attempt settles never builds one of these, exactly as a goal the squares settle never builds a
   * pair.
   */
  private def bySquares(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term,
    refusal: LogicError
  ): Either[LogicError, Kernel.Thm] = {
    val completed = squares(conclusion, facts)

    if (completed.isEmpty) Left(refusal)
    else withExtra(facts, assumed, completed, conclusion).left.map(kept(_, refusal))
  }

  /**
   * The conclusion by ruling out the other two ways its relation could fall.
   *
   * The move that was missing until 2026-09-10, and the one a consumer met first. `nlinarith`
   * multiplies over the hypotheses **and the negation of the goal**; this multiplied over the
   * hypotheses alone, so a whole family stayed out of reach for a reason that had nothing to do
   * with the family: from `n * d = b` with `n` and `b` positive it does not follow *linearly* that
   * `d` is positive, and it does follow at once from `d <= 0`, which is the thing nobody had
   * assumed. Measured on the smallest case, which is that one.
   *
   * The negation is not assumed by a classical step, and there is none to use here: it comes from
   * `LT_TOTAL`, which is one of the sixteen. `a < b` or `a = b` or `b < a`, and each case is then
   * an ordinary run of [[attempt]] over the facts with that case added. So this reaches no axiom
   * the procedure did not already reach and needs no lemma that did not exist.
   *
   * **A case is settled or the whole thing is refused**, and the refusal reported is the one from
   * before any of this. A caller repairs what it wrote, and it did not write these three cases.
   *
   * It is last because it is the most expensive: three branches, each of which may build the
   * products again. A goal decided by either of the two cheaper routes never reaches it.
   */
  private def byRefutation(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term,
    refusal: LogicError
  ): Either[LogicError, Kernel.Thm] =
    Order.destOrder(reals, conclusion) match {
      case None => Left(refusal)

      case Some((left, right, strict)) =>
        val attempted = for {
          total <- reals.law("LT_TOTAL")
          cases <- specialise(total, List(left, right))

          split <- reals.logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a three-way disjunction", cases.conclusion))
          (isLess, rest) = split

          tail <- reals.logic
            .destDisj(rest)
            .toRight(NotOfForm("a two-way disjunction", rest))
          (isEqual, isGreater) = tail

          lessCase <- fromLess(isLess, conclusion, strict)
          equalCase <- fromEqual(isEqual, facts, assumed, conclusion, strict)
          greaterCase <- fromCase(isGreater, facts, assumed, conclusion)

          assumedRest <- LogicError.lift(Kernel.assume(rest))
          upper <- rules.disjElim(assumedRest, equalCase, greaterCase)
          result <- rules.disjElim(cases, lessCase, upper)
        } yield result

        attempted.left.map(kept(_, refusal))
    }

  /**
   * Which refusal to report when an escalation failed after the first attempt already had.
   *
   * The rule this file has always followed is that a caller repairs what it wrote, and it did not
   * write the product facts or the three cases of the split, so the refusal reported is the one
   * from before any of them. The exception was written as `case bound: BoundReached` at two sites
   * with a comment either side saying why: "I stopped" is not a fact about the goal, and reporting
   * it as one sends a caller in the opposite direction.
   *
   * It is the standing that decides, now that there is one, and the generalisation is not free: a
   * rewriting that ran out of steps inside an escalation is `NotNormalised` rather than a bound, and
   * under the old spelling it was swallowed into a refusal that now claims to be a decision. An
   * escalation that stopped means the procedure did not finish, whichever of the two stopped it.
   */
  private def kept(escalation: LogicError, refusal: LogicError): LogicError =
    if (surfaces(escalation)) escalation else refusal

  /**
   * Whether an escalation's failure is reported in place of the refusal from before it.
   *
   * Two kinds are, and they share the reason: neither is a fact about the goal. A search that
   * stopped is the one [[kept]] was written for. A certificate that was found and not rebuilt is
   * the second, since 2026-09-25: the escalation's search said the goal follows, so reporting the
   * earlier `DoesNotFollow` in its place tells a caller the goal was decided against when its proof
   * had just been found, and nothing a caller wrote is at fault either.
   */
  private def surfaces(escalation: LogicError): Boolean =
    escalation.standing.stoppedShort || (escalation match {
      case _: NotRebuilt => true
      case _ => false
    })

  /**
   * A certificate's rebuilding, with a refusal of it reported as the procedure's own failure.
   *
   * Every step after [[Certificate.find]] is assembly: the search has said the goal follows, and a
   * refusal from here on is the kernel not accepting what was assembled, whatever the step that
   * refused says of itself. Wrapped once, at the two places a certificate is rebuilt, so a
   * `NotEqualTo` from the final RING check cannot reach a caller as a decision about the goal.
   */
  private def rebuilt(conclusion: Term, rebuilding: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    rebuilding.left.map(NotRebuilt(conclusion, "LINARITH", _))

  /** The case where the goal's own relation holds strictly, which proves it either way it is put. */
  private def fromLess(
    disjunct: Term,
    conclusion: Term,
    strict: Boolean
  ): Either[LogicError, Kernel.Thm] =
    for {
      assumed <- LogicError.lift(Kernel.assume(disjunct))
      result <-
        if (strict) Right(assumed)
        else
          for {
            sides <- Order.destLess(reals, disjunct)
            lemma <- order.leOfLt
            instance <- specialise(lemma, List(sides._1, sides._2))
            weakened <- rules.mp(instance, assumed)
          } yield weakened
      _ <- if (result.conclusion == conclusion) Right(()) else Left(NotOfForm("the goal", result.conclusion))
    } yield result

  /**
   * The case where the two sides are equal.
   *
   * For a non-strict goal it is `LE_OF_EQ` and nothing else has to be searched for. For a strict
   * one the equality has to contradict the facts, so it joins them and the ordinary attempt runs.
   */
  private def fromEqual(
    disjunct: Term,
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term,
    strict: Boolean
  ): Either[LogicError, Kernel.Thm] =
    if (strict) fromCase(disjunct, facts, assumed, conclusion)
    else
      for {
        equal <- LogicError.lift(Kernel.assume(disjunct))
        sides <- Term.destEq(disjunct).toRight(NotOfForm("an equation", disjunct))
        lemma <- order.leOfEq
        instance <- specialise(lemma, List(sides._1, sides._2))
        weakened <- rules.mp(instance, equal)
        result <-
          if (weakened.conclusion == conclusion) Right(weakened)
          else fromCase(disjunct, facts, assumed, conclusion)
      } yield result

  /** One case of the split: the disjunct joins the facts, and the goal is attempted again. */
  private def fromCase(
    disjunct: Term,
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      fact <- LinearFact.of(reals, disjunct)
      hypothesis <- LogicError.lift(Kernel.assume(disjunct))
      result <- attempt(facts :+ fact, assumed :+ hypothesis, conclusion)
    } yield result

  /**
   * One conclusion, by whichever of the four routes fits its shape.
   *
   * An inequality is a combination of the hypotheses, or it follows from their being impossible.
   * An equality is neither: it is proved by bounding it on both sides and appealing to
   * antisymmetry, which is two runs of the first route and the one place this procedure asks the
   * same question twice. A conjunction is each conjunct and then the introduction rule. Anything
   * else can only be the second route.
   */
  private def prove(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    reals.logic.destConj(conclusion) match {
      case Some((left, right)) => byConjunction(facts, assumed, left, right)

      case None =>
        LinearForm.goal(reals, conclusion) match {
          case Some((form, strict)) =>
            Certificate.find(facts, form, strict) match {
              case Some(certificate) => rebuilt(conclusion, fromCertificate(certificate, facts, assumed, conclusion))
              case None => fromContradiction(facts, assumed, conclusion)
            }

          case None =>
            Term.destEq(conclusion) match {
              case Some((left, right)) if Term.typeOf(left) == Real.realType =>
                byAntisymmetry(facts, assumed, left, right)

              case _ =>
                reals.logic.destNot(conclusion) match {
                  case Some(denied) => byDenial(facts, assumed, denied, conclusion)
                  case None => fromContradiction(facts, assumed, conclusion)
                }
            }
        }
    }

  /**
   * `~p`, by assuming `p` and finding the hypotheses impossible with it.
   *
   * The fifth route, added on 2026-09-10. `!x. 0 < x ==> ~(x = 0)` is a fact this development has
   * as a lemma and could not decide as a goal, and the same is true of every claim whose conclusion
   * is a denial: the reader fell through to the contradiction search, which was asked for `~(x = 0)`
   * itself and could make nothing of it.
   *
   * No new lemma. `p` joins the facts, falsity is what the search is asked for, and `notIntro`
   * discharges. That is the same shape as [[byRefutation]] one rule along, and it reaches no axiom
   * the procedure did not already reach.
   *
   * The refusal reported is the search's, not a complaint about the shape: a denial the facts do
   * not force is a goal that does not follow, and saying so is the honest answer. That sentence was
   * here before the type could carry it, and the refusal it described was a `NotOfForm`; it is a
   * `DoesNotFollow` now, restated against the denial.
   */
  private def byDenial(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    denied: Term,
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      fact <- LinearFact.of(reals, denied)
      hypothesis <- LogicError.lift(Kernel.assume(denied))

      // The inner search is for falsity, so a decision arrives naming falsity as the goal, and
      // falsity is a term the caller never wrote. What finished is a search about the denial: no
      // combination of the premises and `denied` reaches a contradiction, so `~denied` does not
      // follow. Restated here rather than at the boundary, because only this route knows that the
      // goal the caller asked about is not the goal the search was given.
      absurd <- attempt(facts :+ fact, assumed :+ hypothesis, reals.logic.falsity).left.map {
        case DoesNotFollow(_, procedure) => DoesNotFollow(conclusion, procedure)
        case NotRebuilt(_, procedure, reason) => NotRebuilt(conclusion, procedure, reason)
        case other => other
      }
      result <- rules.notIntro(denied, absurd)
      _ <-
        if (result.conclusion == conclusion) Right(())
        else Left(NotOfForm("the denial as stated", result.conclusion))
    } yield result

  /**
   * The same goal again, with the products of the hypotheses added as facts of their own.
   *
   * The move `nlinarith` makes over `linarith`, and the reason `0 < x /\ 0 < y ==> 0 < x * y` is
   * refused without it although it is an axiom: the linear form reads `x * y` as an atom, and no
   * combination of forms over `x` and `y` reaches an atom neither of them mentions. Multiplying the
   * pair puts that atom into a hypothesis, and the ordinary certificate search does the rest.
   *
   * **Second, and only when the first attempt failed.** The pairs are quadratic in the number of
   * hypotheses, so the linear program grows and the simplex pays for it; a goal that was decided
   * without them still costs what it cost. That is what `nlinarith` does relative to `linarith`, and
   * the measurement is in the certificate-search section of `docs/evaluation.md`.
   *
   * **The refusal reported is the first one.** The second attempt refuses about a fact set the
   * caller never wrote, and a caller repairs what it wrote.
   *
   * Nothing here can make the procedure wrong. A manufactured fact is a theorem like any other, and
   * the ring step still checks the combination against the goal, so a product that helps nothing
   * costs a refusal.
   */
  private def byProducts(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term,
    refusal: LogicError
  ): Either[LogicError, Kernel.Thm] =
    pairingPool(facts, assumed) match {
      case Left(reason) => Left(kept(reason, refusal))

      case Right((pool, theorems)) =>
        productsOf(pool, theorems, upToPairs(pool.length)) match {
          case Left(reason) => Left(kept(reason, refusal))
          case Right(extra) if extra.isEmpty => Left(refusal)
          case Right(extra) =>
            withExtra(facts, assumed, extra, conclusion) match {
              case Right(theorem) => Right(theorem)

              // A round that stopped survives the swallowing [[kept]] describes, and there is
              // nothing further to try when it does: the pairs are already too many, and the cubic
              // round starts from them. A certificate the pairs found and could not rebuild
              // survives it for the reason [[surfaces]] gives, and the cubes are not tried over it:
              // what failed is the rebuilding, and a larger search would only find more to rebuild.
              case Left(surfaced) if surfaces(surfaced) =>
                Left(surfaced)

              case Left(_) =>
                val missing = unreached(facts, extra.map(_._1), conclusion)
                if (missing.isEmpty) Left(refusal)
                else byCubes(facts, assumed, pool, theorems, extra, conclusion, missing, refusal)
            }
        }
    }

  /** Every unordered pair of a pool's indices, a fact with itself included. */
  private def upToPairs(size: Int): Vector[(Int, Int)] =
    for {
      left <- (0 until size).toVector
      right <- (left until size).toVector
    } yield (left, right)

  /**
   * The atoms the goal names that neither the hypotheses nor their pairwise products reach.
   *
   * The gate on the cubic round, and the whole of what keeps it affordable. A goal whose atoms are
   * all reached has nothing to gain from a deeper product: a certificate is a combination over
   * columns, and a column nothing needs is a column nothing uses. A chain of twelve linear
   * hypotheses has an empty answer here and never builds a cube; a goal writing `r * e * d` has
   * that atom in it, since no pair of the three hypotheses produces a product of three factors.
   *
   * Measured, on a chain of twelve, which is the size of a real goal: a refusal costs 32 ms with
   * this gate and 2918 ms without it. The goals that want the round pay for it and nothing else
   * does.
   */
  private def unreached(
    facts: Vector[LinearFact],
    products: Vector[LinearFact],
    conclusion: Term
  ): Set[Term] = {
    val reached = facts.flatMap(_.form.atoms).toSet ++ products.flatMap(_.form.atoms).toSet
    LinearForm.goal(reals, conclusion).map(_._1.atoms).getOrElse(Set.empty).diff(reached)
  }

  /**
   * The cubic candidates worth manufacturing: the ones that reach an atom the goal asked for.
   *
   * Everything else is a column the simplex would carry and could not use, and a theorem built for
   * one is a theorem built for nothing. The form is computed without deriving anything, which is
   * what makes the filter cheaper than the work it saves.
   */
  private def reaching(
    pool: Vector[LinearFact],
    pairs: Vector[(Int, Int)],
    missing: Set[Term]
  ): Vector[(Int, Int)] =
    pairs.filter { case (left, right) =>
      formOfPair(pool, left, right).exists(form => form.atoms.exists(missing.contains))
    }

  /**
   * What a pair's form would be, without building the theorem that earns it.
   *
   * Split out from [[product]] so that [[usable]] can judge a candidate before anything is derived.
   * The two must agree about the form, and they do by construction: this is the same expression,
   * and a divergence would show up as a manufactured fact whose theorem does not match its column,
   * which the assembly refuses.
   */
  private def formOfPair(
    pool: Vector[LinearFact],
    left: Int,
    right: Int
  ): Option[LinearForm] =
    if (pool(left).kind == Kind.Equal || pool(right).kind == Kind.Equal) None
    else Some(pool(left).form.times(pool(right).form, LinearForm.productAtom(reals, _, _)))

  /**
   * The same goal once more, with each product multiplied by each original fact.
   *
   * Degree three, and the third and last attempt at the products. The pairs reach degree two, so
   * `0 < r /\ 0 < e /\ d < q ==> r * e * d - r * e * q < 0` was refused for a reason that is not a
   * gap in the idea: `(0 < r) * (0 < e)` gives `0 < r * e`, and that times `d < q` is the goal.
   * The consumer that met it worked around it by carrying `r * e` as one positive quantity, which
   * is honest and is also a person doing the procedure's arithmetic.
   *
   * **It is cubic and it is last**, which is the whole of what makes it affordable: a goal settled
   * linearly never builds a pair, and a goal settled by the pairs never builds one of these. What
   * pays for it is a refusal, and the measurement is in the certificate-search section of
   * `docs/evaluation.md`.
   *
   * Only the products times the originals, never the products times each other. That would be
   * degree four and the count would be quartic, and nothing measured has wanted it. `docs/adr/0032`
   * is where that was measured rather than assumed, and the finding is sharper than "nothing has
   * wanted it": the two corpus goals that asked for more degree have **no hypotheses**, so the
   * pool this round multiplies is empty for them and a fourth round would settle neither, at any
   * degree. What they wanted was a fact from outside the goal's text, which is [[squares]].
   */
  private def byCubes(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    pool: Vector[LinearFact],
    theorems: Vector[Kernel.Thm],
    pairs: Vector[(LinearFact, Kernel.Thm)],
    conclusion: Term,
    missing: Set[Term],
    refusal: LogicError
  ): Either[LogicError, Kernel.Thm] =
    if (facts.length + pairs.length > cubeLimit)
      Left(BoundReached("Linarith.Cubes", facts.length + pairs.length, cubeLimit, conclusion))
    else {
    val combined = pool ++ pairs.map(_._1)
    val combinedTheorems = theorems ++ pairs.map(_._2)
    val crossed = for {
      product <- (pool.length until combined.length).toVector
      original <- (0 until pool.length).toVector
    } yield (product, original)

    productsOf(combined, combinedTheorems, reaching(combined, crossed, missing)) match {
      case Left(reason) => Left(kept(reason, refusal))
      case Right(deeper) if deeper.isEmpty => Left(refusal)

      // Through [[kept]] since the standing existed, and this line is the reason it is worth
      // generalising rather than repeating `case bound: BoundReached` a third time. The cubic round
      // adds facts on top of the pairs, so its `withExtra` can reach `Linarith.Facts` where the
      // pair round did not; `_ => refusal` swallowed that bound and reported a search that stopped
      // as a goal that does not follow, which is the defect this whole change is about, surviving
      // at the one site nobody had written the exception at.
      case Right(deeper) =>
        withExtra(facts, assumed, pairs ++ deeper, conclusion).left.map(kept(_, refusal))
    }
  }

  /**
   * The goal against the facts with some manufactured ones added, which stay parallel to them.
   *
   * == The bound, and what measured it ==
   *
   * The simplex underneath is exact-rational and its cost grows with the columns, which are the
   * distinct atoms, and the products manufacture atoms: `a * (b + c) = 152` and two more like it,
   * with three positivity facts, give a pool of nine, forty-five pairs, and a cubic round on top,
   * and [[byRefutation]] runs the whole of that three times.
   *
   * Measured on miniF2F's `amc12b_2002_p19`, which is exactly that statement: **439 seconds**, and
   * then a refusal. The next slowest of the 244 took 25. A procedure that spends seven minutes and
   * says no is worse than one that stops, which is the argument `Quantified` makes for its own
   * bound in the same words.
   *
   * The bound is on the facts the simplex is asked about, because that is what the cost tracks. It
   * is generous rather than tight: nothing in either vendored corpus reaches it, which is measured
   * by those suites and not asserted here.
   *
   * **The refusal it returns is swallowed, and that is this file's existing decision rather than a
   * new one.** Every failure of the escalation reports the refusal from before any of it, because a
   * caller repairs what it wrote and it did not write the products. What makes the bound readable
   * anyway is that it is a named constant with a test either side of it.
   */
  private def withExtra(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    extra: Vector[(LinearFact, Kernel.Thm)],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] = {
    val enlarged = facts ++ extra.map(_._1)

    if (enlarged.length > factLimit)
      Left(BoundReached("Linarith.Facts", enlarged.length, factLimit, conclusion))
    else prove(enlarged, assumed ++ extra.map(_._2), conclusion)
  }

  /**
   * Every pair of hypotheses multiplied, as a fact and the theorem that earns it.
   *
   * **Which pairs, and why not all of them.** Two strict facts give a strict one by `LT_MUL`, which
   * is an axiom; a strict and a non-strict give a non-strict one by `Order.multiplyNonNegative`;
   * two non-strict give a non-strict one by `Order.multiplyNonNegatives`. That last pair was
   * skipped until 2026-09-10 and the reason was a missing lemma rather than a missing move, which
   * is what it looked like from here: nothing in this procedure changed when the lemma arrived
   * except the line that chooses which one to instantiate. An equality is none of the three, and it
   * does not need to be: [[pairingPool]] has replaced it by its two halves, which are non-strict,
   * before any pair is taken.
   *
   * A pair is taken once, and includes a fact with itself. `e * f` and `f * e` are the same fact,
   * and [[LinearForm.productAtom]] gives them the same key, so the second would be a column the
   * simplex has to
   * carry and can never need; a fact squared is a different matter and is the case this move exists
   * for as much as any, since `0 < x ==> 0 < x * x` has only one hypothesis to work with.
   *
   * **An equality is paired through its two halves**, since 2026-09-10, and what it replaced was an
   * argument that is wrong. The argument: the difference an equality states is zero, so every
   * product with it is zero and carries nothing a combination could use. The first half is true and
   * the second does not follow. `e = 0` times `0 < n` is `n * e = 0`, which is zero and which says
   * that **the atom `n * e` is zero**, and the linear reading did not know that: `n * e` is a
   * column of its own and nothing else constrains it. That is the whole of why
   * `n * d = b /\ 0 < n /\ 0 < b ==> 0 < d` was refused, together with the negation of the goal not
   * being paired either, and `LinarithProductsSpec` holds that goal now.
   *
   * The halves are `a <= b` and `b <= a`, by `LE_OF_EQ` and the same the other way round, so this
   * needs no lemma that did not exist and reaches no new axiom. They are used for pairing and are
   * not added to the fact set: as forms they say what the equality already said, so a column for
   * each would be work the simplex does twice.
   */
  private def productsOf(
    pool: Vector[LinearFact],
    theorems: Vector[Kernel.Thm],
    pairs: Vector[(Int, Int)]
  ): Either[LogicError, Vector[(LinearFact, Kernel.Thm)]] =
    pairs.foldLeft(Right(Vector.empty): Either[LogicError, Vector[(LinearFact, Kernel.Thm)]]) {
      (acc, pair) =>
        for {
          done <- acc
          next <- product(pool, theorems, pair._1, pair._2)
        } yield done ++ next
    }

  /**
   * The facts as the pairing sees them: every one as itself, except an equality, which is two.
   *
   * `a = b` gives `a <= b` and `b <= a`. Both are non-strict, so the pairing multiplies them by the
   * lemma it already has, and between them they pin the product atom from both sides, which is what
   * an equality contributes and what dropping it lost.
   */
  private def pairingPool(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm]
  ): Either[LogicError, (Vector[LinearFact], Vector[Kernel.Thm])] =
    traverse(facts.indices.toVector) { index =>
      val fact = facts(index)
      assumed.lift(index) match {
        case None => Right(Vector((fact, Conv.refl(reals.logic.truth))))

        case Some(hypothesis) if fact.kind == Kind.Equal =>
          for {
            sides <- Term.destEq(hypothesis.conclusion).toRight(
              NotOfForm("an equation", hypothesis.conclusion)
            )
            (left, right) = sides
            lemma <- order.leOfEq
            upwards <- specialise(lemma, List(left, right))
            below <- rules.mp(upwards, hypothesis)
            reversed <- Conv.sym(hypothesis)
            downwards <- specialise(lemma, List(right, left))
            above <- rules.mp(downwards, reversed)
            belowFact <- LinearFact.of(reals, below.conclusion)
            aboveFact <- LinearFact.of(reals, above.conclusion)
          } yield Vector((belowFact, below), (aboveFact, above))

        case Some(hypothesis) => Right(Vector((fact, hypothesis)))
      }
    }.map(expanded => (expanded.flatten.map(_._1), expanded.flatten.map(_._2)))

  /** One pair, or nothing when the pair is one this does not multiply. */
  private def product(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    left: Int,
    right: Int
  ): Either[LogicError, Vector[(LinearFact, Kernel.Thm)]] = {
    import LinearFact.Kind

    def zeroForm(index: Int): Either[LogicError, Kernel.Thm] =
      assumed
        .lift(index)
        .toRight(NotOfForm("as many hypotheses as facts", reals.logic.truth))
        .flatMap { hypothesis =>
          facts(index).kind match {
            case Kind.Strict => strictPart(1, hypothesis)
            case Kind.NonStrict => nonStrictPart(1, hypothesis)
            case Kind.Equal => Left(NotOfForm("an inequality", hypothesis.conclusion))
          }
        }

    /**
     * The product of two facts, with the stronger one first where that matters.
     *
     * `LT_MUL` takes its two premises as a conjunction and the two non-strict lemmas take theirs
     * one at a time, so the shape of the application follows the kind of the result. Which
     * non-strict lemma is decided by the first side: a strict one there means the mixed lemma, and
     * a non-strict one means the lemma where both premises are non-strict. The caller is what puts
     * a strict side first, because the mixed lemma reads that way round and the order matters to it
     * and not to the other two.
     */
    def multiplied(
      strongerSide: Int,
      otherSide: Int,
      kind: Kind
    ): Either[LogicError, Vector[(LinearFact, Kernel.Thm)]] =
      for {
        first <- zeroForm(strongerSide)
        second <- zeroForm(otherSide)
        firstSide <- sideOf(first)
        secondSide <- sideOf(second)

        theorem <-
          if (kind == Kind.Strict)
            for {
              axiom <- reals.law("LT_MUL")
              instance <- specialise(axiom, List(firstSide, secondSide))
              both <- rules.conjIntro(first, second)
              result <- rules.mp(instance, both)
            } yield result
          else
            for {
              lemma <-
                if (facts(strongerSide).kind == Kind.Strict) order.multiplyNonNegative
                else order.multiplyNonNegatives
              instance <- specialise(lemma, List(firstSide, secondSide))
              applied <- rules.mp(instance, first)
              result <- rules.mp(applied, second)
            } yield result

        form = facts(strongerSide).form.times(
          facts(otherSide).form,
          LinearForm.productAtom(reals, _, _)
        )
      } yield Vector((LinearFact(kind, form), theorem))

    (facts(left).kind, facts(right).kind) match {
      case (Kind.Strict, Kind.Strict) => multiplied(left, right, Kind.Strict)
      case (Kind.Strict, Kind.NonStrict) => multiplied(left, right, Kind.NonStrict)
      case (Kind.NonStrict, Kind.Strict) => multiplied(right, left, Kind.NonStrict)
      case (Kind.NonStrict, Kind.NonStrict) => multiplied(left, right, Kind.NonStrict)
      case _ => Right(Vector.empty)
    }
  }

  /** The right-hand side of `0 < e` or `0 <= e`, which is what a product is taken between. */
  private def sideOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Order
      .destOrder(reals, theorem.conclusion)
      .map(_._2)
      .toRight(NotOfForm("an inequality against zero", theorem.conclusion))

  /**
   * `a /\ b` from `a` and `b`, each proved the way its own shape wants.
   *
   * The conjunctive hypotheses were always taken apart; the conjunctive conclusion had no route
   * until 2026-09-08, and it is the shape a corpus of measurements is written in: "the index is
   * above one in 2023 and in 2024" is one claim to whoever writes it and two goals to this
   * procedure.
   *
   * A failing conjunct is reported as itself rather than as the conjunction, because a caller told
   * that `a /\ b` failed learns nothing it can act on, and the two conjuncts usually fail for
   * different reasons or not at all. Nesting deeper is free: each side re-enters [[prove]], so a
   * chain of three or more is a chain of introductions.
   */
  private def byConjunction(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      first <- prove(facts, assumed, left)
      second <- prove(facts, assumed, right)
      result <- rules.conjIntro(first, second)
    } yield result

  /**
   * Why this goal was not settled, naming the obstacle when the fragment can name one.
   *
   * When the conclusion carries a construction the linear form cannot see, that construction is the
   * answer the caller needs and it is named: a `NotOfForm`, which says the question was never put.
   *
   * Otherwise the simplex ran to the end and there is no non-negative combination, and since this
   * defect was closed that is a `DoesNotFollow` rather than a second `NotOfForm` with a different
   * sentence in it. [[Farkas]] is complete over the columns it is given and carries no iteration
   * bound, so `None` from [[Certificate]] is the search finishing rather than the search stopping;
   * a search that stopped comes back as a `BoundReached` from somewhere else entirely.
   *
   * Only the conclusion is inspected here. Whether the HYPOTHESES were read is what decides whether
   * that `DoesNotFollow` survives, and it is asked once at the boundary by [[read]] rather than at
   * each of this method's callers, which see a sub-goal and not the statement.
   */
  private def refusal(conclusion: Term): LogicError =
    LinearForm.obstacleIn(reals, conclusion) match {
      case Some(named) => NotOfForm(s"a goal this procedure can read: $named", conclusion)
      case None => DoesNotFollow(conclusion, "LINARITH")
    }

  /**
   * A decision taken back when the procedure did not read the statement it decided over.
   *
   * [[LinearFact.of]] never fails: a hypothesis it cannot read becomes a strict fact over an atom
   * nobody else mentions, which is right for a procedure that ends in a theorem and wrong for one
   * that ends in an answer, and its own documentation says so. A bare proposition `p` becomes the
   * fact `0 < p`, so `p ==> p` reaches the certificate search as a question about an unknown, finds
   * no combination, and would report a **decision** that a tautology does not follow. The same goes
   * for a conclusion of a shape the form does not read at all, which falls through to the
   * contradiction search and is refused without ever having been looked at.
   *
   * So the standing is earned by the reading: every hypothesis has to be one of the three relations
   * [[LinearFact.relation]] admits, and the conclusion has to be one of the shapes [[prove]] routes
   * on. Otherwise the refusal is demoted to a `NotOfForm`, which says what it is.
   *
   * **The unread hypothesis is named, and until this existed it deliberately was not.** The earlier
   * decision was that naming it sends a caller to repair the half of the goal that was not the
   * obstacle, which was right while the only thing at stake was advice. It stops being right once a
   * decision is at stake: an unread premise is not a weak signal then, it is the whole reason there
   * is no decision, and a caller told "your goal does not follow" about a premise nobody read is
   * told the one thing this repository exists not to say.
   */
  private def read(shape: Shape, refusal: LogicError): LogicError = refusal match {
    case _: DoesNotFollow =>
      shape.hypotheses.find(LinearFact.relation(reals, _).isLeft) match {
        case Some(unread) =>
          NotOfForm(
            s"a goal whose hypotheses are relations between reals: ${reals.show(unread)} is not " +
              "one, so nothing here has read it",
            shape.conclusion
          )
        case None if readsAsGoal(shape.conclusion) => refusal
        case None =>
          NotOfForm(
            "a goal that is a relation between reals, or a conjunction or a denial of them",
            shape.conclusion
          )
      }

    case other => other
  }

  /**
   * Whether [[prove]] has a route for this conclusion, asked the way [[prove]] chooses one.
   *
   * A second reading of the same dispatch, and the only defensible way to write it: what makes a
   * refusal a decision is that the search was about the goal, and the search is about the goal
   * exactly when the dispatch found it a route other than the fall-through to the contradiction
   * search. A predicate invented beside that dispatch would go out of step with it silently.
   */
  private def readsAsGoal(conclusion: Term): Boolean =
    reals.logic.destConj(conclusion) match {
      case Some((left, right)) => readsAsGoal(left) && readsAsGoal(right)
      case None =>
        LinearForm.goal(reals, conclusion).isDefined ||
          Term.destEq(conclusion).exists { case (left, _) =>
            Term.typeOf(left) == Real.realType
          } ||
          reals.logic.destNot(conclusion).exists(readsAsGoal)
    }

  /** `a = b` from `a <= b` and `b <= a`, each proved the way an inequality is. */
  private def byAntisymmetry(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      lessEqual <- Order.lessEqualConstant(reals)
      upwards <- LogicError.lift(Term.appAll(lessEqual, List(left, right)))
      downwards <- LogicError.lift(Term.appAll(lessEqual, List(right, left)))

      below <- prove(facts, assumed, upwards)
      above <- prove(facts, assumed, downwards)

      lemma <- order.antisymmetric
      instance <- specialise(lemma, List(left, right))
      applied <- rules.mp(instance, below)
      result <- rules.mp(applied, above)
    } yield result

  /**
   * Assume the antecedent as written and take it apart along its own conjunctions.
   *
   * As written, because the discharge at the end removes the term it is given and nothing else: an
   * antecedent assumed in a shape the goal did not have is discharged into an implication the goal
   * did not state. Assuming the whole and projecting, rather than assuming each conjunct, means
   * one thing to discharge. The parts come out in the order [[conjuncts]] lists them, which is
   * what lets the certificate's multipliers name them.
   */
  private def assumeAll(antecedents: Vector[Term]): Either[LogicError, Vector[Kernel.Thm]] =
    traverse(antecedents)(term => LogicError.lift(Kernel.assume(term)).flatMap(project))
      .map(_.flatten)

  /**
   * The goal, from the combination the search found.
   *
   * The multipliers are whole because the certificate was cleared of its denominators, so the sum
   * comes out as the goal's difference multiplied by that common denominator, and the cancellation
   * lemmas in [[Order]] take it back off. Nothing here divides and nothing here writes `inv`,
   * which is what lets a rational certificate be checked by a ring that refuses `inv`.
   */
  private def fromCertificate(
    certificate: Certificate,
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      parts <- weigh(certificate, facts, assumed)
      combined <- combine(parts)
      shifted <- shiftToGoal(combined, certificate.scale, conclusion)
    } yield shifted

  /**
   * The goal, from hypotheses that cannot all hold.
   *
   * The other half of a decision procedure, rather than a search for one shape of proof: an
   * implication whose premises cannot all hold is true whatever it concludes. It is the same
   * search with the zero form as its target, so what the combination adds up to is nothing while
   * being strictly above nothing, and the goal follows from that falsity.
   */
  private def fromContradiction(
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    Certificate.find(facts, LinearForm.zero, strict = true) match {
      case None => Left(refusal(conclusion))
      case Some(certificate) => rebuilt(conclusion, absurdity(certificate, facts, assumed, conclusion))
    }

  /** The goal from a certificate that the hypotheses cannot all hold, which is [[fromContradiction]]'s rebuilding. */
  private def absurdity(
    certificate: Certificate,
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm],
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      parts <- weigh(certificate, facts, assumed)
      combined <- combine(parts)
      summed <- combined match {
        case (theorem, true) => Right(theorem)
        case (theorem, false) => Left(NotOfForm("a combination that is strictly positive", theorem.conclusion))
      }

      sum <- Order.destLess(reals, summed.conclusion).map(_._2)
      zero <- reals.term("0")
      equation <- LogicError.lift(Term.eq(sum, zero))
      vanishes <- ring.prove(equation)
      atZero <- Conv.rewriteRight(summed, vanishes)

      irreflexive <- reals.law("LT_IRREFLEXIVE")
      never <- rules.spec(zero, irreflexive)
      absurd <- rules.notElim(never, atZero)
      result <- rules.falsityElim(conclusion, absurd)
    } yield result

  /**
   * Each hypothesis the certificate weighs, as a theorem about zero, in two piles.
   *
   * A strict hypothesis weighed by `k` gives `0 < k * e`; a non-strict one gives `0 <= k * e`; an
   * equality gives `0 <= k * (b - a)` for a `k` of either sign, because what it multiplies is
   * zero. The constant the certificate asked for is strict, since it is a positive numeral.
   */
  private def weigh(
    certificate: Certificate,
    facts: Vector[LinearFact],
    assumed: Vector[Kernel.Thm]
  ): Either[LogicError, (Vector[Kernel.Thm], Vector[Kernel.Thm])] = {
    val chosen = certificate.multipliers.zipWithIndex.filter { case (factor, _) => factor != 0 }

    for {
      weighed <- traverse(chosen) { case (factor, index) =>
        for {
          hypothesis <- assumed
            .lift(index)
            .toRight(NotOfForm("as many hypotheses as the certificate names", reals.logic.truth))
          kind <- facts
            .lift(index)
            .map(_.kind)
            .toRight(NotOfForm("as many facts as the certificate names", reals.logic.truth))
          result <- kind match {
            case Kind.Strict => strictPart(factor, hypothesis).map(Left(_))
            case Kind.NonStrict => nonStrictPart(factor, hypothesis).map(Right(_))
            case Kind.Equal => equalPart(factor, hypothesis).map(Right(_))
          }
        } yield result
      }

      constant <-
        if (certificate.slack > 0) order.positive(certificate.slack).map(Vector(_))
        else Right(Vector.empty)
    } yield (
      weighed.collect { case Left(theorem) => theorem } ++ constant,
      weighed.collect { case Right(theorem) => theorem }
    )
  }

  /** `a < b` weighed by `k` becomes `0 < k * (b - a)`. */
  private def strictPart(factor: BigInt, hypothesis: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Order.destLess(reals, hypothesis.conclusion)
      instance <- specialise(moveRight, List(sides._1, sides._2))
      positive <- rules.mp(instance, hypothesis)
      result <- multiply(factor, positive)
    } yield result

  /** `a <= b` weighed by `k` becomes `0 <= k * (b - a)`. */
  private def nonStrictPart(
    factor: BigInt,
    hypothesis: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Order.destLessEqual(reals, hypothesis.conclusion)
      lemma <- order.leToZero
      instance <- specialise(lemma, List(sides._1, sides._2))
      nonNegative <- rules.mp(instance, hypothesis)
      result <- multiplyWeakly(factor, nonNegative)
    } yield result

  /**
   * `a = b` weighed by `k` becomes `0 <= k * (b - a)`, for a `k` of either sign.
   *
   * What the multiplier multiplies is zero, so the sign is free and the fact is non-negative
   * rather than positive. The equation is proved by congruence at the one place `a` was put:
   * `k * (b - a) = k * (b - b)` from the hypothesis, and `RING` closes `k * (b - b) = 0`.
   *
   * **Not by rewriting with the hypothesis**, which is what this did until 2026-09-25. A rewrite
   * replaces `a` wherever it occurs, and when `a` occurs inside `b` it replaces it there too:
   * `x = c * x` turned `k * (c * x - x)` into `k * (c * (c * x) - c * x)`, which is not zero, so
   * `RING` refused a goal the linear fragment decides and the refusal named neither the goal nor
   * the equation. Taking one pass rather than a fixed point did not help, because the occurrence
   * inside `b` is reached in the same pass. Congruence cannot reach it: the function it applies is
   * built with `b` already in place.
   */
  private def equalPart(factor: BigInt, hypothesis: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Term
        .destEq(hypothesis.conclusion)
        .toRight(NotOfForm("an equation", hypothesis.conclusion))
      difference <- Linarith.difference(reals, sides._2, sides._1)
      numeral <- reals.term(factor.toString)
      weighted <- Linarith.product(reals, numeral, difference)

      subtractFrom <- difference match {
        case App(fn, _) => Right(fn)
        case other => Left(NotOfForm("a subtraction", other))
      }
      scaleBy <- weighted match {
        case App(fn, _) => Right(fn)
        case other => Left(NotOfForm("a product", other))
      }
      substituted <- Conv.apTerm(subtractFrom, hypothesis)
      scaled <- Conv.apTerm(scaleBy, substituted)
      settled <- Term
        .destEq(scaled.conclusion)
        .toRight(NotOfForm("an equation", scaled.conclusion))

      zero <- reals.term("0")
      collapses <- LogicError.lift(Term.eq(settled._2, zero)).flatMap(ring.prove)
      isZero <- Conv.trans(scaled, collapses)
      backwards <- Conv.sym(isZero)

      lemma <- order.leOfEq
      instance <- specialise(lemma, List(zero, weighted))
      result <- rules.mp(instance, backwards)
    } yield result

  /**
   * `0 < e` becomes `0 < k * e`, for a whole `k` above one.
   *
   * The multiplier is proved positive rather than assumed to be: `Order.positive` derives `0 < k`
   * from the bits of `k` and the axiom for a product of positives does the rest. A multiplier of
   * one is left alone, which is what keeps the goals that never needed one as cheap as they were.
   */
  private def multiply(factor: BigInt, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (factor == 1) Right(positive)
    else
      for {
        numeral <- Numeral.of(reals, factor)
        positiveFactor <- order.positive(factor)
        side <- Order.destLess(reals, positive.conclusion).map(_._2)
        ltMul <- reals.law("LT_MUL")
        instance <- specialise(ltMul, List(numeral, side))
        both <- rules.conjIntro(positiveFactor, positive)
        result <- rules.mp(instance, both)
      } yield result

  /** `0 <= e` becomes `0 <= k * e`, for a whole `k` above one. */
  private def multiplyWeakly(
    factor: BigInt,
    nonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    if (factor == 1) Right(nonNegative)
    else
      for {
        numeral <- Numeral.of(reals, factor)
        positiveFactor <- order.positive(factor)
        side <- Order.destLessEqual(reals, nonNegative.conclusion).map(_._2)
        lemma <- order.multiplyNonNegative
        instance <- specialise(lemma, List(numeral, side))
        applied <- rules.mp(instance, positiveFactor)
        result <- rules.mp(applied, nonNegative)
      } yield result

  /**
   * The two piles added into one theorem, and whether what came out is strict.
   *
   * The non-negative ones are added together first and the positive ones after, so that the last
   * step is the one lemma that mixes them. With nothing positive the result is non-negative, which
   * is enough for a goal that is not strict; with nothing at all it is `0 <= 0`, which is what a
   * goal like `x <= x` needs.
   */
  private def combine(
    parts: (Vector[Kernel.Thm], Vector[Kernel.Thm])
  ): Either[LogicError, (Kernel.Thm, Boolean)] = {
    val (strict, nonStrict) = parts

    (strict.toList, nonStrict.toList) match {
      case (Nil, Nil) => zeroIsNonNegative.map((_, false))

      case (positives, Nil) => addUp(positives.toVector).map((_, true))

      case (Nil, weak) => addUpWeakly(weak.toVector).map((_, false))

      case (positives, weak) =>
        for {
          summedWeak <- addUpWeakly(weak.toVector)
          summedStrict <- addUp(positives.toVector)
          lemma <- order.addNonNegativePositive
          weakSide <- Order.destLessEqual(reals, summedWeak.conclusion).map(_._2)
          strictSide <- Order.destLess(reals, summedStrict.conclusion).map(_._2)
          instance <- specialise(lemma, List(weakSide, strictSide))
          applied <- rules.mp(instance, summedWeak)
          result <- rules.mp(applied, summedStrict)
        } yield (result, true)
    }
  }

  /** `|- 0 <= 0`, which is the empty combination. */
  private def zeroIsNonNegative: Either[LogicError, Kernel.Thm] =
    for {
      zero <- reals.term("0")
      lemma <- order.leOfEq
      instance <- specialise(lemma, List(zero, zero))
      result <- rules.mp(instance, Conv.refl(zero))
    } yield result

  /** Add a list of `0 < e` theorems into one. */
  private def addUp(positives: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    positives.toList match {
      case Nil => Left(NotOfForm("at least one hypothesis to add", reals.logic.truth))
      case first :: rest =>
        rest.foldLeft(Right(first): Either[LogicError, Kernel.Thm]) { (acc, next) =>
          acc.flatMap(addPair(_, next))
        }
    }

  /** Add a list of `0 <= e` theorems into one. */
  private def addUpWeakly(parts: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    parts.toList match {
      case Nil => Left(NotOfForm("at least one hypothesis to add", reals.logic.truth))
      case first :: rest =>
        rest.foldLeft(Right(first): Either[LogicError, Kernel.Thm]) { (acc, next) =>
          for {
            running <- acc
            lemma <- order.addNonNegatives
            left <- Order.destLessEqual(reals, running.conclusion).map(_._2)
            right <- Order.destLessEqual(reals, next.conclusion).map(_._2)
            instance <- specialise(lemma, List(left, right))
            afterFirst <- rules.mp(instance, running)
            result <- rules.mp(afterFirst, next)
          } yield result
        }
    }

  /** `0 < a` and `0 < b` give `0 < a + b`. */
  private def addPair(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      leftSide <- Order.destLess(reals, left.conclusion).map(_._2)
      rightSide <- Order.destLess(reals, right.conclusion).map(_._2)
      instance <- specialise(addPositive, List(leftSide, rightSide))
      afterFirst <- rules.mp(instance, left)
      result <- rules.mp(afterFirst, right)
    } yield result

  /**
   * Turn the combination into the goal, by showing it is the goal's difference times the scale.
   *
   * This is where the search is checked. The combination was chosen by arithmetic on linear forms,
   * and nothing so far says it has anything to do with the goal; the ring tactic says whether it
   * does. A scale above one is then cancelled, which is the only place a multiplier that was
   * rational ever shows itself, and a strict combination is weakened when the goal is not strict.
   */
  private def shiftToGoal(
    combined: (Kernel.Thm, Boolean),
    scale: BigInt,
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] = {
    val (summed, strictSum) = combined

    for {
      goalSides <- Order
        .destOrder(reals, conclusion)
        .toRight(NotOfForm("an inequality", conclusion))
      (left, right, strictGoal) = goalSides

      matched <-
        if (strictSum == strictGoal) Right(summed)
        else if (strictSum) weaken(summed)
        else Left(NotOfForm("a combination strict enough for the goal", summed.conclusion))

      sum <- Order
        .destOrder(reals, matched.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an inequality", matched.conclusion))
      difference <- Linarith.difference(reals, right, left)

      target <-
        if (scale == 1) Right(difference)
        else Numeral.of(reals, scale).flatMap(Linarith.product(reals, _, difference))

      equation <- LogicError.lift(Term.eq(sum, target))
      sameThing <- ring.prove(equation)
      moved <- Conv.rewriteRight(matched, sameThing)

      unscaled <-
        if (scale == 1) Right(moved)
        else cancel(scale, difference, moved, strictGoal)

      lemma <- if (strictGoal) Right(moveLeft) else order.leFromZero
      instance <- specialise(lemma, List(left, right))
      result <- rules.mp(instance, unscaled)
    } yield result
  }

  /** `0 < e` becomes `0 <= e`. */
  private def weaken(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Order.destLess(reals, positive.conclusion)
      lemma <- order.leOfLt
      instance <- specialise(lemma, List(sides._1, sides._2))
      result <- rules.mp(instance, positive)
    } yield result

  /** `0 < d * e` becomes `0 < e`, and the same without the strictness, for a whole `d`. */
  private def cancel(
    scale: BigInt,
    difference: Term,
    positive: Kernel.Thm,
    strict: Boolean
  ): Either[LogicError, Kernel.Thm] =
    for {
      numeral <- Numeral.of(reals, scale)
      positiveScale <- order.positive(scale)
      lemma <- if (strict) order.cancelPositive else order.cancelNonNegative
      instance <- specialise(lemma, List(numeral, difference))
      applied <- rules.mp(instance, positiveScale)
      result <- rules.mp(applied, positive)
    } yield result

  /** Every conjunct of a theorem's conclusion as a theorem of its own, left to right. */
  private def project(theorem: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
    reals.logic.destConj(theorem.conclusion) match {
      case None => Right(Vector(theorem))
      case Some(_) =>
        for {
          left <- rules.conjElim1(theorem)
          right <- rules.conjElim2(theorem)
          leftParts <- project(left)
          rightParts <- project(right)
        } yield leftParts ++ rightParts
    }

  /* ------------------------------------------------------------------- shapes */

  /** Take the quantifiers off a goal, replacing each bound variable with a fresh free one. */

  /** An implication becomes its antecedent, in parts, and its consequent; anything else is a goal with none. */
  private def split(body: Term): Shape = {
    def peel(current: Term, taken: Vector[Term]): (Vector[Term], Term) =
      reals.logic.destImp(current) match {
        case Some((antecedent, consequent)) => peel(consequent, taken :+ antecedent)
        case None => (taken, current)
      }

    val (antecedents, conclusion) = peel(body, Vector.empty)
    Shape(antecedents, antecedents.flatMap(conjuncts), conclusion)
  }

  private def conjuncts(term: Term): Vector[Term] =
    reals.logic.destConj(term) match {
      case Some((left, right)) => conjuncts(left) ++ conjuncts(right)
      case None => Vector(term)
    }

  private def generalise(
    theorem: Kernel.Thm,
    variables: Vector[FVar]
  ): Either[LogicError, Kernel.Thm] =
    variables.reverse.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, variable) =>
      acc.flatMap(current => rules.gen(variable, current))
    }

  private def specialise(
    theorem: Kernel.Thm,
    arguments: List[Term]
  ): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, argument) =>
      acc.flatMap(current => rules.spec(argument, current))
    }

  private def traverse[A, B](
    items: Vector[A]
  )(f: A => Either[LogicError, B]): Either[LogicError, Vector[B]] =
    items.foldLeft(Right(Vector.empty): Either[LogicError, Vector[B]]) { (acc, item) =>
      for {
        done <- acc
        next <- f(item)
      } yield done :+ next
    }
}

object Linarith {

  /**
   * What a proof rested on: the goal's own premises, and beside them the squares it was given.
   *
   * Two fields and not one list, which is `docs/adr/0032` point 4. [[Linarith.support]] answers
   * "which of the premises I wrote did this need", and a completed square is not a premise
   * anybody wrote: putting it among them would answer a question nobody asked, and it would put a
   * proposition in the list that no citation can ever be attached to, which is exactly the
   * confusion `Provenance.Premise.Unnameable` exists one level up to avoid.
   *
   * Leaving it out entirely was the other candidate and it is worse, which is why this type
   * exists at all. A goal settled by a square alone then reports an empty `hypotheses`, and empty
   * is already the honest answer for a goal that needed none of its premises; the two readings
   * are "nothing was needed" and "something was needed and it is not shown", and a diagnostic
   * that cannot tell them apart is the failure `Refutation` keeps seven outcomes apart to avoid.
   *
   * `squares` carries the theorem's own statement, `0 <= (x + c) * (x + c)`, rather than the
   * atom it was completed over, because that is the proposition the certificate weighed and the
   * one a reader can check against `SQUARE_NONNEG`.
   */
  final case class Support(
    hypotheses: Vector[(Term, BigInt)],
    squares: Vector[(Term, BigInt)]
  )


  /**
   * The most facts the simplex is asked about once the products have been manufactured.
   *
   * Not a tuning knob. It is what stops the escalation from spending on a goal it is going to
   * refuse anyway, and the number was chosen by measurement: nothing in either vendored corpus
   * builds a problem this large, and four statements of miniF2F build one at fifty-one facts.
   *
   * A goal over the bound is refused, not decided, so raising it can only add proofs and lowering it
   * can only remove them. **What it costs is measured in both directions**, and the measurement was
   * taken twice, because the first version of this note had the second half wrong.
   *
   * What it cuts: `mathd_algebra_478` and, in the generated family of `LinarithLimitsSpec`, every
   * goal from nine positivity hypotheses up. Those are provable, and they come back refused.
   *
   * What it buys: **not what this said**. It said the pair round on fifty-one facts "takes minutes
   * on a goal it then refuses", and on 2026-09-11 one call of this procedure with the bounds at 400
   * takes 15 to 100 milliseconds on every one of them. The minutes were somewhere else, and the
   * cost is real one level up: `Abduce` runs this once per candidate premise, so a goal twenty
   * milliseconds dearer here is a hundred times that there. Through the whole surface over the six
   * heaviest statements of miniF2F: **20.0 seconds at these bounds against 40.6 seconds at 400**,
   * for one proof. Twice the time on the heavy tail against one theorem, and the time wins, because
   * raising this line is a change a caller can make and waiting is not.
   *
   * `docs/evaluation.md` carries both measurements with their dates.
   */
  val Facts: Int = 48

  /**
   * The largest problem the cubic round will start from.
   *
   * Separate from [[Facts]] because the two rounds are for different things and cost differently:
   * the cubic round multiplies every pair by every original, so it is cubic in the pool where the
   * pair round is quadratic, and a problem the pairs settle in milliseconds is one the cubes do
   * not.
   *
   * The number says what the round is for rather than tuning it. Its own docstring gives the case
   * it was built for, `0 < r /\ 0 < e /\ d < q ==> r * e * d - r * e * q < 0`: three hypotheses, a
   * pool of three, six pairs, nine facts. A round reached only by small problems is what makes a
   * cubic round affordable, and the bound is what makes "small" a fact rather than a hope.
   *
   * == Which of the two a goal meets, which is not decided by its size ==
   *
   * The two guards compare **the same quantity**, the facts plus the manufactured products, against
   * different numbers, so a goal past [[Facts]] never reaches the cubic round at all and this bound
   * can only act between the two. What decides which one a goal meets is its **conclusion**: one
   * naming an atom the pairs already reach is refused on the facts, and one naming a product of
   * three gets the cubic round and meets this. `LinarithLimitsSpec` generates both from one family
   * and the first version of it asserted the opposite, on the argument that the smaller number is
   * reached first.
   *
   * Reached by one statement of miniF2F, `imo_1964_p2`, at 27 against 24 when this was measured,
   * before 2026-09-14, and by six positivity hypotheses with a product of three in the conclusion —
   * which is provable, and refused here.
   */
  val Cubes: Int = 24

  /** Built once over the standard theory. */
  lazy val standard: Linarith =
    construct(Order.standard).fold(
      error => throw new IllegalStateException(s"linear arithmetic does not build: ${error.message}"),
      identity
    )

  /**
   * Over an order that has already been built.
   *
   * The three lemmas the procedure runs on are order facts and live in [[Order]] with the rest of
   * them, so this takes the facts rather than deriving them: building the order twice is the only
   * other way to have them, and one of the two copies would then be the one nobody tested.
   */
  def construct(order: Order): Either[LogicError, Linarith] = at(order, Facts, Cubes)

  def construct(ring: Ring): Either[LogicError, Linarith] =
    Order.construct(ring).flatMap(construct)

  /**
   * The same procedure with the two bounds somewhere else, which is how they are measured.
   *
   * Not a tuning entry point for ordinary use and the name says so. Raising a bound can only add
   * proofs and lowering one can only remove them, so neither direction is a risk to soundness: what
   * moves is time and reach. What this is for is asking the same goals either side of a line, which
   * is the only way to say what a line costs.
   */
  def at(order: Order, factLimit: Int, cubeLimit: Int): Either[LogicError, Linarith] =
    for {
      moveRight <- order.moveToZero
      moveLeft <- order.moveFromZero
      addPositive <- order.addPositive
    } yield new Linarith(order, moveRight, moveLeft, addPositive, factLimit, cubeLimit)

  /* ----------------------------------------------------------------- helpers */

  val realType: Type = TyApp(Real.TypeName, Nil)

  /** `b - a`, as a term. */
  def difference(reals: Signature, left: Term, right: Term): Either[LogicError, Term] =
    for {
      subtraction <- LogicError.lift(
        reals.theory.constant(Real.Subtraction, Type.fun(realType, Type.fun(realType, realType)))
      )
      result <- LogicError.lift(Term.appAll(subtraction, List(left, right)))
    } yield result

  /** `a * b`, as a term. */
  def product(reals: Signature, left: Term, right: Term): Either[LogicError, Term] =
    for {
      multiplication <- LogicError.lift(
        reals.theory.constant(Real.Multiplication, Type.fun(realType, Type.fun(realType, realType)))
      )
      result <- LogicError.lift(Term.appAll(multiplication, List(left, right)))
    } yield result

  /** `a + b`, as a term. */
  def sum(reals: Signature, left: Term, right: Term): Either[LogicError, Term] =
    for {
      addition <- LogicError.lift(
        reals.theory.constant(Real.Addition, Type.fun(realType, Type.fun(realType, realType)))
      )
      result <- LogicError.lift(Term.appAll(addition, List(left, right)))
    } yield result

  /** `a / b`, as a term. */
  def quotient(reals: Signature, left: Term, right: Term): Either[LogicError, Term] =
    for {
      division <- LogicError.lift(
        reals.theory.constant(Real.Division, Type.fun(realType, Type.fun(realType, realType)))
      )
      result <- LogicError.lift(Term.appAll(division, List(left, right)))
    } yield result

  /**
   * A rational as a term the form reader gives that rational back for.
   *
   * Whole values are a numeral and nothing else; the rest are a quotient of two numerals, which is
   * one of the four shapes [[LinearForm]] reads as a constant rather than as an atom. The sign is
   * on the numerator because `Rational.of` puts it there, so a negative value is a numeral under
   * `Real.Negation` and never a negative denominator, which that reader does not accept.
   *
   * Built here rather than by printing and parsing, because a text would go through the elaborator
   * and a numeral with nothing to fix its type is refused since `docs/adr/0018`.
   */
  def constant(reals: Signature, value: Rational): Either[LogicError, Term] = {
    def whole(magnitude: BigInt): Either[LogicError, Term] =
      if (magnitude >= 0) Numeral.of(reals, magnitude)
      else
        for {
          positive <- Numeral.of(reals, -magnitude)
          negation <- LogicError.lift(
            reals.theory.constant(Real.Negation, Type.fun(realType, realType))
          )
          result <- LogicError.lift(Term.app(negation, positive))
        } yield result

    if (value.denominator == 1) whole(value.numerator)
    else
      for {
        numerator <- whole(value.numerator)
        denominator <- Numeral.of(reals, value.denominator)
        result <- quotient(reals, numerator, denominator)
      } yield result
  }
}
