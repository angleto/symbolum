package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The integers inside the reals: `real_of_int`, and the facts that make it a ring embedding.
 *
 * == Why it is a development of its own and not five lines of `Integer.scala` ==
 *
 * `Integer.scala` says of itself that *nothing in it reaches for a real*, and `docs/adr/0033` rests
 * a consequence on that sentence: when the reals are constructed, phase 5 of `docs/adr/0016` moves
 * that development **below** `Real` rather than rewriting it. The bridge is the one thing that
 * cannot move with it, because `real` is half of every statement here. Putting it there would have
 * made the file's own first paragraph false on the day it was written.
 *
 * The precedent is the same shape one type down. `docs/adr/0016` split `Peano` in two, and the
 * seventeen facts that cannot be stated without the reals went into `Embedding.scala`; this
 * development stands to `Integer` as that file stands to `Peano`. What is different is that this is
 * a link of the chain and that is a private object, and the reason is the reason a link exists at
 * all: `real_of_int` is a constant, and a constant declared outside the chain is unreachable from
 * `Ask`, from `Find` and from `docs/lemmas.md`.
 *
 * == What it costs ==
 *
 * One constant, no type, and **no axiom asserted**: `InclusionSpec` reads the trusted base off the
 * theory and finds it unmoved, which is the claim that matters and is the one a link is allowed to
 * make.
 *
 * What it does **spend** is a different question and the answer is the interesting one.
 * `IntegerSpec` asserts that no fact of that development reaches any of the sixteen axioms of the
 * reals, and the card that asked for it turns on that: a signed ring charging the reals would be
 * built on the thing it exists to avoid needing. **Every fact here reaches them**, because every
 * fact here is an equation between real numbers and `Ring` decides those out of the field. So this
 * file is exactly the boundary that sentence is about — the integers cost the carrier's three,
 * choice, eta and infinity, and the bridge costs those three and the reals' sixteen — and
 * `InclusionSpec` asserts both halves, the inclusion and the contrast, because a walk that returned
 * the same set for everything would pass either one alone.
 *
 * That is also the accounting reason the split is not cosmetic. After phase 5 of `docs/adr/0016`
 * the sixteen are theorems and this development's price falls to the carrier's, while `Integer`'s
 * does not move at all: two files whose axiom sets answer differently to the same future change.
 *
 * == It is `Quotient.liftPredicate`, which nobody expected ==
 *
 * The lift is not written out here. `Quotient.liftPredicate` takes a function of one carrier
 * argument, and nothing in it reads what that function returns, so it lifts a `real`-valued one
 * unchanged; that file's own docstring said the opposite until this landed, and names this
 * development as the measurement that refuted it.
 *
 * What the builder was missing is a different thing and is `Quotient.over`. A lift defines its
 * constant into the quotient's **own** theory, which is the theory as it stood when the last lift
 * ran: `Integer` lifts addition, negation and multiplication and then defines five more constants,
 * so its quotient's theory is five short of the one it publishes, and `real_of_int INT_ZERO = 0`
 * could not be stated against it, never mind proved. Re-basing the quotient onto the theory being
 * extended is what this development does first, and it is checked rather than assumed: `Logic.over`
 * refuses a theory that does not declare every constant of the narrower one at the same type.
 *
 * == How six of the eight are proved, which is one route ==
 *
 * [[Inclusion.AtPair]] is what the lift returns, and each of the six equations after it is the same
 * four steps. Both sides are written at **carrier** variables, `INT_OF_PAIR x` rather than `a:int`;
 * the lifted equations of `Integer`, the two definitions that are pairs and the two projections
 * bring each side to an expression built out of `real_of_num` applied to components; `Peano`'s
 * homomorphism facts take the embedding through the `num` arithmetic that is left; and `Ring`
 * closes what remains, which is an identity of the reals with `real_of_num (FST x)` and its
 * siblings as atoms it cannot take apart. The result is put back over `int` by specialising at a
 * representative, which is `Integer`'s own last step.
 *
 * The two that are **not** that route say so where they are written: [[Inclusion.respectfulness]],
 * which has to move an equation of `num` into the reals before any identity is available, and
 * [[Inclusion.EmbedsInjectively]], which runs the same move backwards and is an implication.
 */
final class Inclusion private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Inclusion {

  /* ------------------------------------------------------------------ the names */

  /**
   * `real_of_int a` — the integer `a` as a real number.
   *
   * Lowercase, and reading as the pair of subjects it is about, which is `real_of_num`'s spelling
   * one type down rather than the `INT_` namespace of the development it embeds. `docs/naming.md`
   * decides it twice over: a constant is named the way its neighbours are named, and the neighbour
   * of a map into the reals is the other map into the reals. The card that asked for this file
   * wrote `REAL_OF_INT`, which would have put two spellings of one operation into one signature.
   */
  val Name: String = "real_of_int"

  /**
   * `|- !p. real_of_int (INT_OF_PAIR p) = real_of_num (FST p) - real_of_num (SND p)`.
   *
   * What the lift hands back, and the fact every one below goes through. A pair `(a, b)` stands for
   * `a - b`, so this is the construction's own sentence read at the reals, where it can be written
   * with a subtraction because the reals have one that is not truncated. The carrier's own version
   * cannot be written at all: that is `docs/adr/0033`'s reason for the additive spelling of
   * `INT_SAME` and it is why this development is the first place the difference appears.
   */
  val AtPair: String = "INT_REAL_PAIR"

  /** `|- !a b. real_of_int (INT_ADD a b) = real_of_int a + real_of_int b` */
  val EmbedsSum: String = "INT_REAL_ADD"

  /** `|- !a b. real_of_int (INT_MUL a b) = real_of_int a * real_of_int b` */
  val EmbedsProduct: String = "INT_REAL_MUL"

  /**
   * `|- !a. real_of_int (INT_NEG a) = 0 - real_of_int a`
   *
   * Not free given [[EmbedsSum]] and [[EmbedsZero]]: getting it from those spends `INT_ADD_NEG` and an
   * identity, where by the route below it is one more pair of texts. It is published rather than
   * left to a caller because `INT_NEG` is the operation the whole type exists for, and an embedding
   * silent about it would be an embedding of the semiring.
   */
  val EmbedsNegation: String = "INT_REAL_NEG"

  /** `|- real_of_int INT_ZERO = 0` */
  val EmbedsZero: String = "INT_REAL_ZERO"

  /** `|- real_of_int INT_ONE = 1` */
  val EmbedsOne: String = "INT_REAL_ONE"

  /**
   * `|- !n. real_of_int (INT_OF_NUM n) = real_of_num n`
   *
   * The triangle, and the one fact here about all three types at once: since this development the
   * naturals reach the reals by two routes, directly and through the integers, and this says the
   * two agree. A development holding the other seven and not this one would leave two embeddings
   * that nothing related.
   */
  val EmbedsNatural: String = "INT_REAL_OF_NUM"

  /**
   * `|- !a b. real_of_int a = real_of_int b ==> a = b`
   *
   * What says the embedding loses nothing, and the one fact here whose absence would be invisible:
   * every equation above holds of the map sending every integer to zero, and so does the axiom
   * count. This is the assertion that the seven others are about an embedding rather than about a
   * collapse, and it is `INT_OF_NUM_EQ`'s argument one type up.
   */
  val EmbedsInjectively: String = "INT_REAL_INJECTIVE"

  /* ------------------------------------------------------------------ the types */

  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** `real`, which is half of every statement here and the whole reason for the file. */
  private val values: Type = Real.realType

  private val realBinary: Type = Type.fun(values, Type.fun(values, values))

  /* ------------------------------------------------------------------ the statements */

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * Read as a term rather than compared as printed text, which is the reading `RotationSpec` argues
   * for: what a reader wants to compare against the informal claim is a statement that parses back
   * to the theorem, and the parse is the stronger comparison of the two.
   */
  val Statements: Vector[(String, String)] = Vector(
    AtPair ->
      ("!p:prod(num,num). real_of_int (INT_OF_PAIR p) = " +
        "real_of_num (FST p) - real_of_num (SND p)"),
    EmbedsSum -> "!a:int b:int. real_of_int (INT_ADD a b) = real_of_int a + real_of_int b",
    EmbedsProduct -> "!a:int b:int. real_of_int (INT_MUL a b) = real_of_int a * real_of_int b",
    EmbedsNegation -> "!a:int. real_of_int (INT_NEG a) = 0 - real_of_int a",
    EmbedsZero -> "real_of_int INT_ZERO = 0",
    EmbedsOne -> "real_of_int INT_ONE = 1",
    EmbedsNatural -> "!n:num. real_of_int (INT_OF_NUM n) = real_of_num n",
    EmbedsInjectively -> "!a:int b:int. real_of_int a = real_of_int b ==> a = b"
  )

  /**
   * The standard development, which is the chain's own and not a second one beside it.
   *
   * A lookup rather than a second construction, for the reason `Integer.standard` gives: a second
   * one would put a second `real_of_int` of a different origin into the world, and `docs/adr/0008`
   * is what says two constants of one name and two origins are two constants.
   */
  lazy val standard: Inclusion = Chain.standard.inclusion

  /**
   * `\p. real_of_num (FST p) - real_of_num (SND p)`, the function being lifted.
   *
   * The annotation on the binder is not decoration. `FST` is `prod('a,'b) -> 'a` and the context
   * fixes only `'a`, so a text without it leaves the pair's second component a metavariable and is
   * refused — which is `docs/adr/0018`'s refusal working, at a type variable rather than at a
   * numeral.
   */
  private val Body: String =
    "\\p:prod(num,num). real_of_num (FST p) - real_of_num (SND p)"

  /**
   * The development, over whatever the last link of the chain is.
   *
   * `base` is the theory to **extend** and is not the whole of what this needs: `integers` supplies
   * the quotient and the arithmetic being embedded, `product` the two projection facts, `peano` the
   * facts that carry `real_of_num` through a sum, a product and a successor, and `ring` the
   * decision procedure that closes every identity left over. The two orders are different things,
   * which is `Rotation.construct`'s sentence.
   *
   * `base` has to extend `integers.theory`, and the re-basing is where that is checked: a caller
   * that placed this link below the one it embeds is refused rather than quietly building a second
   * branch off the quotient.
   */
  def construct(
    classical: Classical,
    integers: Integer,
    product: Product,
    peano: Peano,
    ring: Ring,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Inclusion] =
    for {
      quotient <- staged("re-basing the quotient", integers.quotient.over(base))
      logic <- classical.logic.over(base)

      body <- staged("reading the function to lift", Parser.term(base, notation, Body))
      respects <- staged(
        "proving the lift's obligation",
        respectfulness(logic, quotient, integers, peano, ring)
      )

      lifted <- staged("lifting it", quotient.liftPredicate(Name, body, respects))
      (widened, atPair) = lifted

      theory = widened.theory
      wider <- classical.logic.over(theory)
      definition <- widened.definition(Name)

      route <- staged(
        "assembling the rule set",
        Route.over(wider, theory, notation, widened, integers, product, peano, ring, atPair)
      )
      proved <- staged("proving the facts", route.prove)
    } yield new Inclusion(
      classical,
      theory,
      notation,
      Map(Name -> definition),
      proved + (AtPair -> atPair)
    )

  /**
   * A refusal with the stage it came from in front of it.
   *
   * The construction is one for-comprehension over six steps that each fail with a message about a
   * term, so a reader of `application: expected num, found real` learns which application only by
   * reading the file. `Route.blaming` is the same wrapper one level down, and this is the reason it
   * is there: the first run of this development refused with exactly that message and nothing in it
   * said whether the obligation, the lift or the rewriting had produced it.
   */
  private def staged[T](stage: String, result: Either[LogicError, T]): Either[LogicError, T] =
    result.left.map(error => NotOfForm(s"$stage: ${error.message}, at", Term.variable(Name, values)))

  /* ------------------------------------------------------------------ the obligation */

  /**
   * `|- !x y. INT_SAME x y ==> (real_of_num (FST x) - real_of_num (SND x) = …)`.
   *
   * What the lift asks for, and the one derivation here that has to cross between the two types
   * before any decision procedure is available. `INT_SAME x y` is an equation of `num` and the
   * conclusion an equation of `real`; nothing decides a mixed claim, so the premise is carried over
   * by applying `real_of_num` to both sides as a congruence and then pushing the embedding inside
   * the two sums with `NUM_REAL_ADD`. After that everything is an identity of the reals with the
   * four images as atoms, and `Ring` settles those.
   *
   * Writing `A`, `B`, `C`, `D` for the four images, what arrives is `A + D = C + B` and what is
   * wanted is `A - B = C - D`. Three steps, and only the middle one uses the premise:
   * `A - B = (A + D) - (B + D)` is an identity, the premise carries the first bracket to `C + B`
   * under the subtraction, and `(C + B) - (B + D) = C - D` is an identity again. The middle step is
   * two congruences rather than a rewrite because the premise is an **assumption**, and
   * `Rewrite.Rule.of` refuses a theorem carrying one.
   *
   * The two sums are read off the premise rather than rebuilt from the four images. Rebuilding
   * agrees today and is the kind of agreement that stops holding the day `NUM_REAL_ADD` is stated
   * with its sides the other way round, in a place where the mismatch prints as a `trans` that will
   * not line up.
   */
  private def respectfulness(
    logic: Logic,
    quotient: Quotient,
    integers: Integer,
    peano: Peano,
    ring: Ring
  ): Either[LogicError, Kernel.Thm] = {
    val theory = quotient.theory
    val taken = Term.freeVariables(quotient.relation)
    val x = Conv.freshVariable("x", Integer.Pairs, taken)
    val y = Conv.freshVariable("y", Integer.Pairs, taken + x)

    for {
      same <- quotient.related(x, y)
      assumed <- LogicError.lift(Kernel.assume(same))

      sameDefinition <- integers.definition(Integer.SameName)
      unfolded <- Conv.unfold(sameDefinition, List(x, y))
      overNaturals <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      embedding <- LogicError.lift(
        theory.constant(Peano.EmbeddingName, Type.fun(numbers, values))
      )
      carried <- Conv.apTerm(embedding, overNaturals)
      embedsSum <- peano.fact(Peano.EmbedsSum).flatMap(Rewrite.Rule.of(logic, _))
      premise <- Rewrite.inTheorem(Vector(embedsSum), carried)

      sides <- Term
        .destEq(premise.conclusion)
        .toRight(NotOfForm("an equation between two sums", premise.conclusion))
      (leftSum, rightSum) = sides

      first <- imageOfComponent(theory, Product.First, x)
      second <- imageOfComponent(theory, Product.Second, x)
      third <- imageOfComponent(theory, Product.First, y)
      fourth <- imageOfComponent(theory, Product.Second, y)

      subtraction <- LogicError.lift(theory.constant(Real.Subtraction, realBinary))
      addition <- LogicError.lift(theory.constant(Real.Addition, realBinary))

      shift <- applied(addition, second, fourth)
      wantedLeft <- applied(subtraction, first, second)
      wantedRight <- applied(subtraction, third, fourth)
      openedLeft <- applied(subtraction, leftSum, shift)
      openedRight <- applied(subtraction, rightSum, shift)

      opening <- equationOf(wantedLeft, openedLeft).flatMap(ring.prove)
      partial <- Conv.apTerm(subtraction, premise)
      across <- Conv.apThm(partial, shift)
      closing <- equationOf(openedRight, wantedRight).flatMap(ring.prove)

      halfway <- Conv.trans(opening, across)
      equation <- Conv.trans(halfway, closing)

      implication <- logic.rules.disch(same, equation)
      result <- logic.rules.genAll(implication, List(x, y))
    } yield result
  }

  /* ------------------------------------------------------------------ the route */

  /**
   * The rewriting that brings a statement about integers down to one about the images of
   * components, and the identity that closes it.
   *
   * Held as a value because every fact below is the same four steps over a different pair of texts,
   * and because the rule set has to be assembled once: a fact proved against a subset of it would
   * be a fact about a different normal form. It is `Integer.Laws` one type up, and the difference
   * is the last step — there a relation between two pairs and the quotient's central fact, here an
   * identity of the reals and `Ring`.
   */
  private final class Route private (
    val logic: Logic,
    val theory: Theory,
    val notation: Notation,
    val quotient: Quotient,
    val integers: Integer,
    val peano: Peano,
    val ring: Ring,
    /** The bridge, the lifts, the two pair definitions, the projections and the embedding's facts. */
    val rules: Vector[Rewrite.Rule],
    /** `INT_OF_PAIR (INT_OF_PAIR_repr a) = a`, which is what puts a fact back over `int`. */
    val representative: Rewrite.Rule,
    /** `real_of_num m + real_of_num n = real_of_num (NUM_ADD m n)`, the one rule read backwards. */
    val folding: Rewrite.Rule
  ) {

    private val a: FVar = Term.variable("a", Integer.Classes)
    private val b: FVar = Term.variable("b", Integer.Classes)
    private val x: FVar = Term.variable("x", Integer.Pairs)
    private val y: FVar = Term.variable("y", Integer.Pairs)
    private val n: FVar = Term.variable("n", numbers)

    def prove: Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        sum <- overClasses(
          EmbedsSum,
          "real_of_int (INT_ADD (INT_OF_PAIR x) (INT_OF_PAIR y))",
          "real_of_int (INT_OF_PAIR x) + real_of_int (INT_OF_PAIR y)",
          List(x, y),
          List(a, b)
        )
        product <- overClasses(
          EmbedsProduct,
          "real_of_int (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y))",
          "real_of_int (INT_OF_PAIR x) * real_of_int (INT_OF_PAIR y)",
          List(x, y),
          List(a, b)
        )
        negation <- overClasses(
          EmbedsNegation,
          "real_of_int (INT_NEG (INT_OF_PAIR x))",
          "0 - real_of_int (INT_OF_PAIR x)",
          List(x),
          List(a)
        )
        zero <- closed(EmbedsZero, "real_of_int INT_ZERO", "0")
        one <- closed(EmbedsOne, "real_of_int INT_ONE", "1")
        ofNatural <- overNaturals(EmbedsNatural, "real_of_int (INT_OF_NUM n)", "real_of_num n", List(n))
        injective <- blaming(EmbedsInjectively, "real_of_int a = real_of_int b ==> a = b", injectivity)
      } yield Map(
        EmbedsSum -> sum,
        EmbedsProduct -> product,
        EmbedsNegation -> negation,
        EmbedsZero -> zero,
        EmbedsOne -> one,
        EmbedsNatural -> ofNatural,
        EmbedsInjectively -> injective
      )

    /* ------------------------------------------------ the one route */

    /**
     * The two sides opened into images of components, and what is left handed to `Ring`.
     *
     * The normal form is not canonical and does not have to be. What the rules guarantee is that no
     * `real_of_int`, no `INT_` operation and no `real_of_num` of a compound survives, so what is
     * standing is an identity of the reals over atoms; `Ring` decides that, and a side the rules
     * failed to open is a term it refuses rather than a wrong theorem.
     */
    private def equation(leftText: String, rightText: String): Either[LogicError, Kernel.Thm] =
      for {
        left <- Parser.term(theory, notation, leftText, values)
        right <- Parser.term(theory, notation, rightText, values)
        leftNormal <- Rewrite.rewrite(rules, left)
        rightNormal <- Rewrite.rewrite(rules, right)
        leftOpened <- rightOf(leftNormal)
        rightOpened <- rightOf(rightNormal)
        identity <- equationOf(leftOpened, rightOpened).flatMap(ring.prove)
        halfway <- Conv.trans(leftNormal, identity)
        undo <- Conv.sym(rightNormal)
        result <- Conv.trans(halfway, undo)
      } yield result

    /**
     * A fact proved at carrier variables, put back over `int`.
     *
     * Specialising at `INT_OF_PAIR_repr a` and rewriting `INT_OF_PAIR (INT_OF_PAIR_repr a)` to `a`
     * is the whole of it, and it is `Integer`'s own last step. The two files reach the same place
     * from opposite sides of the projection and the helper is four lines, so it is written twice
     * rather than shared: the one there is private to a file that must not name a real, and moving
     * it to a third place neither development owns would cost more than the copy.
     */
    private def overClasses(
      name: String,
      leftText: String,
      rightText: String,
      carrierVariables: List[FVar],
      classVariables: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      blaming(
        name,
        leftText,
        equation(leftText, rightText).flatMap(
          overRepresentatives(logic, quotient, representative, _, carrierVariables, classVariables)
        )
      )

    /** A fact whose variables are naturals, which needs no representative. */
    private def overNaturals(
      name: String,
      leftText: String,
      rightText: String,
      variables: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      blaming(name, leftText, equation(leftText, rightText).flatMap(logic.rules.genAll(_, variables)))

    /** A fact with no variable in it at all, which is the two constants. */
    private def closed(
      name: String,
      leftText: String,
      rightText: String
    ): Either[LogicError, Kernel.Thm] =
      blaming(name, leftText, equation(leftText, rightText))

    /**
     * A refusal with the fact's name in front of it.
     *
     * Every fact above is the same steps over a different pair of texts, so a refusal from any of
     * them reads identically: `Ring` names two normal forms and nothing says which fact was being
     * proved. `Integer.Laws` carries the same wrapper for the same reason, and the longer comment.
     */
    private def blaming(
      name: String,
      text: String,
      result: Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      result.left.map(error =>
        NotOfForm(s"$name over `$text`, which is ${error.message}, at", Term.variable(name, values))
      )

    /* ------------------------------------------------ the one that is not that route */

    /**
     * `|- !a b. real_of_int a = real_of_int b ==> a = b`.
     *
     * The respectfulness obligation run backwards, and the only fact here that is an implication.
     * From `A - B = C - D` assumed, the identity `A + D = (A - B) + (B + D)` and the premise under
     * a congruence give `A + D = C + B`; `NUM_REAL_ADD` read **backwards** puts each sum back under
     * one `real_of_num`, which is the one place in this file a rule is reversed;
     * `NUM_REAL_INJECTIVE` takes the embedding off, leaving exactly the body of `INT_SAME x y`; and
     * `INT_EQ_PAIRS` turns that into the equation of classes wanted.
     *
     * It is not the route above for two reasons and the second is the one to carry: that route
     * proves equations, and its last step is `Ring`, which has nothing to say about an implication.
     */
    private def injectivity: Either[LogicError, Kernel.Thm] =
      for {
        leftValue <- valueAt(x)
        rightValue <- valueAt(y)
        hypothesis <- equationOf(leftValue, rightValue)
        assumed <- LogicError.lift(Kernel.assume(hypothesis))

        opened <- Rewrite.inTheorem(rules, assumed)
        differences <- Term
          .destEq(opened.conclusion)
          .toRight(NotOfForm("an equation between two differences", opened.conclusion))
        (leftDifference, rightDifference) = differences

        left <- partsOfDifference(leftDifference)
        right <- partsOfDifference(rightDifference)
        (imageA, imageB) = left
        (imageC, imageD) = right

        addition <- LogicError.lift(theory.constant(Real.Addition, realBinary))
        shift <- applied(addition, imageB, imageD)
        wantedLeft <- applied(addition, imageA, imageD)
        wantedRight <- applied(addition, imageC, imageB)
        openedLeft <- applied(addition, leftDifference, shift)
        openedRight <- applied(addition, rightDifference, shift)

        opening <- equationOf(wantedLeft, openedLeft).flatMap(ring.prove)
        partial <- Conv.apTerm(addition, opened)
        across <- Conv.apThm(partial, shift)
        closing <- equationOf(openedRight, wantedRight).flatMap(ring.prove)

        halfway <- Conv.trans(opening, across)
        overReals <- Conv.trans(halfway, closing)

        folded <- Rewrite.inTheorem(Vector(folding), overReals)
        sums <- Term
          .destEq(folded.conclusion)
          .toRight(NotOfForm("an equation between two images", folded.conclusion))

        // The two **arguments**, not the two sides: `NUM_REAL_INJECTIVE` quantifies over naturals,
        // and specialising it at the images is where this derivation first refused.
        leftNumber <- underEmbedding(sums._1)
        rightNumber <- underEmbedding(sums._2)
        injective <- peano.fact(Peano.EmbedsInjectively)
        instance <- logic.rules.specAll(injective, List(leftNumber, rightNumber))
        overNumbers <- logic.rules.mp(instance, folded)

        sameDefinition <- integers.definition(Integer.SameName)
        unfolded <- Conv.unfold(sameDefinition, List(x, y))
        related <- Conv.sym(unfolded).flatMap(flip => LogicError.lift(Kernel.eqMp(flip, overNumbers)))

        equal <- integers.fact(Integer.Equal)
        atPairs <- logic.rules.specAll(equal, List(x, y))
        classes <- Conv.sym(atPairs).flatMap(flip => LogicError.lift(Kernel.eqMp(flip, related)))

        implication <- logic.rules.disch(hypothesis, classes)
        result <- overRepresentatives(
          logic,
          quotient,
          representative,
          implication,
          List(x, y),
          List(a, b)
        )
      } yield result

    /** `real_of_int (INT_OF_PAIR p)`, as a term. */
    private def valueAt(pair: FVar): Either[LogicError, Term] =
      for {
        bridge <- LogicError.lift(theory.constant(Name, Type.fun(Integer.Classes, values)))
        projection <- LogicError.lift(
          theory.constant(Integer.Projection, Type.fun(Integer.Pairs, Integer.Classes))
        )
        projected <- LogicError.lift(Term.app(projection, pair))
        result <- LogicError.lift(Term.app(bridge, projected))
      } yield result

    /** What `real_of_num` was applied to, or a refusal naming what was found instead. */
    private def underEmbedding(term: Term): Either[LogicError, Term] =
      term match {
        case App(Const(name, _), argument) if name == Peano.EmbeddingName => Right(argument)
        case other => Left(NotOfForm("a natural under the embedding", other))
      }

    /** The two sides of a subtraction, or a refusal naming what was found instead. */
    private def partsOfDifference(term: Term): Either[LogicError, (Term, Term)] =
      term match {
        case App(App(Const(name, _), left), right) if name == Real.Subtraction =>
          Right((left, right))
        case other => Left(NotOfForm("a difference of two reals", other))
      }
  }

  private object Route {

    /**
     * The rule set, assembled once.
     *
     * The two constants and the embedding of the naturals arrive as **definitions** rather than as
     * facts, and `INT_OF_NUM`'s is a lambda: unfolding it at a variable and generalising is what
     * turns it into something a rewrite rule can be read from, which is `Integer.Laws.equationRule`
     * doing the same thing for the same reason.
     */
    def over(
      logic: Logic,
      theory: Theory,
      notation: Notation,
      quotient: Quotient,
      integers: Integer,
      product: Product,
      peano: Peano,
      ring: Ring,
      atPair: Kernel.Thm
    ): Either[LogicError, Route] = {
      val counter: FVar = Term.variable("k", numbers)

      for {
        bridge <- Rewrite.Rule.of(logic, atPair)

        addPairs <- integers.fact(Integer.AddPairs)
        negPair <- integers.fact(Integer.NegPair)
        mulPairs <- integers.fact(Integer.MulPairs)
        lifts <- Rewrite.Rule.all(logic, Vector(addPairs, negPair, mulPairs))

        firstOfPair <- product.fact(Product.FirstOfPair)
        secondOfPair <- product.fact(Product.SecondOfPair)
        projections <- Rewrite.Rule.all(logic, Vector(firstOfPair, secondOfPair))

        zeroDefinition <- integers.definition(Integer.Zero)
        oneDefinition <- integers.definition(Integer.One)
        constants <- Rewrite.Rule.all(logic, Vector(zeroDefinition, oneDefinition))

        ofNaturalDefinition <- integers.definition(Integer.OfNatural)
        ofNatural <- unfoldedRule(logic, ofNaturalDefinition, List(counter))

        embedsSum <- peano.fact(Peano.EmbedsSum)
        embedsProduct <- peano.fact(Peano.EmbedsProduct)
        embedsZero <- peano.fact(Peano.EmbedsZero)
        embedsSuccessor <- peano.fact(Peano.EmbedsSuccessor)
        embedding <- Rewrite.Rule.all(
          logic,
          Vector(embedsSum, embedsProduct, embedsZero, embedsSuccessor)
        )

        representative <- quotient
          .fact(Quotient.ProjectionOfRepresentative)
          .flatMap(Rewrite.Rule.of(logic, _))

        folding <- reversedRule(logic, embedsSum)
      } yield new Route(
        logic,
        theory,
        notation,
        quotient,
        integers,
        peano,
        ring,
        Vector(bridge) ++ lifts ++ projections ++ constants ++ Vector(ofNatural) ++ embedding,
        representative,
        folding
      )
    }

    /** `|- !k. c k = …`, which is a definition put into the shape a rewrite rule is read from. */
    private def unfoldedRule(
      logic: Logic,
      definition: Kernel.Thm,
      variables: List[FVar]
    ): Either[LogicError, Rewrite.Rule] =
      for {
        unfolded <- Conv.unfold(definition, variables.map(variable => variable: Term))
        general <- logic.rules.genAll(unfolded, variables)
        rule <- Rewrite.Rule.of(logic, general)
      } yield rule

    /**
     * A published equation read backwards, as a rule.
     *
     * The direction that **contracts**: two images under one sum are one image, so the right side
     * is smaller than the left and mentions only what the left binds. `Integer.Order` checks the
     * same thing about its own reversal, and says there that reading an equation backwards into a
     * rule is how this pair of files exhausted a heap once.
     */
    private def reversedRule(
      logic: Logic,
      theorem: Kernel.Thm
    ): Either[LogicError, Rewrite.Rule] = {
      val left: FVar = Term.variable("m", numbers)
      val right: FVar = Term.variable("n", numbers)

      for {
        instance <- logic.rules.specAll(theorem, List(left, right))
        flipped <- Conv.sym(instance)
        general <- logic.rules.genAll(flipped, List(left, right))
        rule <- Rewrite.Rule.of(logic, general)
      } yield rule
    }
  }

  /* ------------------------------------------------------------------ small shapes */

  /** `real_of_num (FST p)` and its three siblings, built over the theory that declares them. */
  private def imageOfComponent(
    theory: Theory,
    projection: String,
    pair: Term
  ): Either[LogicError, Term] =
    for {
      component <- LogicError.lift(theory.constant(projection, Type.fun(Integer.Pairs, numbers)))
      applied <- LogicError.lift(Term.app(component, pair))
      embedding <- LogicError.lift(
        theory.constant(Peano.EmbeddingName, Type.fun(numbers, values))
      )
      result <- LogicError.lift(Term.app(embedding, applied))
    } yield result

  private def applied(head: Term, left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.appAll(head, List(left, right)))

  private def equationOf(left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.eq(left, right))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * A fact proved at carrier variables, generalised over classes.
   *
   * See [[Route.overClasses]] for why it is here and private rather than taken from `Integer`.
   */
  private def overRepresentatives(
    logic: Logic,
    quotient: Quotient,
    representative: Rewrite.Rule,
    proved: Kernel.Thm,
    carrierVariables: List[FVar],
    classVariables: List[FVar]
  ): Either[LogicError, Kernel.Thm] =
    for {
      general <- logic.rules.genAll(proved, carrierVariables)
      chooser <- LogicError.lift(
        quotient.theory.constant(
          quotient.names.representative,
          Type.fun(Integer.Classes, Integer.Pairs)
        )
      )
      chosen <- classVariables.foldLeft(Right(List.empty[Term]): Either[LogicError, List[Term]]) {
        (accumulated, variable) =>
          for {
            so <- accumulated
            applied <- LogicError.lift(Term.app(chooser, variable))
          } yield so :+ applied
      }
      instance <- logic.rules.specAll(general, chosen)
      rewritten <- Rewrite.inTheorem(Vector(representative), instance)
      result <- logic.rules.genAll(rewritten, classVariables)
    } yield result
}
