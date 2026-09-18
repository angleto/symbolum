package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A type carved out of the classes of an equivalence relation, and the lifting of what acts on it.
 *
 * `docs/adr/0016` decides that a quotient is **a builder written once** rather than a construction
 * repeated per type, and this is that builder. The integers are a quotient of pairs of naturals,
 * the rationals a quotient over those, and the reals under either route `0016` leaves open a third;
 * the risk the record names is not that a quotient cannot be done but that it gets done three
 * times, discovered one at a time.
 *
 * == It is a Scala function and not a type of the object logic ==
 *
 * The shape [[Recursion]] and [[Descent]] already have. A quotient type's defining predicate names
 * the relation, and a relation is a particular term, so there is no one `quotient` operator to
 * declare: every quotient is its own `Kernel.defineType`. What is reused is the function that
 * performs it, which is why this file publishes no constant and no fact of its own and adds no link
 * to `Chain`. `docs/lemmas.md` and `docs/reading-register.md` do not move when it lands.
 *
 * == It costs no axiom beyond what the chain already holds ==
 *
 * Three things could have cost one and none of them does, which `docs/adr/0016` measured against
 * the kernel on 2026-09-15 and `QuotientSpec` asserts as an **equality** of axiom sets rather
 * than as an inclusion, the form `CodingSpec` uses:
 *
 *   - `Kernel.defineType` wants a closed predicate. The image of the relation,
 *     `\s. ?x. s = R x`, is closed whenever `R` is, and `R` being closed is the one thing this
 *     builder asks of its caller that is not a theorem.
 *   - The fact the whole thing is for, `proj x = proj y <=> R x y`, needs function
 *     extensionality in one direction. `Classical.ext` is derived from eta rather than asserted.
 *   - The lifting needs a representative of a class, and the chooser is `select` applied to the
 *     surjectivity of the projection. That is the choice axiom, which the chain already holds and
 *     which `Product.FST` already spends for exactly this reason. Over `num` modulo two it adds
 *     **nothing**, the carrier having spent choice already; over a carrier that has not, it adds
 *     one. That is a fact about the carrier rather than about this builder, and `QuotientSpec`
 *     says so where it measures it.
 *
 * So what a development built through here rests on is what its carrier rested on, and nothing
 * else. That is the claim worth checking and it is checked.
 *
 * == What it produces ==
 *
 * [[Quotient.define]] returns a [[Quotient]] carrying the extended theory, the type, the two halves
 * of the bijection the kernel returned, the projection and four derived facts. Then
 * [[Quotient.liftUnary]], [[Quotient.liftBinary]] and [[Quotient.liftPredicate]] each extend it by
 * one constant and one fact, against an obligation the caller discharges:
 *
 * {{{
 *   PROJ_EQ     |- !x y. (proj x = proj y) = R x y
 *   PROJ_ONTO   |- !q. ?x. q = proj x
 *   PROJ_REPR   |- !q. proj (repr q) = q
 *   REPR_REL    |- !x. R x (repr (proj x))
 *
 *   liftUnary     f  against  |- !x y. R x y ==> R (f x) (f y)
 *                 gives       |- !x. g (proj x) = proj (f x)
 *   liftBinary    f  against  |- !x y u v. R x u ==> R y v ==> R (f x y) (f u v)
 *                 gives       |- !x y. g (proj x) (proj y) = proj (f x y)
 *   liftPredicate p  against  |- !x y. R x y ==> (p x = p y)
 *                 gives       |- !x. g (proj x) = p x
 * }}}
 *
 * **The obligation is the caller's and is not checked by inspection.** A lift takes a theorem of
 * the stated shape and refuses anything else by name; it does not read `f` and decide whether it
 * respects the relation, because that is undecidable in general and the special cases where it is
 * syntactic belong to whatever procedure reads shapes, not here.
 *
 * == The one fact that looks redundant and is not ==
 *
 * [[Quotient.RelatedToRepresentative]], `!x. R x (repr (proj x))`, follows from
 * [[Quotient.ProjectionEqual]] and [[Quotient.ProjectionOfRepresentative]] in two steps, and every
 * one of the three lifts takes those two steps. It is derived once and held because a lift is the
 * thing a caller repeats: the integers lift addition, multiplication, negation and the order, so
 * the two steps would be walked at least four times in the first consumer and three times again in
 * the second.
 *
 * == What is not here ==
 *
 * No induction over the quotient, no lifting of a relation of two quotient arguments other than
 * through [[liftBinary]] at `bool`, and no lifting of a function whose result is **not** quotiented
 * (`num`-valued, say). Each is a further step of the same kind and none of them is needed by the
 * integers, which is the criterion `docs/adr/0016` sets for this piece: validated on a toy quotient
 * and then measured by its first real consumer, not grown ahead of one.
 *
 * No notation. A quotient's operations are written by the names the caller gave them.
 */
final class Quotient private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  /** The logic reading against [[theory]], which is wider than the classical one. */
  val logic: Logic,
  /** The relation the classes are of, as the closed term the caller supplied. */
  val relation: Term,
  /** The type of what is being quotiented. */
  val carrier: Type,
  /** The type this development defined. */
  val classes: Type,
  /**
   * The names this quotient's constants were given.
   *
   * Held rather than recomputed because every lift has to name the projection and the chooser, and
   * a builder that rebuilt a name from a convention would be a second place the convention is
   * written.
   */
  val names: Quotient.Names,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `proj x`, as a term, for a caller holding the element rather than its spelling. */
  def project(element: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(names.projection, Type.fun(carrier, classes)))
      applied <- LogicError.lift(Term.app(constant, element))
    } yield applied

  /** `R x y`, as a term, built from the relation this quotient was given. */
  def related(left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.appAll(relation, List(left, right)))

  /**
   * A unary operation on the carrier, lifted to the classes.
   *
   * `respects` is `|- !x y. R x y ==> R (f x) (f y)` and is the whole of what makes this sound: the
   * lifted function is defined through a **chosen** representative, so two representatives of one
   * class must send `f` into one class or the definition means nothing. Refused by name when the
   * theorem is not of that shape.
   */
  def liftUnary(
    name: String,
    operation: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] =
    Quotient.liftUnary(this, name, operation, respects)

  /**
   * A binary operation on the carrier, lifted to the classes.
   *
   * `respects` is `|- !x y u v. R x u ==> R y v ==> R (f x y) (f u v)`, curried rather than
   * conjunctive because that is the shape `Modular` already publishes its congruence compatibility
   * in and because two `Rules.mp` is what a consumer writes either way.
   */
  def liftBinary(
    name: String,
    operation: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] =
    Quotient.liftBinary(this, name, operation, respects)

  /**
   * A predicate on the carrier, lifted to the classes.
   *
   * `respects` is `|- !x y. R x y ==> (p x = p y)`, an equation at `bool` rather than an
   * implication: a predicate true of one representative and false of another does not lift, and the
   * implication in one direction alone would not say so.
   */
  def liftPredicate(
    name: String,
    predicate: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] =
    Quotient.liftPredicate(this, name, predicate, respects)

}

object Quotient {

  /**
   * What the caller supplies about the relation, and the only three theorems this builder asks for.
   *
   * The shapes are the ones the repository already publishes. `Modular.CongTrans` is curried, so
   * transitivity is taken curried; taking it conjunctive would make every caller reshape a theorem
   * it already holds, and the reshaping is where a caller gets the argument order wrong.
   *
   * **The relation is a closed term and need not be a constant.** `NUM_CONG 2` is a partial
   * application of a ternary constant to a numeral, it is closed, and `Kernel.defineType` asks for
   * nothing more. That is what lets the toy validation be a real congruence instead of a relation
   * invented for the test.
   */
  final case class Equivalence(
    relation: Term,
    /** `|- !x. R x x` */
    reflexive: Kernel.Thm,
    /** `|- !x y. R x y ==> R y x` */
    symmetric: Kernel.Thm,
    /** `|- !x y z. R x y ==> R y z ==> R x z` */
    transitive: Kernel.Thm
  )

  /**
   * The five names a quotient introduces, all of them the caller's.
   *
   * `docs/adr/0008` is why they are not derived from the type name by a rule written here: a
   * constant carries what defined it, so two quotients of one relation under two naming schemes
   * would be two different constants, and the scheme belongs to the development that owns the type.
   */
  final case class Names(
    typeName: String,
    abstraction: String,
    representation: String,
    projection: String
  ) {
    /** The chooser of a representative, named off the projection so a caller supplies four. */
    def representative: String = s"${projection}_repr"
  }

  /** `|- !x y. (proj x = proj y) = R x y`, the fact the type is defined for. */
  val ProjectionEqual: String = "PROJ_EQ"

  /** `|- !q. ?x. q = proj x`: every class has a member. */
  val ProjectionOnto: String = "PROJ_ONTO"

  /** `|- !q. proj (repr q) = q`: the chosen representative is one. */
  val ProjectionOfRepresentative: String = "PROJ_REPR"

  /** `|- !x. R x (repr (proj x))`: and it is related to the one you started with. */
  val RelatedToRepresentative: String = "REPR_REL"

  /** The two theorems `Kernel.defineType` returns, named as `Product` names its pair. */
  val AbstractionOfRepresentation: String = "QUOT_ABS_REP"
  val Characterisation: String = "QUOT_REP_ABS"

  /**
   * Carve the classes of an equivalence relation out of the predicates on its carrier.
   *
   * The carrier type is read off the relation rather than passed in, so a caller cannot disagree
   * with the kernel about it. Everything else the kernel decides — the arity of the type operator,
   * the order of its parameters — is read back off the theorems it returns for the same reason:
   * `Product` reconstructs those and this does not, because the one place the two could drift is
   * exactly the place a mismatch prints as a `trans` that will not line up.
   */
  def define(
    classical: Classical,
    base: Theory,
    notation: Notation,
    names: Names,
    equivalence: Equivalence
  ): Either[LogicError, Quotient] = {
    val relation = equivalence.relation

    for {
      carrier <- carrierOf(relation)

      _ <-
        if (Term.freeVariables(relation).isEmpty) Right(())
        else Left(NotOfForm("a closed relation", relation))

      narrow <- classical.logic.over(base)

      predicate <- imageOf(narrow, relation, carrier)
      sample = Conv.freshVariable("x", carrier, Term.freeVariables(predicate))
      witness <- represented(narrow, relation, predicate, sample)

      typed <- LogicError.lift(
        Kernel.defineType(base, names.typeName, names.abstraction, names.representation, witness)
      )
      (withType, bijection) = typed
      (absRep, characterisation) = bijection

      // The abstract type as the kernel built it, read off `|- abs (rep a) = a` rather than
      // rebuilt from the predicate's type variables. Rebuilding agrees today, and it is the kind
      // of agreement that stops holding the day the kernel's rule for ordering the parameters
      // changes, in a place where the mismatch prints as a `trans` that will not line up.
      abstractVariable <- variableSideOf(absRep)
      classes = abstractVariable.ty

      abstraction <- LogicError.lift(
        withType.constant(names.abstraction, Type.fun(Type.fun(carrier, Type.Bool), classes))
      )
      representation <- LogicError.lift(
        withType.constant(names.representation, Type.fun(classes, Type.fun(carrier, Type.Bool)))
      )

      projectionBody <- projectionOf(abstraction, relation, carrier)
      projected <- LogicError.lift(
        Kernel.defineConstant(withType, names.projection, projectionBody)
      )
      (withProjection, projectionDefinition) = projected

      wider <- classical.logic.over(withProjection)
      projection <- LogicError.lift(
        withProjection.constant(names.projection, Type.fun(carrier, classes))
      )

      shapes <- Shapes.of(wider, relation, carrier, equivalence)

      vocabulary = Vocabulary(
        relation,
        carrier,
        classes,
        abstraction,
        representation,
        projection,
        predicate,
        characterisation,
        projectionDefinition
      )

      equal <- projectionEqual(classical, wider, vocabulary, shapes)
      onto <- projectionOnto(wider, vocabulary, absRep, abstractVariable)

      chosen <- representative(classical, wider, withProjection, names, carrier, classes, onto)
      (complete, representativeDefinition, projectionOfRepresentative) = chosen

      widest <- classical.logic.over(complete)
      related <- relatedToRepresentative(
        widest,
        relation,
        carrier,
        classes,
        complete,
        names,
        projectionOfRepresentative,
        equal
      )
    } yield new Quotient(
      classical,
      complete,
      notation,
      widest,
      relation,
      carrier,
      classes,
      names,
      Map(
        names.projection -> projectionDefinition,
        names.representative -> representativeDefinition
      ),
      Map(
        AbstractionOfRepresentation -> absRep,
        Characterisation -> characterisation,
        ProjectionEqual -> equal,
        ProjectionOnto -> onto,
        ProjectionOfRepresentative -> projectionOfRepresentative,
        RelatedToRepresentative -> related
      )
    )
  }

  /* ------------------------------------------------------------------ the predicate and witness */

  /** The carrier, read off `R : A -> A -> bool` and refused when the relation is not of that type. */
  private def carrierOf(relation: Term): Either[LogicError, Type] =
    Type.destFun(Term.typeOf(relation)) match {
      case Some((domain, rest)) =>
        Type.destFun(rest) match {
          case Some((second, Type.Bool)) if second == domain => Right(domain)
          case _ => Left(NotOfForm("a relation of two arguments of one type", relation))
        }
      case None => Left(NotOfForm("a relation of two arguments of one type", relation))
    }

  /**
   * `\s. ?x. s = R x`, the image of the relation seen as a map into the predicates.
   *
   * A class is the set of what is related to one element, and what makes the classes a type is that
   * this map's image is exactly the classes. Left as a lambda rather than given a constant, which
   * is `Product`'s choice for its own predicate and for its reason: nothing but the three steps
   * crossing the bijection ever mentions it, and a constant would put a name in a caller's
   * signature that no statement of the caller's uses.
   */
  private def imageOf(
    logic: Logic,
    relation: Term,
    carrier: Type
  ): Either[LogicError, Term] = {
    val classType = Type.fun(carrier, Type.Bool)
    val s = Conv.freshVariable("s", classType, Term.freeVariables(relation))
    val x = Conv.freshVariable("x", carrier, Term.freeVariables(relation) + s)

    for {
      atX <- LogicError.lift(Term.app(relation, x))
      equation <- LogicError.lift(Term.eq(s, atX))
      body <- logic.mkExists(x, equation)
      lambda <- LogicError.lift(Term.abs(s, body))
    } yield lambda
  }

  /**
   * `|- P (R x)`, the witness `Kernel.defineType` will not run without.
   *
   * `R x` is `R` of something by reflexivity of equality, which is the whole derivation, and it is
   * `Product.pairIsRepresented` with one existential instead of two. The application is **not**
   * contracted, for the reason that file gives: the rule reads `P` off the outermost application,
   * so a reduced witness would define the type of things equal to this one class.
   */
  private def represented(
    logic: Logic,
    relation: Term,
    predicate: Term,
    element: FVar
  ): Either[LogicError, Kernel.Thm] =
    for {
      representative <- LogicError.lift(Term.app(relation, element))
      applied <- LogicError.lift(Term.app(predicate, representative))
      contraction <- Conv.betaRoot(applied)
      goal <- rightOf(contraction)
      inner <- logic
        .destExistsPredicate(goal)
        .toRight(NotOfForm("a claim that something is a class", goal))
      introduced <- logic.rules.existsIntro(inner, element, Conv.refl(representative))
      back <- Conv.sym(contraction)
      result <- LogicError.lift(Kernel.eqMp(back, introduced))
    } yield result

  /** `\x. abs (R x)`, the body of the projection. */
  private def projectionOf(
    abstraction: Term,
    relation: Term,
    carrier: Type
  ): Either[LogicError, Term] = {
    val x = Conv.freshVariable("x", carrier, Term.freeVariables(relation))
    for {
      atX <- LogicError.lift(Term.app(relation, x))
      abstracted <- LogicError.lift(Term.app(abstraction, atX))
      lambda <- LogicError.lift(Term.abs(x, abstracted))
    } yield lambda
  }

  /* ------------------------------------------------------------------ the three equivalence facts */

  /**
   * The three theorems the caller supplied, checked against the shapes this builder states.
   *
   * Checked rather than trusted, and refused **by which one** rather than by a single message: a
   * caller handing symmetry where transitivity was wanted gets a failure several derivations later
   * with a `trans` that will not line up, and the name of the wrong argument is the one piece of
   * information that failure does not carry.
   */
  private final case class Shapes(
    reflexive: Kernel.Thm,
    symmetric: Kernel.Thm,
    transitive: Kernel.Thm
  )

  private object Shapes {
    def of(
      logic: Logic,
      relation: Term,
      carrier: Type,
      equivalence: Equivalence
    ): Either[LogicError, Shapes] = {
      val taken = Term.freeVariables(relation)
      val x = Conv.freshVariable("x", carrier, taken)
      val y = Conv.freshVariable("y", carrier, taken + x)
      val z = Conv.freshVariable("z", carrier, taken + x + y)

      def rel(left: FVar, right: FVar): Either[LogicError, Term] =
        LogicError.lift(Term.appAll(relation, List(left, right)))

      for {
        xx <- rel(x, x)
        reflexiveWanted <- logic.mkForall(x, xx)
        _ <- sameAs("reflexivity of the relation", reflexiveWanted, equivalence.reflexive)

        xy <- rel(x, y)
        yx <- rel(y, x)
        symmetricBody <- logic.mkImp(xy, yx)
        symmetricInner <- logic.mkForall(y, symmetricBody)
        symmetricWanted <- logic.mkForall(x, symmetricInner)
        _ <- sameAs("symmetry of the relation", symmetricWanted, equivalence.symmetric)

        yz <- rel(y, z)
        xz <- rel(x, z)
        transitiveTail <- logic.mkImp(yz, xz)
        transitiveBody <- logic.mkImp(xy, transitiveTail)
        transitiveInnermost <- logic.mkForall(z, transitiveBody)
        transitiveInner <- logic.mkForall(y, transitiveInnermost)
        transitiveWanted <- logic.mkForall(x, transitiveInner)
        _ <- sameAs("transitivity of the relation, curried", transitiveWanted, equivalence.transitive)
      } yield Shapes(equivalence.reflexive, equivalence.symmetric, equivalence.transitive)
    }

    private def sameAs(
      what: String,
      wanted: Term,
      supplied: Kernel.Thm
    ): Either[LogicError, Unit] =
      if (supplied.hypotheses.nonEmpty)
        Left(NotOfForm(s"$what, with nothing assumed", supplied.conclusion))
      else if (supplied.conclusion == wanted) Right(())
      else Left(NotOfForm(what, supplied.conclusion))
  }

  /* ------------------------------------------------------------------ what the derivations share */

  private final case class Vocabulary(
    relation: Term,
    carrier: Type,
    classes: Type,
    abstraction: Term,
    representation: Term,
    projection: Term,
    predicate: Term,
    characterisation: Kernel.Thm,
    projectionDefinition: Kernel.Thm
  ) {
    def rel(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(relation, List(left, right)))

    def project(element: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(projection, element))
  }

  /**
   * `|- rep (proj x) = R x`: the representation undoes the projection.
   *
   * The bridge every derivation here crosses, and `Product.representationOfPair` is the same step
   * for the pair. `proj x` unfolds to `abs (R x)`, and the characterisation says `rep` undoes `abs`
   * on a term satisfying the predicate and on nothing else, which is why the witness is needed a
   * second time and at the caller's element rather than at a sample.
   */
  private def representationOfProjection(
    logic: Logic,
    vocabulary: Vocabulary,
    element: FVar
  ): Either[LogicError, Kernel.Thm] =
    for {
      holds <- represented(logic, vocabulary.relation, vocabulary.predicate, element)
      atClass <- LogicError.lift(Term.app(vocabulary.relation, element))
      variable = Term.variable("r", Type.fun(vocabulary.carrier, Type.Bool))
      at <- LogicError.lift(Kernel.inst(Map(variable -> atClass), vocabulary.characterisation))
      undone <- LogicError.lift(Kernel.eqMp(at, holds))

      unfolded <- Conv.unfold(vocabulary.projectionDefinition, List(element))
      carried <- Conv.apTerm(vocabulary.representation, unfolded)
      result <- Conv.trans(carried, undone)
    } yield result

  /**
   * `|- !x y. (proj x = proj y) = R x y`.
   *
   * The two directions cost quite different things and it is worth knowing which is which before
   * reading them.
   *
   * **Left to right is bookkeeping.** Apply `rep` to the assumed equation, cross twice by
   * [[representationOfProjection]] to get `R x = R y`, apply both sides at `y` to get
   * `R x y = R y y`, and `R y y` is reflexivity. No classical step and no extensionality.
   *
   * **Right to left is where the whole cost of the type sits.** From `R x y` one has to reach the
   * equality of two **functions**, `R x = R y`, and pointwise agreement gives that only through
   * function extensionality. Each point is a biconditional built by `Kernel.deductAntisym` out of
   * two uses of transitivity, one of which needs symmetry to turn `R x y` round. That is the whole
   * reason [[Equivalence]] asks for three theorems rather than for one.
   *
   * Put together with `deductAntisym` in that order, so the conclusion reads
   * `(proj x = proj y) = R x y` and not the other way about: a consumer rewriting with it wants the
   * projection on the left, since what it holds is an equation between classes.
   */
  private def projectionEqual(
    classical: Classical,
    logic: Logic,
    vocabulary: Vocabulary,
    shapes: Shapes
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val taken = Term.freeVariables(vocabulary.relation)
    val x = Conv.freshVariable("x", vocabulary.carrier, taken)
    val y = Conv.freshVariable("y", vocabulary.carrier, taken + x)
    val z = Conv.freshVariable("z", vocabulary.carrier, taken + x + y)

    for {
      projectedX <- vocabulary.project(x)
      projectedY <- vocabulary.project(y)
      equalProjections <- LogicError.lift(Term.eq(projectedX, projectedY))
      relatedXY <- vocabulary.rel(x, y)

      forward <- forwardDirection(logic, vocabulary, shapes, x, y, equalProjections)
      backward <- backwardDirection(classical, logic, vocabulary, shapes, x, y, z, relatedXY)

      // `deductAntisym(left, right)` concludes `left.conclusion = right.conclusion` and drops each
      // side's assumption from the other, so passing the backward direction first is what puts the
      // projection on the left and leaves nothing assumed.
      biconditional = Kernel.deductAntisym(backward, forward)
      result <- rules.genAll(biconditional, List(x, y))
    } yield result
  }

  /** `proj x = proj y |- R x y`. */
  private def forwardDirection(
    logic: Logic,
    vocabulary: Vocabulary,
    shapes: Shapes,
    x: FVar,
    y: FVar,
    equalProjections: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(equalProjections))
      carried <- Conv.apTerm(vocabulary.representation, assumed)

      atX <- representationOfProjection(logic, vocabulary, x)
      atY <- representationOfProjection(logic, vocabulary, y)

      fromX <- Conv.sym(atX)
      throughY <- Conv.trans(fromX, carried)
      // `|- R x = R y`, an equation between two functions on the carrier.
      functions <- Conv.trans(throughY, atY)

      // Applied at `y`, so that the right side becomes `R y y` and reflexivity closes it. At `x`
      // the left becomes `R x x` and the same argument runs the other way round; at anything else
      // neither side is closed by anything this development holds.
      pointwise <- Conv.apThm(functions, y)
      reflexiveAtY <- rules.spec(y, shapes.reflexive)
      back <- Conv.sym(pointwise)
      result <- LogicError.lift(Kernel.eqMp(back, reflexiveAtY))
    } yield result
  }

  /** `R x y |- proj x = proj y`. */
  private def backwardDirection(
    classical: Classical,
    logic: Logic,
    vocabulary: Vocabulary,
    shapes: Shapes,
    x: FVar,
    y: FVar,
    z: FVar,
    relatedXY: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      assumed <- LogicError.lift(Kernel.assume(relatedXY))

      // `R y x`, which is the only place symmetry is spent in the whole file.
      symmetricAt <- rules.specAll(shapes.symmetric, List(x, y))
      reversed <- rules.mp(symmetricAt, assumed)

      relatedXZ <- vocabulary.rel(x, z)
      relatedYZ <- vocabulary.rel(y, z)

      // `R x z |- R y z`, by `R y x` and transitivity.
      assumedXZ <- LogicError.lift(Kernel.assume(relatedXZ))
      throughX <- rules.specAll(shapes.transitive, List(y, x, z))
      throughXOnce <- rules.mp(throughX, reversed)
      leftToRight <- rules.mp(throughXOnce, assumedXZ)

      // `R y z |- R x z`, by `R x y` and transitivity.
      assumedYZ <- LogicError.lift(Kernel.assume(relatedYZ))
      throughY <- rules.specAll(shapes.transitive, List(x, y, z))
      throughYOnce <- rules.mp(throughY, assumed)
      rightToLeft <- rules.mp(throughYOnce, assumedYZ)

      // `R x y |- R x z = R y z`: each side drops the other's assumption, and `R x y` is left
      // because both halves rest on it.
      atPoint = Kernel.deductAntisym(rightToLeft, leftToRight)
      generalised <- rules.gen(z, atPoint)

      // The one use of extensionality, and the reason the builder costs eta and nothing more.
      functions <- classical.ext(logic, generalised)

      carried <- Conv.apTerm(vocabulary.abstraction, functions)
      unfoldedX <- Conv.unfold(vocabulary.projectionDefinition, List(x))
      unfoldedY <- Conv.unfold(vocabulary.projectionDefinition, List(y))
      backY <- Conv.sym(unfoldedY)
      fromProjection <- Conv.trans(unfoldedX, carried)
      result <- Conv.trans(fromProjection, backY)
    } yield result
  }

  /**
   * `|- !q. ?x. q = proj x`: the projection is onto.
   *
   * What makes a representative choosable, and the fact `Product.Cases` is for the pair. The route
   * is the same one: `abs (rep q) = q` is one half of the bijection, applying `rep` to it gives
   * `rep (abs (rep q)) = rep q`, which is the right side of the characterisation at `rep q`, so
   * `P (rep q)` holds and unfolds to `?x. rep q = R x`. At such an `x`, `proj x` is `abs (R x)` is
   * `abs (rep q)` is `q`.
   */
  private def projectionOnto(
    logic: Logic,
    vocabulary: Vocabulary,
    absRep: Kernel.Thm,
    abstractVariable: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val taken = Term.freeVariables(vocabulary.relation)
    val q = Conv.freshVariable("q", vocabulary.classes, taken)

    for {
      atQ <- LogicError.lift(Kernel.inst(Map(abstractVariable -> q), absRep))

      representedQ <- LogicError.lift(Term.app(vocabulary.representation, q))
      carried <- Conv.apTerm(vocabulary.representation, atQ)

      characterisationVariable = Term.variable("r", Type.fun(vocabulary.carrier, Type.Bool))
      atClass <- LogicError.lift(
        Kernel.inst(Map(characterisationVariable -> representedQ), vocabulary.characterisation)
      )
      back <- Conv.sym(atClass)
      holds <- LogicError.lift(Kernel.eqMp(back, carried))

      contraction <- Conv.betaRoot(holds.conclusion)
      opened <- LogicError.lift(Kernel.eqMp(contraction, holds))

      goal <- ontoGoal(logic, vocabulary, q)
      chosen <- eliminateInto(logic, vocabulary, opened, q, atQ, goal)
      result <- rules.gen(q, chosen)
    } yield result
  }

  /** `?x. q = proj x`, the statement [[projectionOnto]] proves at each `q`. */
  private def ontoGoal(
    logic: Logic,
    vocabulary: Vocabulary,
    q: FVar
  ): Either[LogicError, Term] = {
    val x = Conv.freshVariable("x", vocabulary.carrier, Term.freeVariables(vocabulary.relation) + q)
    for {
      projected <- vocabulary.project(x)
      equation <- LogicError.lift(Term.eq(q, projected))
      existential <- logic.mkExists(x, equation)
    } yield existential
  }

  /**
   * From `?x. rep q = R x` to `?x. q = proj x`, by eliminating the first at a fresh name.
   *
   * The step that has to name the witness, because what is wanted about it is not what is known
   * about it: `rep q = R x` is a statement about the representation and `q = proj x` is one about
   * the projection, and `abs` is what carries the first to the second.
   */
  private def eliminateInto(
    logic: Logic,
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    q: FVar,
    absRepAtQ: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val taken = Term.freeVariables(existential.conclusion) + q
    val x = Conv.freshVariable("x", vocabulary.carrier, taken)

    for {
      predicate <- logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("a claim that the representation is a class", existential.conclusion))
      applied <- LogicError.lift(Term.app(predicate, x))
      instance <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
      assumed <- LogicError.lift(Kernel.assume(instance))

      // `abs (rep q) = abs (R x)`, then `q = proj x` by the two equations either side of it.
      carried <- Conv.apTerm(vocabulary.abstraction, assumed)
      fromQ <- Conv.sym(absRepAtQ)
      throughAbs <- Conv.trans(fromQ, carried)
      unfolded <- Conv.unfold(vocabulary.projectionDefinition, List(x))
      backToProjection <- Conv.sym(unfolded)
      reached <- Conv.trans(throughAbs, backToProjection)

      outer <- logic
        .destExistsPredicate(goal)
        .toRight(NotOfForm("a claim that the class has a member", goal))
      introduced <- rules.existsIntro(outer, x, reached)
      result <- rules.existsElim(existential, x, introduced)
    } yield result
  }

  /* ------------------------------------------------------------------ the chosen representative */

  /**
   * The constant that picks a member of a class, and the fact that it picks one.
   *
   * `repr = \q. select (\x. q = proj x)`, and `|- !q. proj (repr q) = q`.
   *
   * **The body is read off the surjectivity theorem rather than built here**, which is the one
   * thing in this function worth slowing down for. The choice axiom applied to `?x. q = proj x`
   * hands back a statement about `select` of *the predicate that theorem carries*, and a predicate
   * built independently would be equal by construction today and is exactly the pair of terms
   * `Product.pairIsRepresented` warns about: two spellings of one thing, trusted to agree, which is
   * how `Rules.existsIntro` comes to refuse a correct step.
   */
  private def representative(
    classical: Classical,
    logic: Logic,
    theory: Theory,
    names: Names,
    carrier: Type,
    classes: Type,
    onto: Kernel.Thm
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val q = Conv.freshVariable("q", classes, Term.freeVariables(onto.conclusion))

    for {
      atQ <- rules.spec(q, onto)
      predicate <- logic
        .destExistsPredicate(atQ.conclusion)
        .toRight(NotOfForm("a claim that the class has a member", atQ.conclusion))

      // `Classical.select` reads against the classical extension's **own** theory, which has never
      // heard of the carrier: `Chain.standard.classical` does not know `num`, so asking it for the
      // choice operator at `num` is refused with "no type operator named num in this theory". The
      // constant is taken from the theory being extended instead, which is the same widening
      // `Classical.ext(wider, _)` takes an argument for and that `Divisibility` documents for
      // quantifier introduction: a polymorphic constant is declared once and named where the types
      // live. Found by the eleven failures this caused rather than by reading the signature.
      select <- LogicError.lift(
        theory.constant(Classical.Select, Type.fun(Type.fun(carrier, Type.Bool), carrier))
      )
      chosenTerm <- LogicError.lift(Term.app(select, predicate))
      body <- LogicError.lift(Term.abs(q, chosenTerm))

      defined <- LogicError.lift(Kernel.defineConstant(theory, names.representative, body))
      (complete, definition) = defined

      wider <- classical.logic.over(complete)
      choice <- classical.axiom(Classical.Choice)
      // `|- q = proj (select (\x. q = proj x))`, unreduced as `witnessFrom` hands it back.
      picked <- Classical.witnessFrom(wider, choice, atQ)
      normalised <- reduced(picked)

      unfolded <- Conv.unfold(definition, List(q))
      projection <- LogicError.lift(complete.constant(names.projection, Type.fun(carrier, classes)))
      carried <- Conv.apTerm(projection, unfolded)

      // `proj (repr q) = proj (select ...) = q`.
      back <- Conv.sym(normalised)
      joined <- Conv.trans(carried, back)
      result <- wider.rules.gen(q, joined)
    } yield (complete, definition, result)
  }

  /**
   * `|- !x. R x (repr (proj x))`.
   *
   * Two steps from [[ProjectionEqual]] and [[ProjectionOfRepresentative]], derived once because
   * every lift takes them: `proj (repr (proj x)) = proj x` is the second fact at `proj x`, and the
   * first fact read backwards turns that equation into the relation.
   *
   * The argument order is `R x (repr (proj x))` and not the reverse, which matters at the call
   * sites: a lift needs `R x x'` with `x` the element the caller named and `x'` the chosen
   * representative, so that respectfulness applies in the direction its statement is written in.
   */
  private def relatedToRepresentative(
    logic: Logic,
    relation: Term,
    carrier: Type,
    classes: Type,
    theory: Theory,
    names: Names,
    projectionOfRepresentative: Kernel.Thm,
    equal: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Conv.freshVariable("x", carrier, Term.freeVariables(relation))

    for {
      projection <- LogicError.lift(theory.constant(names.projection, Type.fun(carrier, classes)))
      projected <- LogicError.lift(Term.app(projection, x))

      // `|- proj (repr (proj x)) = proj x`.
      atClass <- rules.spec(projected, projectionOfRepresentative)

      // The equation is turned round **here**, before the relation is reached at all, and that is
      // the whole reason this fact needs no appeal to the relation's own symmetry: `R x c` and
      // `R c x` are two specialisations of [[ProjectionEqual]], and which one comes out is decided
      // by which way the equation between the two classes is pointing when it is spent.
      //
      // Which way round is not a taste. Respectfulness is stated `R x y ==> R (f x) (f y)`, and a
      // lift detaches it with the element the caller named in the first position, so a fact
      // concluding `R (repr (proj x)) x` would apply in the wrong direction and fail to line up one
      // derivation later with nothing naming the cause.
      turned <- Conv.sym(atClass)

      chosen <- representativeIn(atClass)
      instance <- rules.specAll(equal, List(x, chosen))
      related <- LogicError.lift(Kernel.eqMp(instance, turned))

      result <- rules.gen(x, related)
    } yield result
  }

  /** `repr (proj x)`, read off the left side of `proj (repr (proj x)) = proj x`. */
  private def representativeIn(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion) match {
      case Some((App(_, inner), _)) => Right(inner)
      case _ =>
        Left(NotOfForm("the projection of a chosen representative", theorem.conclusion))
    }

  /* ------------------------------------------------------------------ the three lifts */

  /**
   * A unary operation lifted, `|- !x. g (proj x) = proj (f x)`.
   *
   * The definition is `g = \q. proj (f (repr q))` and the fact is what says the chosen
   * representative did not matter. Read the derivation in that order: `g (proj x)` unfolds to
   * `proj (f (repr (proj x)))`, [[RelatedToRepresentative]] says `x` and that representative are
   * related, respectfulness carries the relation through `f`, and [[ProjectionEqual]] turns the
   * relation back into an equation between classes.
   */
  private def liftUnary(
    quotient: Quotient,
    name: String,
    operation: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] = {
    val carrier = quotient.carrier
    val classes = quotient.classes
    val taken = Term.freeVariables(quotient.relation)
    val x = Conv.freshVariable("x", carrier, taken)
    val y = Conv.freshVariable("y", carrier, taken + x)
    val q = Conv.freshVariable("q", classes, taken)

    for {
      _ <- checkUnary(quotient, operation, respects, x, y)

      representativeConstant <- LogicError.lift(
        quotient.theory.constant(quotient.names.representative, Type.fun(classes, carrier))
      )
      projection <- LogicError.lift(
        quotient.theory.constant(quotient.names.projection, Type.fun(carrier, classes))
      )

      chosen <- LogicError.lift(Term.app(representativeConstant, q))
      applied <- applyTo(operation, List(chosen))
      projected <- LogicError.lift(Term.app(projection, applied))
      body <- LogicError.lift(Term.abs(q, projected))

      defined <- LogicError.lift(Kernel.defineConstant(quotient.theory, name, body))
      (complete, definition) = defined
      wider <- quotient.classical.logic.over(complete)

      related <- quotient.fact(RelatedToRepresentative)
      equal <- quotient.fact(ProjectionEqual)

      projectedX <- LogicError.lift(Term.app(projection, x))
      relatedAtX <- wider.rules.spec(x, related)
      chosenAtX <- secondArgument(relatedAtX)

      respectsAt <- wider.rules.specAll(respects, List(x, chosenAtX))
      carriedRelation <- wider.rules.mp(respectsAt, relatedAtX)

      appliedX <- applyTo(operation, List(x))
      appliedChosen <- applyTo(operation, List(chosenAtX))
      equalAt <- wider.rules.specAll(equal, List(appliedX, appliedChosen))
      back <- Conv.sym(equalAt)
      classesEqual <- LogicError.lift(Kernel.eqMp(back, carriedRelation))

      unfolded <- Conv.unfold(definition, List(projectedX))
      normalised <- reduced(unfolded)
      backwards <- Conv.sym(classesEqual)
      result <- Conv.trans(normalised, backwards)
      generalised <- wider.rules.gen(x, result)

      extended = extend(quotient, complete, wider, name, definition)
    } yield (extended, generalised)
  }

  /** `|- !x y. R x y ==> R (f x) (f y)`, checked rather than trusted. */
  private def checkUnary(
    quotient: Quotient,
    operation: Term,
    respects: Kernel.Thm,
    x: FVar,
    y: FVar
  ): Either[LogicError, Unit] =
    for {
      appliedX <- applyTo(operation, List(x))
      appliedY <- applyTo(operation, List(y))
      relatedArguments <- quotient.related(x, y)
      relatedResults <- quotient.related(appliedX, appliedY)
      body <- quotient.logic.mkImp(relatedArguments, relatedResults)
      inner <- quotient.logic.mkForall(y, body)
      wanted <- quotient.logic.mkForall(x, inner)
      _ <-
        if (respects.hypotheses.nonEmpty)
          Left(NotOfForm("respectfulness with nothing assumed", respects.conclusion))
        else if (respects.conclusion == wanted) Right(())
        else Left(NotOfForm("respectfulness of a unary operation", respects.conclusion))
    } yield ()

  /**
   * A binary operation lifted, `|- !x y. g (proj x) (proj y) = proj (f x y)`.
   *
   * The unary derivation with two representatives instead of one, and respectfulness taken curried
   * so that the two relations detach with two `Rules.mp` rather than through a conjunction that
   * would have to be built and taken apart again.
   */
  private def liftBinary(
    quotient: Quotient,
    name: String,
    operation: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] = {
    val carrier = quotient.carrier
    val classes = quotient.classes
    val taken = Term.freeVariables(quotient.relation)
    val x = Conv.freshVariable("x", carrier, taken)
    val y = Conv.freshVariable("y", carrier, taken + x)
    val u = Conv.freshVariable("u", carrier, taken + x + y)
    val v = Conv.freshVariable("v", carrier, taken + x + y + u)
    val p = Conv.freshVariable("p", classes, taken)
    val r = Conv.freshVariable("r", classes, taken + p)

    for {
      _ <- checkBinary(quotient, operation, respects, x, y, u, v)

      representativeConstant <- LogicError.lift(
        quotient.theory.constant(quotient.names.representative, Type.fun(classes, carrier))
      )
      projection <- LogicError.lift(
        quotient.theory.constant(quotient.names.projection, Type.fun(carrier, classes))
      )

      chosenP <- LogicError.lift(Term.app(representativeConstant, p))
      chosenR <- LogicError.lift(Term.app(representativeConstant, r))
      applied <- applyTo(operation, List(chosenP, chosenR))
      projected <- LogicError.lift(Term.app(projection, applied))
      body <- LogicError.lift(Term.absAll(List(p, r), projected))

      defined <- LogicError.lift(Kernel.defineConstant(quotient.theory, name, body))
      (complete, definition) = defined
      wider <- quotient.classical.logic.over(complete)

      related <- quotient.fact(RelatedToRepresentative)
      equal <- quotient.fact(ProjectionEqual)

      projectedX <- LogicError.lift(Term.app(projection, x))
      projectedY <- LogicError.lift(Term.app(projection, y))

      relatedAtX <- wider.rules.spec(x, related)
      relatedAtY <- wider.rules.spec(y, related)
      chosenAtX <- secondArgument(relatedAtX)
      chosenAtY <- secondArgument(relatedAtY)

      respectsAt <- wider.rules.specAll(respects, List(x, y, chosenAtX, chosenAtY))
      once <- wider.rules.mp(respectsAt, relatedAtX)
      carriedRelation <- wider.rules.mp(once, relatedAtY)

      appliedOriginal <- applyTo(operation, List(x, y))
      appliedChosen <- applyTo(operation, List(chosenAtX, chosenAtY))
      equalAt <- wider.rules.specAll(equal, List(appliedOriginal, appliedChosen))
      back <- Conv.sym(equalAt)
      classesEqual <- LogicError.lift(Kernel.eqMp(back, carriedRelation))

      unfolded <- Conv.unfold(definition, List(projectedX, projectedY))
      normalised <- reduced(unfolded)
      backwards <- Conv.sym(classesEqual)
      result <- Conv.trans(normalised, backwards)
      generalised <- wider.rules.genAll(result, List(x, y))

      extended = extend(quotient, complete, wider, name, definition)
    } yield (extended, generalised)
  }

  /** `|- !x y u v. R x u ==> R y v ==> R (f x y) (f u v)`, checked rather than trusted. */
  private def checkBinary(
    quotient: Quotient,
    operation: Term,
    respects: Kernel.Thm,
    x: FVar,
    y: FVar,
    u: FVar,
    v: FVar
  ): Either[LogicError, Unit] =
    for {
      appliedLeft <- applyTo(operation, List(x, y))
      appliedRight <- applyTo(operation, List(u, v))
      firstRelated <- quotient.related(x, u)
      secondRelated <- quotient.related(y, v)
      resultsRelated <- quotient.related(appliedLeft, appliedRight)
      tail <- quotient.logic.mkImp(secondRelated, resultsRelated)
      body <- quotient.logic.mkImp(firstRelated, tail)
      wanted <- foldForall(quotient.logic, List(x, y, u, v), body)
      _ <-
        if (respects.hypotheses.nonEmpty)
          Left(NotOfForm("respectfulness with nothing assumed", respects.conclusion))
        else if (respects.conclusion == wanted) Right(())
        else Left(NotOfForm("respectfulness of a binary operation, curried", respects.conclusion))
    } yield ()

  /**
   * A predicate lifted, `|- !x. g (proj x) = p x`.
   *
   * The simplest of the three, because the result is already a proposition and no projection has to
   * be undone: `g (proj x)` unfolds to `p (repr (proj x))`, and respectfulness at `x` and that
   * representative is an equation at `bool` which is the answer.
   *
   * Respectfulness is asked for as an **equation** and not as an implication. A predicate holding of
   * one representative and failing at another does not lift at all, and the implication in one
   * direction would let exactly that through: `g` would be well defined as a term and the fact
   * would be unprovable, which is a worse failure than a refusal here because it surfaces one
   * derivation later with nothing naming the cause.
   */
  private def liftPredicate(
    quotient: Quotient,
    name: String,
    predicate: Term,
    respects: Kernel.Thm
  ): Either[LogicError, (Quotient, Kernel.Thm)] = {
    val carrier = quotient.carrier
    val classes = quotient.classes
    val taken = Term.freeVariables(quotient.relation)
    val x = Conv.freshVariable("x", carrier, taken)
    val y = Conv.freshVariable("y", carrier, taken + x)
    val q = Conv.freshVariable("q", classes, taken)

    for {
      _ <- checkPredicate(quotient, predicate, respects, x, y)

      representativeConstant <- LogicError.lift(
        quotient.theory.constant(quotient.names.representative, Type.fun(classes, carrier))
      )
      projection <- LogicError.lift(
        quotient.theory.constant(quotient.names.projection, Type.fun(carrier, classes))
      )

      chosen <- LogicError.lift(Term.app(representativeConstant, q))
      applied <- applyTo(predicate, List(chosen))
      body <- LogicError.lift(Term.abs(q, applied))

      defined <- LogicError.lift(Kernel.defineConstant(quotient.theory, name, body))
      (complete, definition) = defined
      wider <- quotient.classical.logic.over(complete)

      related <- quotient.fact(RelatedToRepresentative)

      projectedX <- LogicError.lift(Term.app(projection, x))
      relatedAtX <- wider.rules.spec(x, related)
      chosenAtX <- secondArgument(relatedAtX)

      respectsAt <- wider.rules.specAll(respects, List(x, chosenAtX))
      // `|- p x = p (repr (proj x))`, at `bool`.
      agreement <- wider.rules.mp(respectsAt, relatedAtX)

      unfolded <- Conv.unfold(definition, List(projectedX))
      normalised <- reduced(unfolded)
      back <- Conv.sym(agreement)
      result <- Conv.trans(normalised, back)
      generalised <- wider.rules.gen(x, result)

      extended = extend(quotient, complete, wider, name, definition)
    } yield (extended, generalised)
  }

  /** `|- !x y. R x y ==> (p x = p y)`, checked rather than trusted. */
  private def checkPredicate(
    quotient: Quotient,
    predicate: Term,
    respects: Kernel.Thm,
    x: FVar,
    y: FVar
  ): Either[LogicError, Unit] =
    for {
      atX <- applyTo(predicate, List(x))
      atY <- applyTo(predicate, List(y))
      agreement <- LogicError.lift(Term.eq(atX, atY))
      relatedArguments <- quotient.related(x, y)
      body <- quotient.logic.mkImp(relatedArguments, agreement)
      wanted <- foldForall(quotient.logic, List(x, y), body)
      _ <-
        if (respects.hypotheses.nonEmpty)
          Left(NotOfForm("respectfulness with nothing assumed", respects.conclusion))
        else if (respects.conclusion == wanted) Right(())
        else Left(NotOfForm("respectfulness of a predicate, as an equation", respects.conclusion))
    } yield ()

  /* ------------------------------------------------------------------ internals */

  /**
   * The quotient again over a theory that has gained one constant.
   *
   * A lift extends the signature, so everything the value holds that reads against a theory has to
   * be rebuilt against the new one. The facts do not move: a theorem of a theory is a theorem of
   * every extension of it, which is what makes this a copy rather than a re-derivation.
   */
  private def extend(
    quotient: Quotient,
    theory: Theory,
    logic: Logic,
    name: String,
    definition: Kernel.Thm
  ): Quotient =
    new Quotient(
      quotient.classical,
      theory,
      quotient.notation,
      logic,
      quotient.relation,
      quotient.carrier,
      quotient.classes,
      quotient.names,
      quotient.definitions.updated(name, definition),
      quotient.facts
    )

  /**
   * The variable side of `|- abs (rep a) = a`, which is where the abstract type is read from.
   *
   * `Kernel.defineType` picks the name and the type of that variable, so this is the one place the
   * builder learns what type it just defined. Refused rather than assumed: a right side that is not
   * a variable means the kernel returned something other than the theorem documented, and a builder
   * that carried on would instantiate at the wrong thing several steps later.
   */
  private def variableSideOf(theorem: Kernel.Thm): Either[LogicError, FVar] =
    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .collect { case variable: FVar => variable }
      .toRight(NotOfForm("the abstraction of a representation, at a variable", theorem.conclusion))

  /** The second argument of `R a b`, which at [[RelatedToRepresentative]] is the chosen member. */
  private def secondArgument(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(App(_, _), second) => Right(second)
      case other => Left(NotOfForm("a relation applied to two arguments", other))
    }

  private def foldForall(
    logic: Logic,
    variables: List[FVar],
    body: Term
  ): Either[LogicError, Term] =
    variables.foldRight[Either[LogicError, Term]](Right(body)) { (variable, acc) =>
      acc.flatMap(logic.mkForall(variable, _))
    }

  /**
   * A theorem with its conclusion in beta normal form, whatever shape that conclusion has.
   *
   * `Conv.normaliseSides` wants an equation and `Classical.witnessFrom` hands back an application,
   * so one of the two uses here would need the other helper and the difference is not one a reader
   * of the call site should have to hold. `Conv.betaNormalise` is total on a well-typed term, so
   * this reduces where there is anything to reduce and is the identity where there is not.
   *
   * **Everything this builder constructs is in normal form and that is a decision.** An operation a
   * caller supplies may be a lambda, and then `f x` written by hand is a redex while the same thing
   * inside the caller's own respectfulness theorem is usually reduced. Normalising both sides of
   * that comparison is what keeps [[checkUnary]] from refusing a correct theorem over a spelling.
   */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.betaNormalise(theorem.conclusion)
      result <- LogicError.lift(Kernel.eqMp(equation, theorem))
    } yield result

  /** The same for a term being built rather than a theorem being reduced. */
  private def applyTo(fn: Term, arguments: List[Term]): Either[LogicError, Term] =
    for {
      applied <- LogicError.lift(Term.appAll(fn, arguments))
      equation <- Conv.betaNormalise(applied)
      result <- rightOf(equation)
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

}
