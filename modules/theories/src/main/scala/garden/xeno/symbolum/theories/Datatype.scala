package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * An inductive type from a list of constructors, with its induction principle, the injectivity
 * and distinctness of its constructors, its case analysis and its recursion theorem, all derived.
 *
 * Until this landed no syntax could be a **type** here. Every development spoke of objects —
 * numbers, pairs, words, integers — and the one way to speak of expressions was the arithmetic
 * coding `Language` walks, which pays for each function over a code with a proof of admissibility
 * that a type with constructors gives for nothing. Four types had been carved by hand with
 * `Kernel.defineType`, each with its own universe and its own proofs; this is the fifth site, and it
 * is the first that carves a type **from a description** rather than one written out. `Quotient` is
 * the precedent for the shape: a Scala function, not a constant of the object logic, so it adds no
 * link to the chain and moves neither `docs/lemmas.md` nor the reading register when it lands.
 * `docs/adr/0042` is the decision and the alternatives it rejects.
 *
 * == The construction, which is HOL Light's and costs no axiom ==
 *
 * A value of every such type is represented by a **labelled tree**, and one type holds all of them:
 *
 * {{{
 *   word(num) -> L -> bool
 * }}}
 *
 * the set of pairs (path, label), where a path is the list of child indices walked from the root.
 * `NODE l c` is the tree with `l` at the root and the tree `c i` under child `i`:
 *
 * {{{
 *   NODE = \l c p x. (p = WORD_EMPTY /\ x = l) \/ (?i q. p = LIST_CONS i q /\ c i q x)
 * }}}
 *
 * and the one fact everything rests on is that `NODE` is injective, which is `LIST_CONS_NOT_EMPTY`,
 * `LIST_CONS_INJECTIVE` and extensionality and nothing else. The label of constructor `k` is the
 * pair of the numeral `k` with a tuple holding its non-recursive arguments, the slots of the other
 * constructors filled with `select (\z. T)`, so two labels of different constructors differ in
 * their first component and two of the same constructor differ exactly where the arguments do. The
 * children of a node are `\i. COND (i = 0) r0 (COND (i = 1) r1 (...))`, with the empty tree past
 * the last recursive argument.
 *
 * The type is then `Kernel.defineType` over `INDUCTIVE F`, where `F` says a tree is one of the
 * constructors' nodes over trees of the set: the least such set is what the constructors reach, and
 * `Monotone.prove` discharges what `INDUCTIVE_INTRO` asks. Nothing in any of that is asserted, so
 * every fact of a type defined here costs choice, eta and infinity, which the chain already holds,
 * and the builder refuses rather than proceeding when no constructor is free of recursive
 * arguments, since then there is no first value to witness the type with.
 *
 * `NODE` is a **term**, not a constant: nothing is declared for the universe, so two types built
 * over one theory do not meet on a name, and the cost is that no derivation below may normalise a
 * term with a `NODE` inside it. Every reduction here is at the root, which is what `Conv.unfold`,
 * `Rules.spec` and `Rules.existsIntro` do, and `betaNormalise` is used on nothing that holds a node.
 *
 * == The recursion theorem, which is the half that makes the type usable ==
 *
 * {{{
 *   !f0 ... fk. ?h. !args. h (C0 args) = f0 args (h y1) ... (h yn) /\ ...
 * }}}
 *
 * where each `fj` is handed every argument of its constructor and then the value of `h` at each
 * recursive one. It is proved through the **graph**: the least set of pairs `(t, v)` closed under
 * the equations, which induction on the type shows to be the graph of a function, using the
 * injectivity and the distinctness of the constructors for uniqueness. `h` is then the choice of
 * the value at each `t`. A definition by structural recursion is [[Datatype.defineRecursive]], which
 * names the function this theorem asserts and hands back its equations.
 *
 * == What it does not do ==
 *
 * **One type at a time**, recursive only through arguments of the type itself: no mutual
 * recursion, no recursion under a type operator (`word(t)`, `num -> t`). Those are what HOL Light's
 * nested and mutual machinery is for, and nothing here has asked for them yet. And it proves no
 * uniqueness of the recursive function: the existential is what a definition needs, and two
 * functions satisfying the same equations are equal by induction when a caller wants it.
 */
final class Datatype private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val specification: Datatype.Specification,
  val carrier: Type,
  val constructors: Vector[Term],
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`, a constructor or the abstraction pair. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this type, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** The constructor named `name`, as a constant of [[theory]]. */
  def constructor(name: String): Either[LogicError, Term] =
    specification.constructors.indexWhere(_.name == name) match {
      case -1 => Left(MissingDefinition(name))
      case index => Right(constructors(index))
    }
}

object Datatype {

  /** An argument of a constructor: a value of a type fixed in advance, or one of the type itself. */
  enum Argument {
    case Of(ty: Type)
    case Recursive
  }

  /** One constructor, its name and its arguments in the order it takes them. */
  final case class Constructor(name: String, arguments: List[Argument])

  /** The type to define and its constructors, in order. */
  final case class Specification(typeName: String, constructors: List[Constructor]) {
    val abstraction: String = s"mk_$typeName"
    val representation: String = s"dest_$typeName"
  }

  /** `|- !P. (<one clause per constructor>) ==> !t. P t`. */
  def induction(typeName: String): String = s"${typeName.toUpperCase}_INDUCT"

  /** `|- !t. (?args. t = C0 args) \/ ...`. */
  def cases(typeName: String): String = s"${typeName.toUpperCase}_CASES"

  /** `|- !f0 ... fk. ?h. <one equation per constructor>`. */
  def recursion(typeName: String): String = s"${typeName.toUpperCase}_RECURSION"

  /** `|- !args args'. C args = C args' ==> <argument by argument>`. */
  def injective(constructor: String): String = s"${constructor}_INJECTIVE"

  /** `|- !args args'. ~(C args = D args')`. */
  def distinct(left: String, right: String): String = s"${left}_NOT_${right}"

  /** What the chain supplies to every type built here. */
  final case class Ground(
    classical: Classical,
    product: Product,
    listing: Listing,
    inductive: Inductive,
    successor: Successor
  )

  object Ground {

    /** The pieces as the chain holds them. */
    def of(chain: Chain): Ground =
      Ground(chain.classical, chain.product, chain.listing, chain.inductive, chain.successor)
  }

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Paths: Type = TyApp(Word.TypeName, List(Num))
  private val Point: String = Classical.TypeVariable

  /**
   * The type, over `base`, which must hold the words, the lists, the pairs, `INDUCTIVE` and `COND`:
   * the chain's widest signature does, and so does any theory extending it.
   */
  def define(
    ground: Ground,
    base: Theory,
    notation: Notation,
    specification: Specification
  ): Either[LogicError, Datatype] =
    for {
      _ <- validate(specification)
      narrow <- ground.classical.logic.over(base)
      tools = Tools(ground, narrow, base, notation)
      universe <- Universe.of(tools, specification)
      nodes <- NodeFacts.of(tools, universe)
      shapes <- Shapes.of(tools, universe)

      representing <- Representing.of(tools, universe, nodes, shapes)
      typed <- LogicError.lift(
        Kernel.defineType(
          base,
          specification.typeName,
          specification.abstraction,
          specification.representation,
          representing.witness
        )
      )
      (withType, bijection) = typed
      (absRep, repAbs) = bijection

      carrier <- Term
        .destEq(absRep.conclusion)
        .map(sides => Term.typeOf(sides._2))
        .toRight(NotOfForm("an equation", absRep.conclusion))

      declared <- declareConstructors(ground, withType, notation, specification, universe, carrier)
      (complete, constructors, constructorDefinitions) = declared

      wide <- ground.classical.logic.over(complete)
      finalTools = Tools(ground, wide, complete, notation)
      abstraction <- LogicError.lift(complete.constant(specification.abstraction, Type.fun(universe.tree, carrier)))
      representation <- LogicError.lift(complete.constant(specification.representation, Type.fun(carrier, universe.tree)))

      carried = Carried(
        finalTools,
        universe,
        nodes,
        shapes,
        representing,
        carrier,
        abstraction,
        representation,
        absRep,
        repAbs,
        constructors,
        constructorDefinitions
      )

      member <- carried.everyRepresentationIsMember
      destOf <- carried.representationsOfConstructors(member)
      injectivity <- carried.injectivityFacts(destOf)
      distinctness <- carried.distinctnessFacts(destOf)
      inducted <- carried.inductionPrinciple(member)
      split <- carried.caseAnalysis(inducted)
      recursive <- carried.recursionTheorem(inducted, injectivity, distinctness)

      facts =
        injectivity.map { case (name, theorem) => injective(name) -> theorem } ++
          distinctness.map { case ((left, right), theorem) => distinct(left, right) -> theorem } ++
          Map(
            induction(specification.typeName) -> inducted,
            cases(specification.typeName) -> split,
            recursion(specification.typeName) -> recursive
          )
    } yield new Datatype(
      complete,
      notation,
      wide,
      specification,
      carrier,
      constructors,
      constructorDefinitions ++ Map(
        specification.abstraction -> absRep,
        specification.representation -> repAbs
      ),
      facts
    )

  /**
   * Refused before anything is built: an empty list of constructors, two constructors of one name,
   * and no constructor free of recursive arguments, which leaves the type without a first value.
   */
  private def validate(specification: Specification): Either[LogicError, Unit] = {
    val names = specification.constructors.map(_.name)
    if (specification.constructors.isEmpty)
      Left(NotOfForm("a type with at least one constructor", Term.variable(specification.typeName, Type.Bool)))
    else if (names.distinct.length != names.length)
      Left(NotOfForm("constructors with distinct names", Term.variable(names.mkString(" "), Type.Bool)))
    else if (!specification.constructors.exists(_.arguments.forall(_ != Argument.Recursive)))
      Left(
        NotOfForm(
          "a constructor with no recursive argument, which is what inhabits the type",
          Term.variable(specification.typeName, Type.Bool)
        )
      )
    else Right(())
  }

  /* ================================================================== the moves */

  /** One theory and the few moves every derivation below makes over it. */
  private[theories] final case class Tools(ground: Ground, logic: Logic, theory: Theory, notation: Notation) {
    val rules: Rules = logic.rules
    val intuitionistic: Intuitionistic = Intuitionistic(logic)

    def assume(statement: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(statement))

    /** A propositional step with the subterms as atoms, which costs no axiom. */
    def glue(statement: Either[LogicError, Term]): Either[LogicError, Kernel.Thm] =
      statement.flatMap(intuitionistic.prove)

    def imp(left: Term, right: Term): Either[LogicError, Term] = logic.mkImp(left, right)
    def conj(left: Term, right: Term): Either[LogicError, Term] = logic.mkConj(left, right)
    def disj(left: Term, right: Term): Either[LogicError, Term] = logic.mkDisj(left, right)
    def not(statement: Term): Either[LogicError, Term] = logic.mkNot(statement)
    def equal(left: Term, right: Term): Either[LogicError, Term] = LogicError.lift(Term.eq(left, right))
    def app(fn: Term, arguments: Term*): Either[LogicError, Term] = LogicError.lift(Term.appAll(fn, arguments.toList))

    /** `a1 /\ (a2 /\ ...)`, and `T` for none. */
    def conjoin(parts: List[Term]): Either[LogicError, Term] = parts match {
      case Nil => Right(logic.truth)
      case single :: Nil => Right(single)
      case first :: rest => conjoin(rest).flatMap(conj(first, _))
    }

    /** `a1 \/ (a2 \/ ...)`. */
    def disjoin(parts: List[Term]): Either[LogicError, Term] = parts match {
      case Nil => Right(logic.falsity)
      case single :: Nil => Right(single)
      case first :: rest => disjoin(rest).flatMap(disj(first, _))
    }

    /** `?v1 ... vn. body`. */
    def exists(variables: List[FVar], body: Term): Either[LogicError, Term] =
      variables.foldRight[Either[LogicError, Term]](Right(body))((variable, acc) =>
        acc.flatMap(logic.mkExists(variable, _)))

    /** `!v1 ... vn. body`. */
    def forall(variables: List[FVar], body: Term): Either[LogicError, Term] =
      variables.foldRight[Either[LogicError, Term]](Right(body))((variable, acc) =>
        acc.flatMap(logic.mkForall(variable, _)))

    /** Theorems of a conjunction built by [[conjoin]], one per part. */
    def conjuncts(theorem: Kernel.Thm, count: Int): Either[LogicError, List[Kernel.Thm]] =
      if (count <= 1) Right(List(theorem))
      else
        for {
          first <- rules.conjElim1(theorem)
          rest <- rules.conjElim2(theorem)
          tail <- conjuncts(rest, count - 1)
        } yield first :: tail

    /** A proof of a conjunction built by [[conjoin]] from one proof per part. */
    def conjoined(parts: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] = parts match {
      case Nil => rules.eqTruthElim(Conv.refl(logic.truth))
      case single :: Nil => Right(single)
      case first :: rest => conjoined(rest).flatMap(rules.conjIntro(first, _))
    }

    /**
     * A proof of `?v1 ... vn. body` from a proof of `body` at the witnesses, read off the
     * existential rather than rebuilt, so the predicate at each level is the one the target holds.
     */
    def witnessed(target: Term, witnesses: List[Term], proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      witnesses match {
        case Nil =>
          if (target == proof.conclusion) Right(proof)
          else Left(NotOfForm("a proof of the body the existential opens to", proof.conclusion))
        case first :: rest =>
          for {
            predicate <- logic.destExistsPredicate(target).toRight(NotOfForm("an existential", target))
            applied <- app(predicate, first)
            reduced <- Conv.betaRoot(applied)
            inner <- rightOf(reduced)
            proved <- witnessed(inner, rest, proof)
            result <- rules.existsIntro(predicate, first, proved)
          } yield result
      }

    /**
     * `P1 \/ P2 \/ ...` from a proof of the part at `index`, the disjunction built by [[disjoin]].
     */
    def injected(parts: List[Term], index: Int, proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      parts match {
        case Nil => Left(NotOfForm("a disjunct", logic.falsity))
        case _ :: Nil => Right(proof)
        case first :: rest =>
          if (index == 0) disjoin(rest).flatMap(rules.disjIntro1(_, proof))
          else injected(rest, index - 1, proof).flatMap(rules.disjIntro2(first, _))
      }

    /**
     * From `disjunction` (built by [[disjoin]] over `parts`) and one theorem per part that holds
     * under that part as a hypothesis, the common conclusion.
     */
    def byCases(disjunction: Kernel.Thm, parts: List[Term], cases: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      (parts, cases) match {
        case (_ :: Nil, single :: Nil) =>
          for {
            dischargedCase <- rules.disch(parts.head, single)
            result <- rules.mp(dischargedCase, disjunction)
          } yield result
        case (first :: restParts, firstCase :: restCases) =>
          for {
            restDisjunction <- disjoin(restParts)
            assumedRest <- assume(restDisjunction)
            restProof <- byCases(assumedRest, restParts, restCases)
            result <- rules.disjElim(disjunction, firstCase, restProof)
          } yield result
        case _ => Left(NotOfForm("one case per disjunct", disjunction.conclusion))
      }

    /** Eliminates `?v1 ... vn. body` into a theorem holding under `body`, with `variables` fresh. */
    def opened(existential: Kernel.Thm, variables: List[FVar], proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      variables match {
        case Nil => Right(proof)
        case first :: rest =>
          for {
            predicate <- logic
              .destExistsPredicate(existential.conclusion)
              .toRight(NotOfForm("an existential", existential.conclusion))
            applied <- app(predicate, first)
            reduced <- Conv.betaRoot(applied)
            inner <- rightOf(reduced)
            assumedInner <- assume(inner)
            innerProof <- opened(assumedInner, rest, proof)
            result <- rules.existsElim(existential, first, innerProof)
          } yield result
      }

    /** `|- (\v1 ... vn. body) a1 ... an = body[a]`, by root contractions only. */
    def applied(lambda: Term, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
      Conv.unfold(Conv.refl(lambda), arguments)

    /**
     * `|- template[l1 ... ln] = template[r1 ... rn]` from `|- li = ri`, by congruence under
     * `\z1 ... zn. template` and root contractions, so nothing inside the template is reduced.
     */
    def congruence(holes: List[FVar], template: Term, equations: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        lambda <- LogicError.lift(Term.absAll(holes, template))
        combined <- equations.foldLeft[Either[LogicError, Kernel.Thm]](Right(Conv.refl(lambda))) { (acc, equation) =>
          acc.flatMap(current => LogicError.lift(Kernel.mkComb(current, equation)))
        }
        sides <- Term.destEq(combined.conclusion).toRight(NotOfForm("an equation", combined.conclusion))
        lefts <- equations.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, equation) =>
          acc.flatMap(list => leftOf(equation).map(list :+ _)))
        rights <- equations.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, equation) =>
          acc.flatMap(list => rightOf(equation).map(list :+ _)))
        leftReduced <- applied(lambda, lefts)
        rightReduced <- applied(lambda, rights)
        flipped <- Conv.sym(leftReduced)
        joined <- Conv.trans(flipped, combined)
        result <- Conv.trans(joined, rightReduced)
      } yield result

    /** Instantiates the named type variables of a polymorphic theorem. */
    def at(theorem: Kernel.Thm, types: (String, Type)*): Kernel.Thm = Kernel.instType(types.toMap, theorem)

    def numeral(value: Int): Either[LogicError, Term] = Parser.term(theory, notation, value.toString, Num)

    def constant(name: String, ty: Type): Either[LogicError, Term] = LogicError.lift(theory.constant(name, ty))

    /**
     * `select`, `COND` and a chosen witness read against **this** theory. `Classical`'s own methods
     * read against the theory `Classical` was built over, which has never heard of `num`, and a
     * constant at a type its theory does not hold is refused there rather than here.
     */
    def select(ty: Type): Either[LogicError, Term] =
      constant(Classical.Select, Type.fun(Type.fun(ty, Type.Bool), ty))

    def conditional(ty: Type): Either[LogicError, Term] =
      constant(Classical.Conditional, Type.fun(Type.Bool, Type.fun(ty, Type.fun(ty, ty))))

    def witness(existential: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      ground.classical.axiom(Classical.Choice).flatMap(Classical.witnessFrom(logic, _, existential))

    /** `PAIR a b = PAIR c d` gives `a = c` and `b = d`, by `PAIR_INJECTIVE` at the pair's types. */
    def pairParts(equation: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
      Term.destEq(equation.conclusion) match {
        case Some((App(App(Const(Product.Pairing, _), a), b), App(App(Const(Product.Pairing, _), c), d))) =>
          for {
            injective <- ground.product.fact(Product.PairInjective)
            typed = at(injective, Point -> Term.typeOf(a), Classical.CodomainVariable -> Term.typeOf(b))
            instance <- rules.specAll(typed, List(a, b, c, d))
            split <- LogicError.lift(Kernel.eqMp(instance, equation))
            first <- rules.conjElim1(split)
            second <- rules.conjElim2(split)
          } yield (first, second)
        case _ => Left(NotOfForm("an equation between two pairs", equation.conclusion))
      }
  }

  private[theories] def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  private[theories] def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /* ================================================================ the universe */

  /**
   * The label type, the tree type, and the three terms the representation is written with: the
   * node, the empty tree, and the label of each constructor.
   */
  private final case class Universe(
    specification: Specification,
    slots: Vector[Type],
    slotOwner: Vector[(Int, Int)],
    label: Type,
    tree: Type,
    node: Term,
    empty: Term,
    arbitrary: Vector[Term]
  ) {

    /** The fixed arguments of constructor `k`, as positions in its own argument list. */
    def fixedPositions(k: Int): List[Int] =
      specification.constructors(k).arguments.zipWithIndex.collect { case (Argument.Of(_), index) => index }

    /** The recursive arguments of constructor `k`, as positions in its own argument list. */
    def recursivePositions(k: Int): List[Int] =
      specification.constructors(k).arguments.zipWithIndex.collect { case (Argument.Recursive, index) => index }
  }

  private object Universe {

    def of(tools: Tools, specification: Specification): Either[LogicError, Universe] = {
      import tools.*
      val owned = specification.constructors.zipWithIndex.flatMap { case (constructor, k) =>
        constructor.arguments.zipWithIndex.collect { case (Argument.Of(ty), position) => (ty, (k, position)) }
      }
      val slots = owned.map(_._1).toVector
      val payload = slots.foldRight(Type.Bool)((slot, rest) => TyApp(Product.TypeName, List(slot, rest)))
      val label = TyApp(Product.TypeName, List(Num, payload))
      val tree = Type.fun(Paths, Type.fun(label, Type.Bool))

      val l = Term.variable("l", label)
      val c = Term.variable("c", Type.fun(Num, tree))
      val p = Term.variable("p", Paths)
      val x = Term.variable("x", label)
      val i = Term.variable("i", Num)
      val q = Term.variable("q", Paths)

      for {
        emptyWord <- constant(Concatenation.Empty, Paths)
        cons <- constant(Listing.Cons, Type.fun(Num, Type.fun(Paths, Paths)))
        atRoot <- equal(p, emptyWord).flatMap(left => equal(x, l).flatMap(conj(left, _)))
        consed <- app(cons, i, q)
        below <- equal(p, consed).flatMap(left => app(c, i, q, x).flatMap(conj(left, _)))
        descended <- exists(List(i, q), below)
        body <- disj(atRoot, descended)
        node <- LogicError.lift(Term.absAll(List(l, c, p, x), body))
        empty <- LogicError.lift(Term.absAll(List(p, x), logic.falsity))
        arbitrary <- slots.foldLeft[Either[LogicError, Vector[Term]]](Right(Vector.empty)) { (acc, slot) =>
          for {
            list <- acc
            choice <- tools.select(slot)
            anything = Term.variable("z", slot)
            predicate <- LogicError.lift(Term.abs(anything, logic.truth))
            chosen <- app(choice, predicate)
          } yield list :+ chosen
        }
      } yield Universe(specification, slots, owned.map(_._2).toVector, label, tree, node, empty, arbitrary)
    }
  }

  /* ================================================================ the node facts */

  /** The three facts about `NODE`, at the label type of this universe. */
  private final case class NodeFacts(atEmpty: Kernel.Thm, atCons: Kernel.Thm, injective: Kernel.Thm)

  private object NodeFacts {

    /**
     * `|- NODE l c WORD_EMPTY x = (x = l)`, `|- NODE l c (LIST_CONS j r) x = c j r x` and
     * `|- NODE l c = NODE l' c' ==> l = l' /\ c = c'`, over free `l`, `c`, `x`, `j`, `r`.
     */
    def of(tools: Tools, universe: Universe): Either[LogicError, NodeFacts] = {
      import tools.*
      val l = Term.variable("l", universe.label)
      val l2 = Term.variable("l'", universe.label)
      val c = Term.variable("c", Type.fun(Num, universe.tree))
      val c2 = Term.variable("c'", Type.fun(Num, universe.tree))
      val x = Term.variable("x", universe.label)
      val j = Term.variable("j", Num)
      val r = Term.variable("r", Paths)
      val i = Term.variable("i", Num)
      val q = Term.variable("q", Paths)

      for {
        listed <- List(Listing.ConsNotEmpty, Listing.ConsInjective)
          .foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((acc, name) =>
            acc.flatMap(list => tools.ground.listing.fact(name).map(fact => list :+ at(fact, Point -> Num))))
        notEmpty = listed(0)
        consInjective = listed(1)
        emptyWord <- constant(Concatenation.Empty, Paths)
        cons <- constant(Listing.Cons, Type.fun(Num, Type.fun(Paths, Paths)))

        /* ------------------------------------------------------------ at the root */

        rootOpened <- applied(universe.node, List(l, c, emptyWord, x))
        rootBody <- rightOf(rootOpened)
        rootParts <- logic.destDisj(rootBody).toRight(NotOfForm("a disjunction", rootBody))
        (rootHere, rootBelow) = rootParts
        rootReflexive <- logic.destConj(rootHere).map(_._1).toRight(NotOfForm("a conjunction", rootHere))
        rootPoint <- equal(x, l)
        noneBelow <- {
          val atI = rootBelow
          for {
            assumedBelow <- assume(atI)
            innerStatement <- logic
              .destExistsPredicate(atI)
              .toRight(NotOfForm("an existential", atI))
              .flatMap(predicate => app(predicate, i))
              .flatMap(Conv.betaRoot)
              .flatMap(rightOf)
            bodyStatement <- logic
              .destExistsPredicate(innerStatement)
              .toRight(NotOfForm("an existential", innerStatement))
              .flatMap(predicate => app(predicate, q))
              .flatMap(Conv.betaRoot)
              .flatMap(rightOf)
            assumedBody <- assume(bodyStatement)
            equation <- rules.conjElim1(assumedBody)
            flipped <- Conv.sym(equation)
            refused <- rules.specAll(notEmpty, List(i, q))
            absurd <- rules.notElim(refused, flipped)
            innerOpened <- assume(innerStatement).flatMap(rules.existsElim(_, q, absurd))
            outerOpened <- rules.existsElim(assumedBelow, i, innerOpened)
            result <- rules.notIntro(atI, outerOpened)
          } yield result
        }
        rootForward <- glue(
          not(rootBelow).flatMap(nb => imp(rootBody, rootPoint).flatMap(imp(nb, _))).flatMap(imp(rootReflexive, _))
        )
        rootBackward <- glue(imp(rootPoint, rootBody).flatMap(imp(rootReflexive, _)))
        reflexive = Conv.refl(emptyWord)
        forward <- rules
          .mp(rootForward, reflexive)
          .flatMap(rules.mp(_, noneBelow))
          .flatMap(step => assume(rootBody).flatMap(rules.mp(step, _)))
        backward <- rules.mp(rootBackward, reflexive).flatMap(step => assume(rootPoint).flatMap(rules.mp(step, _)))
        atEmpty <- Conv.trans(rootOpened, Kernel.deductAntisym(backward, forward))

        /* ------------------------------------------------------------ below the root */

        consed <- app(cons, j, r)
        belowOpened <- applied(universe.node, List(l, c, consed, x))
        belowBody <- rightOf(belowOpened)
        belowParts <- logic.destDisj(belowBody).toRight(NotOfForm("a disjunction", belowBody))
        (belowHere, belowThere) = belowParts
        belowWrong <- logic.destConj(belowHere).map(_._1).toRight(NotOfForm("a conjunction", belowHere))
        child <- app(c, j, r, x)
        notHere <- rules.specAll(notEmpty, List(j, r))

        // the existential says exactly `c j r x`
        thereForward <- {
          for {
            assumedThere <- assume(belowThere)
            innerStatement <- logic
              .destExistsPredicate(belowThere)
              .toRight(NotOfForm("an existential", belowThere))
              .flatMap(predicate => app(predicate, i))
              .flatMap(Conv.betaRoot)
              .flatMap(rightOf)
            bodyStatement <- logic
              .destExistsPredicate(innerStatement)
              .toRight(NotOfForm("an existential", innerStatement))
              .flatMap(predicate => app(predicate, q))
              .flatMap(Conv.betaRoot)
              .flatMap(rightOf)
            assumedBody <- assume(bodyStatement)
            equation <- rules.conjElim1(assumedBody)
            atIQ <- rules.conjElim2(assumedBody)
            split <- rules.specAll(consInjective, List(j, r, i, q)).flatMap(rules.mp(_, equation))
            sameIndex <- rules.conjElim1(split)
            samePath <- rules.conjElim2(split)
            // `c j r x = c i q x`, from `j = i` and `r = q`, by congruence over two holes
            holeIndex = Term.variable("hole_i", Num)
            holePath = Term.variable("hole_q", Paths)
            template <- app(c, holeIndex, holePath, x)
            moved <- congruence(List(holeIndex, holePath), template, List(sameIndex, samePath))
            back <- Conv.sym(moved)
            result0 <- LogicError.lift(Kernel.eqMp(back, atIQ))
            innerOpened <- assume(innerStatement).flatMap(rules.existsElim(_, q, result0))
            result <- rules.existsElim(assumedThere, i, innerOpened)
          } yield result
        }
        thereBackward <- {
          for {
            assumedChild <- assume(child)
            both <- rules.conjIntro(Conv.refl(consed), assumedChild)
            result <- witnessed(belowThere, List(j, r), both)
          } yield result
        }
        consForward <- glue(
          not(belowWrong).flatMap(nw => imp(belowThere, child).flatMap(bt =>
            imp(belowBody, child).flatMap(bb => imp(bt, bb)).flatMap(imp(nw, _))))
        )
        consBackward <- glue(imp(child, belowBody).flatMap(cbody => imp(child, belowThere).flatMap(cb => imp(cb, cbody))))
        dischargedThereForward <- rules.disch(belowThere, thereForward)
        dischargedThereBackward <- rules.disch(child, thereBackward)
        consLeft <- rules
          .mp(consForward, notHere)
          .flatMap(rules.mp(_, dischargedThereForward))
          .flatMap(step => assume(belowBody).flatMap(rules.mp(step, _)))
        consRight <- rules
          .mp(consBackward, dischargedThereBackward)
          .flatMap(step => assume(child).flatMap(rules.mp(step, _)))
        atCons <- Conv.trans(belowOpened, Kernel.deductAntisym(consRight, consLeft))

        /* ------------------------------------------------------------ injectivity */

        left <- app(universe.node, l, c)
        right <- app(universe.node, l2, c2)
        same <- equal(left, right)
        assumedSame <- assume(same)

        labels <- {
          for {
            atRoot <- Conv.apThm(assumedSame, emptyWord).flatMap(Conv.apThm(_, l))
            leftRoot <- LogicError.lift(Kernel.inst(Map(x -> l), atEmpty))
            rightRoot <- LogicError.lift(Kernel.inst(Map(x -> l, l -> l2, c -> c2), atEmpty))
            flippedLeft <- Conv.sym(leftRoot)
            joined <- Conv.trans(flippedLeft, atRoot).flatMap(Conv.trans(_, rightRoot))
            result <- LogicError.lift(Kernel.eqMp(joined, Conv.refl(l)))
          } yield result
        }

        children <- {
          for {
            consedIQ <- app(cons, i, q)
            atPath <- Conv.apThm(assumedSame, consedIQ).flatMap(Conv.apThm(_, x))
            leftChild <- LogicError.lift(Kernel.inst(Map(j -> i, r -> q), atCons))
            rightChild <- LogicError.lift(Kernel.inst(Map(j -> i, r -> q, l -> l2, c -> c2), atCons))
            flippedLeft <- Conv.sym(leftChild)
            pointwise <- Conv.trans(flippedLeft, atPath).flatMap(Conv.trans(_, rightChild))
            overX <- rules.gen(x, pointwise).flatMap(tools.ground.classical.ext(logic, _))
            overQ <- rules.gen(q, overX).flatMap(tools.ground.classical.ext(logic, _))
            overI <- rules.gen(i, overQ).flatMap(tools.ground.classical.ext(logic, _))
          } yield overI
        }

        both <- rules.conjIntro(labels, children)
        injective <- rules.disch(same, both)
      } yield NodeFacts(atEmpty, atCons, injective)
    }
  }

  /* ================================================================ labels and children */

  /**
   * The label and the children of a node, as functions of the arguments, and what they give back:
   * the label of a constructor determines its fixed arguments and the constructor itself, and the
   * children determine each recursive argument.
   */
  private final case class Shapes(tools: Tools, universe: Universe) {
    import tools.*

    private val pairInjective: Either[LogicError, Kernel.Thm] = tools.ground.product.fact(Product.PairInjective)

    /** `PAIR k (PAIR v0 (PAIR v1 (... T)))`, with the slots of other constructors chosen. */
    def label(k: Int, fixed: List[Term]): Either[LogicError, Term] = {
      val owned = universe.slotOwner.zipWithIndex.filter(_._1._1 == k).map(_._2)
      val values = universe.slots.indices.map { slot =>
        owned.indexOf(slot) match {
          case -1 => universe.arbitrary(slot)
          case position => fixed(position)
        }
      }.toList
      for {
        payload <- values.zip(universe.slots).foldRight[Either[LogicError, (Term, Type)]](Right((logic.truth, Type.Bool))) {
          case ((value, slot), acc) =>
            for {
              carried <- acc
              (rest, restType) = carried
              pair <- constant(Product.Pairing, Type.fun(slot, Type.fun(restType, TyApp(Product.TypeName, List(slot, restType)))))
              built <- app(pair, value, rest)
            } yield (built, TyApp(Product.TypeName, List(slot, restType)))
        }
        index <- numeral(k)
        (payloadTerm, payloadType) = payload
        pair <- constant(Product.Pairing, Type.fun(Num, Type.fun(payloadType, universe.label)))
        result <- app(pair, index, payloadTerm)
      } yield result
    }

    /** `\i. COND (i = 0) r0 (COND (i = 1) r1 (... EMPTY))`. */
    def children(recursive: List[Term]): Either[LogicError, Term] = {
      val i = Term.variable("i", Num)
      for {
        choose <- tools.conditional(universe.tree)
        body <- recursive.zipWithIndex.foldRight[Either[LogicError, Term]](Right(universe.empty)) {
          case ((child, index), acc) =>
            for {
              rest <- acc
              position <- numeral(index)
              test <- equal(i, position)
              built <- app(choose, test, child, rest)
            } yield built
        }
        result <- LogicError.lift(Term.abs(i, body))
      } yield result
    }

    /** `|- children [r0 ... rn] j = rj`. */
    def childAt(recursive: List[Term], index: Int): Either[LogicError, Kernel.Thm] =
      for {
        lambda <- children(recursive)
        position <- numeral(index)
        opened <- applied(lambda, List(position))
        condTrue <- tools.ground.classical.fact(Classical.CondTrue).map(at(_, Point -> universe.tree))
        condFalse <- tools.ground.classical.fact(Classical.CondFalse).map(at(_, Point -> universe.tree))
        result <- (0 to index).foldLeft[Either[LogicError, Kernel.Thm]](Right(opened)) { (acc, level) =>
          for {
            current <- acc
            conditional <- rightOf(current)
            parts <- conditional match {
              case App(App(App(_, test), yes), no) => Right((test, yes, no))
              case other => Left(NotOfForm("a conditional", other))
            }
            (test, yes, no) = parts
            step <-
              if (level == index)
                rules.specAll(condTrue, List(test, yes, no)).flatMap(rules.mp(_, Conv.refl(position)))
              else
                for {
                  levelNumeral <- numeral(level)
                  differ <- tools.ground.successor.distinct(position, levelNumeral)
                  result <- rules.specAll(condFalse, List(test, yes, no)).flatMap(rules.mp(_, differ))
                } yield result
            next <- Conv.trans(current, step)
          } yield next
        }
      } yield result

    /**
     * Under `label k xs = label k ys`, one equation `xi = yi` per fixed argument, in order.
     */
    def labelsAgree(k: Int, fixed: List[Term], others: List[Term]): Either[LogicError, (Term, List[Kernel.Thm])] =
      for {
        left <- label(k, fixed)
        right <- label(k, others)
        same <- equal(left, right)
        assumed <- assume(same)
        components <- peel(assumed)
        owned = universe.slotOwner.zipWithIndex.filter(_._1._1 == k).map(_._2).toList
        // components(0) is the index; component 1 + slot is that slot
        result = owned.map(slot => components(1 + slot))
      } yield (same, result)

    /** Under `label j xs = label k ys` with `j` and `k` different, falsity. */
    def labelsDiffer(j: Int, fixed: List[Term], k: Int, others: List[Term]): Either[LogicError, (Term, Kernel.Thm)] =
      for {
        left <- label(j, fixed)
        right <- label(k, others)
        same <- equal(left, right)
        assumed <- assume(same)
        components <- peel(assumed)
        leftIndex <- numeral(j)
        rightIndex <- numeral(k)
        differ <- tools.ground.successor.distinct(leftIndex, rightIndex)
        absurd <- rules.notElim(differ, components.head)
      } yield (same, absurd)

    /** `PAIR a0 (PAIR a1 ...) = PAIR b0 (PAIR b1 ...)` gives `a0 = b0`, `a1 = b1`, ... */
    private def peel(equation: Kernel.Thm): Either[LogicError, List[Kernel.Thm]] =
      Term.destEq(equation.conclusion) match {
        case Some((App(App(Const(Product.Pairing, _), a), rest), App(App(Const(Product.Pairing, _), b), others))) =>
          for {
            injective <- pairInjective
            typed = at(injective, Point -> Term.typeOf(a), Classical.CodomainVariable -> Term.typeOf(rest))
            instance <- rules.specAll(typed, List(a, rest, b, others))
            split <- LogicError.lift(Kernel.eqMp(instance, equation))
            head <- rules.conjElim1(split)
            tail <- rules.conjElim2(split)
            more <- peel(tail)
          } yield head :: more
        case _ => Right(Nil)
      }
  }

  private object Shapes {
    def of(tools: Tools, universe: Universe): Either[LogicError, Shapes] = Right(Shapes(tools, universe))
  }

  /* ================================================================ the representing set */

  /**
   * `F`, the operator whose least fixed point is the set of trees the constructors reach, that set,
   * the introduction rule at each constructor, and the witness the type is carved with.
   */
  private final case class Representing(
    operator: Term,
    set: Term,
    monotone: Kernel.Thm,
    introduction: Kernel.Thm,
    witness: Kernel.Thm,
    clauses: Int => Either[LogicError, (List[FVar], List[FVar], Term)],
    tools: Tools,
    universe: Universe,
    shapes: Shapes
  ) {
    import tools.*

    /** `NODE (label k xs) (children ys)`. */
    def nodeOf(k: Int, fixed: List[Term], recursive: List[Term]): Either[LogicError, Term] =
      for {
        labelled <- shapes.label(k, fixed)
        below <- shapes.children(recursive)
        result <- app(universe.node, labelled, below)
      } yield result

    /** `|- REP (NODE (label k xs) (children ys))` from `|- REP yi`, one per recursive argument. */
    def introduce(k: Int, fixed: List[Term], recursive: List[Term], members: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      introduceInto(set, k, fixed, recursive, members, introduction, operator)

    /**
     * The same for any set `S` for which `|- !x. F S x ==> S x` is at hand.
     */
    def introduceInto(
      target: Term,
      k: Int,
      fixed: List[Term],
      recursive: List[Term],
      members: List[Kernel.Thm],
      closed: Kernel.Thm,
      op: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        tree <- nodeOf(k, fixed, recursive)
        unfolded <- applied(op, List(target, tree))
        body <- rightOf(unfolded)
        disjuncts <- Datatype.disjuncts(logic, body, universe.specification.constructors.length)
        clause = disjuncts(k)
        equation = Conv.refl(tree)
        proofOfBody <- conjoined(equation :: members)
        proved <- witnessed(clause, fixed ++ recursive, proofOfBody)
        injectedProof <- injected(disjuncts, k, proved)
        back <- Conv.sym(unfolded)
        image <- LogicError.lift(Kernel.eqMp(back, injectedProof))
        result <- rules.spec(tree, closed).flatMap(rules.mp(_, image))
      } yield result
  }

  /** The domain types of the first `count` universal quantifiers of `term`. */
  private def quantifierTypes(logic: Logic, term: Term, count: Int): Either[LogicError, List[Type]] =
    if (count == 0) Right(Nil)
    else
      logic.destForallPredicate(term) match {
        case Some(predicate @ Abs(binderType, _)) =>
          for {
            opened <- LogicError.lift(Term.app(predicate, Term.variable("v_", binderType)))
            body <- Term.betaReduce(opened).toRight(NotOfForm("a redex", opened))
            rest <- quantifierTypes(logic, body, count - 1)
          } yield binderType :: rest
        case _ => Left(NotOfForm("a universal quantification", term))
      }

  /** One per argument, from the fixed ones and the recursive ones, in the order `shape` takes them. */
  private def interleave[A](shape: List[Argument], fixed: List[A], recursive: List[A]): List[A] =
    (shape, fixed, recursive) match {
      case (Argument.Of(_) :: rest, head :: others, _) => head :: interleave(rest, others, recursive)
      case (Argument.Recursive :: rest, _, head :: others) => head :: interleave(rest, fixed, others)
      case _ => Nil
    }

  /** The `count` disjuncts of a disjunction built by `disjoin`. */
  private def disjuncts(logic: Logic, body: Term, count: Int): Either[LogicError, List[Term]] =
    if (count <= 1) Right(List(body))
    else
      for {
        parts <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
        rest <- disjuncts(logic, parts._2, count - 1)
      } yield parts._1 :: rest

  private object Representing {

    def of(tools: Tools, universe: Universe, nodes: NodeFacts, shapes: Shapes): Either[LogicError, Representing] = {
      import tools.*
      val specification = universe.specification
      val sets = Type.fun(universe.tree, Type.Bool)
      val s = Term.variable("S", sets)
      val r = Term.variable("r", universe.tree)

      /** The bound variables of clause `k`: the fixed arguments and one tree per recursive one. */
      def boundOf(k: Int): (List[FVar], List[FVar]) = {
        val constructor = specification.constructors(k)
        val fixed = constructor.arguments.zipWithIndex.collect { case (Argument.Of(ty), position) =>
          Term.variable(s"a$position", ty)
        }
        val recursive = universe.recursivePositions(k).map(position => Term.variable(s"y$position", universe.tree))
        (fixed, recursive)
      }

      def clauseOf(set: Term, point: Term, k: Int): Either[LogicError, (List[FVar], List[FVar], Term)] = {
        val (fixed, recursive) = boundOf(k)
        for {
          labelled <- shapes.label(k, fixed)
          below <- shapes.children(recursive)
          tree <- app(universe.node, labelled, below)
          equation <- equal(point, tree)
          members <- recursive.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, child) =>
            acc.flatMap(list => app(set, child).map(list :+ _)))
          body <- conjoin(equation :: members)
          closed <- exists(fixed ++ recursive, body)
        } yield (fixed, recursive, closed)
      }

      for {
        clauses <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Term]]](Right(Nil))(
          (acc, k) => acc.flatMap(list => clauseOf(s, r, k).map(clause => list :+ clause._3)))
        body <- disjoin(clauses)
        operator <- LogicError.lift(Term.absAll(List(s, r), body))
        inductiveConstant <- constant(Inductive.Name, Type.fun(Type.fun(sets, sets), sets))
        set <- app(inductiveConstant, operator)
        monotone <- Monotone.prove(logic, tools.ground.inductive, operator)
        introductionFact <- tools.ground.inductive.fact(Inductive.Introduction)
        introduction <- rules
          .spec(operator, at(introductionFact, Point -> universe.tree))
          .flatMap(rules.mp(_, monotone))
        first = specification.constructors.indexWhere(_.arguments.forall(_ != Argument.Recursive))
        partial = Representing(
          operator,
          set,
          monotone,
          introduction,
          introduction,
          k => clauseOf(s, r, k),
          tools,
          universe,
          shapes
        )
        fixedWitnesses = specification.constructors(first).arguments.collect { case Argument.Of(ty) => ty }
        chosen <- fixedWitnesses.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, ty) =>
          for {
            list <- acc
            choice <- tools.select(ty)
            predicate <- LogicError.lift(Term.abs(Term.variable("z", ty), logic.truth))
            chosenTerm <- app(choice, predicate)
          } yield list :+ chosenTerm
        }
        witness <- partial.introduce(first, chosen, Nil, Nil)
      } yield partial.copy(witness = witness)
    }
  }

  /* ================================================================ the constructors */

  private def declareConstructors(
    ground: Ground,
    theory: Theory,
    notation: Notation,
    specification: Specification,
    universe: Universe,
    carrier: Type
  ): Either[LogicError, (Theory, Vector[Term], Map[String, Kernel.Thm])] =
    for {
      narrow <- ground.classical.logic.over(theory)
      tools = Tools(ground, narrow, theory, notation)
      shapes = Shapes(tools, universe)
      abstraction <- LogicError.lift(theory.constant(specification.abstraction, Type.fun(universe.tree, carrier)))
      representation <- LogicError.lift(theory.constant(specification.representation, Type.fun(carrier, universe.tree)))
      result <- specification.constructors.zipWithIndex.foldLeft[Either[LogicError, (Theory, Vector[Term], Map[String, Kernel.Thm])]](
        Right((theory, Vector.empty, Map.empty))
      ) { case (acc, (constructor, k)) =>
        val variables = constructor.arguments.zipWithIndex.map {
          case (Argument.Of(ty), position) => Term.variable(s"a$position", ty)
          case (Argument.Recursive, position) => Term.variable(s"y$position", carrier)
        }
        val fixed = constructor.arguments.zip(variables).collect { case (Argument.Of(_), v) => v }
        val recursive = constructor.arguments.zip(variables).collect { case (Argument.Recursive, v) => v }
        for {
          state <- acc
          (current, built, definitions) = state
          represented <- recursive.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((list, child) =>
            list.flatMap(l => LogicError.lift(Term.app(representation, child)).map(l :+ _)))
          labelled <- shapes.label(k, fixed)
          below <- shapes.children(represented)
          tree <- LogicError.lift(Term.appAll(universe.node, List(labelled, below)))
          value <- LogicError.lift(Term.app(abstraction, tree))
          body <- LogicError.lift(Term.absAll(variables, value))
          defined <- LogicError.lift(Kernel.defineConstant(current, constructor.name, body))
          (next, definition) = defined
          declared <- LogicError.lift(next.constant(constructor.name, Term.typeOf(body)))
        } yield (next, built :+ declared, definitions + (constructor.name -> definition))
      }
    } yield result

  /* ================================================================ the facts */

  private final case class Carried(
    tools: Tools,
    universe: Universe,
    nodes: NodeFacts,
    shapes: Shapes,
    representing: Representing,
    carrier: Type,
    abstraction: Term,
    representation: Term,
    absRep: Kernel.Thm,
    repAbs: Kernel.Thm,
    constructors: Vector[Term],
    definitions: Map[String, Kernel.Thm]
  ) {
    import tools.*
    private val specification = universe.specification
    private val count = specification.constructors.length
    private val shapesHere = Shapes(tools, universe)
    private val representingHere = representing.copy(tools = tools, shapes = shapesHere)

    private def abstractVariable: Either[LogicError, FVar] =
      leftOf(absRep).flatMap {
        case App(_, App(_, variable: FVar)) => Right(variable)
        case other => Left(NotOfForm("mk (dest a)", other))
      }

    private def representingVariable: Either[LogicError, FVar] =
      leftOf(repAbs).flatMap {
        case App(_, variable: FVar) => Right(variable)
        case other => Left(NotOfForm("REP r", other))
      }

    /** The arguments of constructor `k` as fresh variables, with a suffix to tell two sets apart. */
    def argumentsOf(k: Int, suffix: String): List[FVar] =
      specification.constructors(k).arguments.zipWithIndex.map {
        case (Argument.Of(ty), position) => Term.variable(s"a$position$suffix", ty)
        case (Argument.Recursive, position) => Term.variable(s"y$position$suffix", carrier)
      }

    def fixedOf(k: Int, arguments: List[Term]): List[Term] =
      specification.constructors(k).arguments.zip(arguments).collect { case (Argument.Of(_), a) => a }

    def recursiveOf(k: Int, arguments: List[Term]): List[Term] =
      specification.constructors(k).arguments.zip(arguments).collect { case (Argument.Recursive, a) => a }

    /** `|- REP (dest a)`, for a free `a`. */
    def everyRepresentationIsMember: Either[LogicError, Kernel.Thm] =
      for {
        a <- abstractVariable
        r <- representingVariable
        dest <- app(representation, a)
        characterised <- LogicError.lift(Kernel.inst(Map(r -> dest), repAbs))
        roundTrip <- Conv.apTerm(representation, absRep)
        back <- Conv.sym(characterised)
        result <- LogicError.lift(Kernel.eqMp(back, roundTrip))
      } yield result

    private def memberAt(member: Kernel.Thm, value: Term): Either[LogicError, Kernel.Thm] =
      abstractVariable.flatMap(a => LogicError.lift(Kernel.inst(Map(a -> value), member)))

    /** `|- dest (Ck args) = NODE (label k xs) (children (dest ys))`, over free arguments. */
    def representationsOfConstructors(member: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
      specification.constructors.indices.toVector.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        (acc, k) =>
          val arguments = argumentsOf(k, "")
          for {
            list <- acc
            unfolded <- Conv.unfold(definitions(specification.constructors(k).name), arguments)
            carried <- Conv.apTerm(representation, unfolded)
            recursive = recursiveOf(k, arguments)
            represented <- recursive.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
              l.flatMap(list => app(representation, child).map(list :+ _)))
            members <- recursive.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, child) =>
              l.flatMap(list => memberAt(member, child).map(list :+ _)))
            isMember <- representingHere.introduce(k, fixedOf(k, arguments), represented, members)
            tree <- representingHere.nodeOf(k, fixedOf(k, arguments), represented)
            r <- representingVariable
            characterised <- LogicError.lift(Kernel.inst(Map(r -> tree), repAbs))
            roundTrip <- LogicError.lift(Kernel.eqMp(characterised, isMember))
            result <- Conv.trans(carried, roundTrip)
          } yield list :+ result
      }

    /** `NODE l c = NODE l' c'` at two constructors' representations, from their equality. */
    private def nodesAgree(
      destOf: Vector[Kernel.Thm],
      j: Int,
      left: List[FVar],
      k: Int,
      right: List[FVar]
    ): Either[LogicError, (Term, Kernel.Thm, Kernel.Thm)] =
      for {
        leftTerm <- app(constructors(j), left*)
        rightTerm <- app(constructors(k), right*)
        same <- equal(leftTerm, rightTerm)
        assumed <- assume(same)
        carried <- Conv.apTerm(representation, assumed)
        leftDest <- instantiated(destOf(j), argumentsOf(j, ""), left)
        rightDest <- instantiated(destOf(k), argumentsOf(k, ""), right)
        flipped <- Conv.sym(leftDest)
        nodesEqual <- Conv.trans(flipped, carried).flatMap(Conv.trans(_, rightDest))
        parts <- nodeParts(nodesEqual)
        split <- rules.mp(parts, nodesEqual)
      } yield (same, split, nodesEqual)

    private def instantiated(theorem: Kernel.Thm, from: List[FVar], to: List[FVar]): Either[LogicError, Kernel.Thm] =
      LogicError.lift(Kernel.inst(from.zip(to).toMap, theorem))

    /** `NODE l c = NODE l' c' ==> l = l' /\ c = c'` at the four terms of an equation between nodes. */
    private def nodeParts(nodesEqual: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        sides <- Term.destEq(nodesEqual.conclusion).toRight(NotOfForm("an equation", nodesEqual.conclusion))
        pieces <- (sides._1, sides._2) match {
          case (App(App(_, l1), c1), App(App(_, l2), c2)) => Right((l1, c1, l2, c2))
          case _ => Left(NotOfForm("two nodes", nodesEqual.conclusion))
        }
        (l1, c1, l2, c2) = pieces
        injective = nodes.injective
        variables = Term.freeVariables(injective.conclusion).toList
        byName = variables.map(v => v.name -> v).toMap
        result <- LogicError.lift(
          Kernel.inst(Map(byName("l") -> l1, byName("c") -> c1, byName("l'") -> l2, byName("c'") -> c2), injective)
        )
      } yield result

    /** One fact per constructor with arguments, `Ck xs = Ck ys ==> x0 = y0 /\ ...`. */
    def injectivityFacts(destOf: Vector[Kernel.Thm]): Either[LogicError, Map[String, Kernel.Thm]] =
      specification.constructors.indices.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
        (acc, k) =>
          val constructor = specification.constructors(k)
          if (constructor.arguments.isEmpty) acc
          else {
            val left = argumentsOf(k, "")
            val right = argumentsOf(k, "'")
            for {
              map <- acc
              agreed <- nodesAgree(destOf, k, left, k, right)
              (same, split, _) = agreed
              labels <- rules.conjElim1(split)
              kids <- rules.conjElim2(split)
              fixedEquations <- shapesHere.labelsAgree(k, fixedOf(k, left), fixedOf(k, right)).flatMap {
                case (statement, equations) =>
                  equations.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, equation) =>
                    l.flatMap(list => rules.disch(statement, equation).flatMap(rules.mp(_, labels)).map(list :+ _)))
              }
              recursiveLeft = recursiveOf(k, left)
              recursiveRight = recursiveOf(k, right)
              leftRepresented <- recursiveLeft.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
                l.flatMap(list => app(representation, child).map(list :+ _)))
              rightRepresented <- recursiveRight.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
                l.flatMap(list => app(representation, child).map(list :+ _)))
              recursiveEquations <- recursiveLeft.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
                (l, index) =>
                  for {
                    list <- l
                    position <- numeral(index)
                    atIndex <- Conv.apThm(kids, position)
                    leftAt <- shapesHere.childAt(leftRepresented, index)
                    rightAt <- shapesHere.childAt(rightRepresented, index)
                    flipped <- Conv.sym(leftAt)
                    represented <- Conv.trans(flipped, atIndex).flatMap(Conv.trans(_, rightAt))
                    abstracted <- Conv.apTerm(abstraction, represented)
                    leftBack <- abstractVariable.flatMap(a =>
                      LogicError.lift(Kernel.inst(Map(a -> recursiveLeft(index)), absRep)))
                    rightBack <- abstractVariable.flatMap(a =>
                      LogicError.lift(Kernel.inst(Map(a -> recursiveRight(index)), absRep)))
                    flippedLeft <- Conv.sym(leftBack)
                    result <- Conv.trans(flippedLeft, abstracted).flatMap(Conv.trans(_, rightBack))
                  } yield list :+ result
              }
              // Put the equations back in the order the constructor takes its arguments.
              ordered = interleave(constructor.arguments, fixedEquations, recursiveEquations)
              conclusion <- conjoined(ordered)
              discharged <- rules.disch(same, conclusion)
              result <- rules.genAll(discharged, left ++ right)
            } yield map + (constructor.name -> result)
          }
      }

    /** One fact per pair `j < k`, `~(Cj xs = Ck ys)`. */
    def distinctnessFacts(destOf: Vector[Kernel.Thm]): Either[LogicError, Map[(String, String), Kernel.Thm]] = {
      val pairs = for { j <- 0 until count; k <- (j + 1) until count } yield (j, k)
      pairs.foldLeft[Either[LogicError, Map[(String, String), Kernel.Thm]]](Right(Map.empty)) { case (acc, (j, k)) =>
        val left = argumentsOf(j, "")
        val right = argumentsOf(k, "'")
        for {
          map <- acc
          agreed <- nodesAgree(destOf, j, left, k, right)
          (same, split, _) = agreed
          labels <- rules.conjElim1(split)
          differ <- shapesHere.labelsDiffer(j, fixedOf(j, left), k, fixedOf(k, right))
          (statement, absurd) = differ
          absurdHere <- rules.disch(statement, absurd).flatMap(rules.mp(_, labels))
          negated <- rules.notIntro(same, absurdHere)
          result <- rules.genAll(negated, left ++ right)
        } yield map + ((specification.constructors(j).name, specification.constructors(k).name) -> result)
      }
    }

    /** The hypothesis of the induction principle, over a predicate `P`. */
    private def inductionHypotheses(predicate: Term): Either[LogicError, List[Term]] =
      specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, k) =>
        val arguments = argumentsOf(k, "")
        for {
          list <- acc
          applied <- app(constructors(k), arguments*)
          conclusion <- app(predicate, applied)
          premises <- recursiveOf(k, arguments).foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
            l.flatMap(list => app(predicate, child).map(list :+ _)))
          body <- premises.foldRight[Either[LogicError, Term]](Right(conclusion))((premise, rest) =>
            rest.flatMap(imp(premise, _)))
          closed <- forall(arguments, body)
        } yield list :+ closed
      }

    /** `|- !P. (!xs. P y0 ==> ... ==> P (C0 xs)) /\ ... ==> !t. P t`. */
    def inductionPrinciple(member: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val predicate = Term.variable("P", Type.fun(carrier, Type.Bool))
      val t = Term.variable("t", carrier)
      val r = Term.variable("r", universe.tree)
      for {
        hypotheses <- inductionHypotheses(predicate)
        hypothesis <- conjoin(hypotheses)
        assumedHypothesis <- assume(hypothesis)
        perConstructor <- conjuncts(assumedHypothesis, count)

        // Q = \r. REP r /\ P (mk r)
        memberOfR <- app(representing.set, r)
        abstracted <- app(abstraction, r)
        holdsOfR <- app(predicate, abstracted)
        strengthened <- conj(memberOfR, holdsOfR)
        q <- LogicError.lift(Term.abs(r, strengthened))

        // Q is F-closed
        image <- applied(representing.operator, List(q, r))
        imageBody <- rightOf(image)
        clauses <- Datatype.disjuncts(logic, imageBody, count)
        cases <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
          (acc, k) =>
            for {
              list <- acc
              proved <- closedAt(k, clauses(k), q, r, predicate, perConstructor(k), member)
            } yield list :+ proved
        }
        assumedImage <- assume(imageBody)
        qAtR <- byCases(assumedImage, clauses, cases)
        imageStatement <- leftOf(image)
        fromImage <- rules
          .disch(imageBody, qAtR)
          .flatMap(step => assume(imageStatement).flatMap(held => LogicError.lift(Kernel.eqMp(image, held))).flatMap(rules.mp(step, _)))
        closure <- rules.disch(imageStatement, fromImage).flatMap(rules.gen(r, _))

        inductionFact <- tools.ground.inductive.fact(Inductive.Induction)
        inducted <- rules
          .specAll(at(inductionFact, Point -> universe.tree), List(representing.operator, q))
          .flatMap(rules.mp(_, closure))

        dest <- app(representation, t)
        atT <- rules.spec(dest, inducted)
        memberT <- memberAt(member, t)
        qAtDest <- rules.mp(atT, memberT)
        qAtDestTerm <- app(q, dest)
        opened <- Conv.betaRoot(qAtDestTerm)
        both <- LogicError.lift(Kernel.eqMp(opened, qAtDest))
        holds <- rules.conjElim2(both)
        a <- abstractVariable
        roundTrip <- LogicError.lift(Kernel.inst(Map(a -> t), absRep))
        carried <- Conv.apTerm(predicate, roundTrip)
        result <- LogicError.lift(Kernel.eqMp(carried, holds))
        everywhere <- rules.gen(t, result)
        discharged <- rules.disch(hypothesis, everywhere)
        closed <- rules.gen(predicate, discharged)
      } yield closed
    }

    /** Under clause `k` of `F Q r`, `Q r`. */
    private def closedAt(
      k: Int,
      clause: Term,
      q: Term,
      r: FVar,
      predicate: Term,
      hypothesis: Kernel.Thm,
      member: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] = {
      val fixed = argumentsOf(k, "").zip(specification.constructors(k).arguments).collect {
        case (v, Argument.Of(_)) => v
      }
      val recursive = universe.recursivePositions(k).map(position => Term.variable(s"y$position", universe.tree))
      for {
        assumedClause <- assume(clause)
        inside <- {
          for {
            bodyStatement <- existentialBody(clause, fixed ++ recursive)
            assumedBody <- assume(bodyStatement)
            parts <- conjuncts(assumedBody, 1 + recursive.length)
            equation = parts.head
            children <- parts.tail.foldLeft[Either[LogicError, List[(Kernel.Thm, Kernel.Thm)]]](Right(Nil)) { (l, part) =>
              for {
                list <- l
                opened <- Conv.betaRoot(part.conclusion)
                both <- LogicError.lift(Kernel.eqMp(opened, part))
                inSet <- rules.conjElim1(both)
                holds <- rules.conjElim2(both)
              } yield list :+ ((inSet, holds))
            }
            // REP r
            nodeMember <- representingHere.introduce(k, fixed, recursive, children.map(_._1))
            membership <- Conv.apTerm(representingHere.set, equation).flatMap(Conv.sym).flatMap(eqn =>
              LogicError.lift(Kernel.eqMp(eqn, nodeMember)))
            // P (mk r)
            abstractedChildren <- recursive.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
              l.flatMap(list => app(abstraction, child).map(list :+ _)))
            arguments = interleave(specification.constructors(k).arguments, fixed, abstractedChildren)
            atArguments <- rules.specAll(hypothesis, arguments)
            holdsOfConstructor <- children.foldLeft[Either[LogicError, Kernel.Thm]](Right(atArguments))((acc, child) =>
              acc.flatMap(rules.mp(_, child._2)))
            unfolded <- Conv.unfold(definitions(specification.constructors(k).name), arguments)
            // dest (mk yi) = yi, from REP yi
            roundTrips <- children.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (l, child) =>
              for {
                list <- l
                inSet = child._1
                rv <- representingVariable
                point <- inSet.conclusion match {
                  case App(_, value) => Right(value)
                  case other => Left(NotOfForm("REP y", other))
                }
                characterised <- LogicError.lift(Kernel.inst(Map(rv -> point), repAbs))
                result <- LogicError.lift(Kernel.eqMp(characterised, inSet))
              } yield list :+ result
            }
            holes = recursive.map(y => Term.variable(s"${y.name}_", universe.tree))
            labelled <- shapesHere.label(k, fixed)
            below <- shapesHere.children(holes)
            nodeTemplate <- app(universe.node, labelled, below)
            template <- app(abstraction, nodeTemplate)
            simplified <- congruence(holes, template, roundTrips)
            toR <- Conv.apTerm(abstraction, equation).flatMap(Conv.sym)
            chain <- Conv.trans(unfolded, simplified).flatMap(Conv.trans(_, toR))
            carried <- Conv.apTerm(predicate, chain)
            holds <- LogicError.lift(Kernel.eqMp(carried, holdsOfConstructor))
            both <- rules.conjIntro(membership, holds)
            applied <- app(q, r)
            opened <- Conv.betaRoot(applied)
            back <- Conv.sym(opened)
            result <- LogicError.lift(Kernel.eqMp(back, both))
          } yield result
        }
        result <- opened(assumedClause, fixed ++ recursive, inside)
      } yield result
    }

    /** The body of `?v1 ... vn. body` at the given variables, by root contractions. */
    def existentialBody(existential: Term, variables: List[FVar]): Either[LogicError, Term] =
      variables.foldLeft[Either[LogicError, Term]](Right(existential)) { (acc, variable) =>
        for {
          current <- acc
          predicate <- logic.destExistsPredicate(current).toRight(NotOfForm("an existential", current))
          applied <- app(predicate, variable)
          reduced <- Conv.betaRoot(applied)
          result <- rightOf(reduced)
        } yield result
      }

    /** `|- !t. (?xs. t = C0 xs) \/ ...`, by induction with the predicate being that disjunction. */
    def caseAnalysis(inducted: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val t = Term.variable("t", carrier)
      for {
        disjunctsAtT <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) {
          (acc, k) =>
            val arguments = argumentsOf(k, "")
            for {
              list <- acc
              applied <- app(constructors(k), arguments*)
              equation <- equal(t, applied)
              closed <- exists(arguments, equation)
            } yield list :+ closed
        }
        body <- disjoin(disjunctsAtT)
        predicate <- LogicError.lift(Term.abs(t, body))
        atPredicate <- rules.spec(predicate, inducted)
        hypotheses <- logic.destImp(atPredicate.conclusion).map(_._1).toRight(NotOfForm("an implication", atPredicate.conclusion))
        clauses <- conjunctsOf(hypotheses, count)
        proofs <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
          (acc, k) =>
            val arguments = argumentsOf(k, "")
            for {
              list <- acc
              clause = clauses(k)
              applied <- app(constructors(k), arguments*)
              atConstructor <- app(predicate, applied)
              opened <- Conv.betaRoot(atConstructor)
              openedBody <- rightOf(opened)
              parts <- Datatype.disjuncts(logic, openedBody, count)
              reflexive = Conv.refl(applied)
              proved <- witnessed(parts(k), arguments, reflexive)
              injectedProof <- injected(parts, k, proved)
              back <- Conv.sym(opened)
              folded <- LogicError.lift(Kernel.eqMp(back, injectedProof))
              premises <- recursiveOf(k, arguments).foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
                l.flatMap(list => app(predicate, child).map(list :+ _)))
              discharged <- premises.foldRight[Either[LogicError, Kernel.Thm]](Right(folded))((premise, acc) =>
                acc.flatMap(rules.disch(premise, _)))
              closed <- rules.genAll(discharged, arguments)
              _ <- if (closed.conclusion == clause) Right(()) else Left(NotOfForm("the clause", closed.conclusion))
            } yield list :+ closed
        }
        together <- conjoined(proofs)
        everywhere <- rules.mp(atPredicate, together)
        atT <- rules.spec(t, everywhere)
        reduced <- Conv.betaRoot(atT.conclusion)
        opened <- LogicError.lift(Kernel.eqMp(reduced, atT))
        result <- rules.gen(t, opened)
      } yield result
    }

    private def conjunctsOf(term: Term, count: Int): Either[LogicError, List[Term]] =
      if (count <= 1) Right(List(term))
      else
        for {
          parts <- logic.destConj(term).toRight(NotOfForm("a conjunction", term))
          rest <- conjunctsOf(parts._2, count - 1)
        } yield parts._1 :: rest

    /**
     * `|- !f0 ... fk. ?h. (!xs. h (C0 xs) = f0 xs (h y0) ...) /\ ...`, through the graph.
     */
    def recursionTheorem(
      inducted: Kernel.Thm,
      injectivity: Map[String, Kernel.Thm],
      distinctness: Map[(String, String), Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      GraphRecursion.prove(this, inducted, injectivity, distinctness)
  }

  /* ================================================================ recursion */

  /** The recursion theorem, which is long enough to be read on its own. */
  private object GraphRecursion {

    def resultType(specification: Specification, carrier: Type): TyVar = {
      val used = specification.constructors.flatMap(_.arguments).collect { case Argument.Of(ty) => Type.variables(ty) }.flatten.toSet ++
        Type.variables(carrier)
      val name = LazyList.from(0).map(n => if (n == 0) "b" else s"b$n").find(!used.contains(_)).get
      TyVar(name)
    }

    def prove(
      carried: Carried,
      inducted: Kernel.Thm,
      injectivity: Map[String, Kernel.Thm],
      distinctness: Map[(String, String), Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] = {
      import carried.*
      import carried.tools.*
      val specification = carried.universe.specification
      val count = specification.constructors.length
      val result = resultType(specification, carrier)
      val pairs = TyApp(Product.TypeName, List(carrier, result))
      val graphSets = Type.fun(pairs, Type.Bool)

      /** `fk : args -> results -> result`. */
      val functions: List[FVar] = specification.constructors.indices.toList.map { k =>
        val constructor = specification.constructors(k)
        val argumentTypes = constructor.arguments.map {
          case Argument.Of(ty) => ty
          case Argument.Recursive => carrier
        }
        val resultTypes = constructor.arguments.collect { case Argument.Recursive => result }
        Term.variable(s"f$k", (argumentTypes ++ resultTypes).foldRight[Type](result)((ty, acc) => Type.fun(ty, acc)))
      }

      def resultsOf(k: Int, suffix: String): List[FVar] =
        universe.recursivePositions(k).map(position => Term.variable(s"v$position$suffix", result))

      val s = Term.variable("S", graphSets)
      val p = Term.variable("p", pairs)

      def pairOf(left: Term, right: Term): Either[LogicError, Term] =
        for {
          pair <- constant(Product.Pairing, Type.fun(carrier, Type.fun(result, pairs)))
          built <- app(pair, left, right)
        } yield built

      def valueOf(k: Int, arguments: List[Term], results: List[Term]): Either[LogicError, Term] =
        app(functions(k), (arguments ++ results)*)

      def graphClause(set: Term, point: Term, k: Int): Either[LogicError, (List[FVar], List[FVar], Term)] = {
        val arguments = argumentsOf(k, "")
        val results = resultsOf(k, "")
        for {
          applied <- app(constructors(k), arguments*)
          value <- valueOf(k, arguments, results)
          pair <- pairOf(applied, value)
          equation <- equal(point, pair)
          members <- recursiveOf(k, arguments).zip(results).foldLeft[Either[LogicError, List[Term]]](Right(Nil)) {
            case (l, (child, v)) =>
              for { list <- l; pairTerm <- pairOf(child, v); inSet <- app(set, pairTerm) } yield list :+ inSet
          }
          body <- conjoin(equation :: members)
          closed <- exists(arguments ++ results, body)
        } yield (arguments, results, closed)
      }

      for {
        clauses <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Term]]](Right(Nil))(
          (acc, k) => acc.flatMap(list => graphClause(s, p, k).map(list :+ _._3)))
        body <- disjoin(clauses)
        operator <- LogicError.lift(Term.absAll(List(s, p), body))
        inductiveConstant <- constant(Inductive.Name, Type.fun(Type.fun(graphSets, graphSets), graphSets))
        graph <- app(inductiveConstant, operator)
        monotone <- Monotone.prove(logic, tools.ground.inductive, operator)
        introductionFact <- tools.ground.inductive.fact(Inductive.Introduction)
        introduction <- rules.spec(operator, at(introductionFact, Point -> pairs)).flatMap(rules.mp(_, monotone))
        fixpointFact <- tools.ground.inductive.fact(Inductive.Fixpoint)
        fixpoint <- rules.spec(operator, at(fixpointFact, Point -> pairs)).flatMap(rules.mp(_, monotone))

        /* `|- G (PAIR (Ck xs) (fk xs vs))` from `|- G (PAIR yi vi)`. */
        introduce = (k: Int, arguments: List[Term], results: List[Term], members: List[Kernel.Thm]) =>
          for {
            applied <- app(constructors(k), arguments*)
            value <- valueOf(k, arguments, results)
            pair <- pairOf(applied, value)
            unfolded <- carried.tools.applied(operator, List(graph, pair))
            imageBody <- rightOf(unfolded)
            parts <- Datatype.disjuncts(logic, imageBody, count)
            proofOfBody <- conjoined(Conv.refl(pair) :: members)
            proved <- witnessed(parts(k), arguments ++ results, proofOfBody)
            injectedProof <- injected(parts, k, proved)
            back <- Conv.sym(unfolded)
            image <- LogicError.lift(Kernel.eqMp(back, injectedProof))
            result <- rules.spec(pair, introduction).flatMap(rules.mp(_, image))
          } yield result

        /* The predicate the induction runs on: a value, and only one. */
        t = Term.variable("t", carrier)
        y = Term.variable("v", result)
        y2 = Term.variable("w", result)
        atTY <- pairOf(t, y).flatMap(app(graph, _))
        atTY2 <- pairOf(t, y2).flatMap(app(graph, _))
        sameValue <- equal(y2, y)
        uniqueness <- imp(atTY2, sameValue).flatMap(logic.mkForall(y2, _))
        both <- conj(atTY, uniqueness)
        exactlyOne <- logic.mkExists(y, both)
        predicate <- LogicError.lift(Term.abs(t, exactlyOne))

        atPredicate <- rules.spec(predicate, inducted)
        hypotheses <- logic.destImp(atPredicate.conclusion).map(_._1).toRight(NotOfForm("an implication", atPredicate.conclusion))
        steps <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
          (acc, k) =>
            for {
              list <- acc
              step <- functionalAt(
                carried, k, predicate, graph, operator, fixpoint, introduce, pairOf, valueOf,
                resultsOf, injectivity, distinctness, result
              )
            } yield list :+ step
        }
        together <- conjoined(steps)
        everywhere <- rules.mp(atPredicate, together)

        /* h = \t. select (\v. G (PAIR t v) /\ !w. G (PAIR t w) ==> w = v), the predicate the
           witness at each `t` is chosen by, so the choice here and the one `witness` names agree */
        choice <- tools.select(result)
        valuesAt <- logic.destExistsPredicate(exactlyOne).toRight(NotOfForm("an existential", exactlyOne))
        chosen <- app(choice, valuesAt)
        h <- LogicError.lift(Term.abs(t, chosen))

        equations <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
          (acc, k) =>
            val arguments = argumentsOf(k, "")
            for {
              list <- acc
              equation <- equationAt(carried, k, arguments, everywhere, predicate, graph, h, introduce, pairOf, valueOf)
            } yield list :+ equation
        }
        conjunction <- conjoined(equations)
        hVariable = Term.variable("h", Type.fun(carrier, result))
        statementBody <- {
          val hs = specification.constructors.indices.toList.map { k =>
            val arguments = argumentsOf(k, "")
            for {
              applied <- app(constructors(k), arguments*)
              left <- app(hVariable, applied)
              recursiveValues <- recursiveOf(k, arguments).foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
                l.flatMap(list => app(hVariable, child).map(list :+ _)))
              right <- valueOf(k, arguments, recursiveValues)
              equation <- equal(left, right)
              closed <- forall(arguments, equation)
            } yield closed
          }
          hs.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, e) => acc.flatMap(list => e.map(list :+ _)))
            .flatMap(conjoin)
        }
        predicateOfH <- LogicError.lift(Term.abs(hVariable, statementBody))
        applied <- app(predicateOfH, h)
        opened <- Conv.betaRoot(applied)
        // the statement at h, with the beta redexes `h x` that the substitution left
        target <- rightOf(opened)
        normalised <- reconcile(conjunction, target)
        folded <- Conv.sym(opened).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, normalised)))
        witnessedH <- rules.existsIntro(predicateOfH, h, normalised)
        result <- rules.genAll(witnessedH, functions)
      } yield result
    }

    /**
     * A proof of `target` from a proof of a statement equal to it up to the root contractions of
     * `(\t. select ...) x`, which the substitution of `h` into the statement leaves standing.
     */
    private def reconcile(proof: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      if (proof.conclusion == target) Right(proof)
      else Left(NotOfForm("the recursion equations as stated", proof.conclusion))

    /** The induction step at constructor `k`: exactly one value at `Ck xs` if at each `yi`. */
    private def functionalAt(
      carried: Carried,
      k: Int,
      predicate: Term,
      graph: Term,
      operator: Term,
      fixpoint: Kernel.Thm,
      introduce: (Int, List[Term], List[Term], List[Kernel.Thm]) => Either[LogicError, Kernel.Thm],
      pairOf: (Term, Term) => Either[LogicError, Term],
      valueOf: (Int, List[Term], List[Term]) => Either[LogicError, Term],
      resultsOf: (Int, String) => List[FVar],
      injectivity: Map[String, Kernel.Thm],
      distinctness: Map[(String, String), Kernel.Thm],
      result: Type
    ): Either[LogicError, Kernel.Thm] = {
      import carried.*
      import carried.tools.*
      val specification = carried.universe.specification
      val count = specification.constructors.length
      val arguments = argumentsOf(k, "")
      val recursive = recursiveOf(k, arguments)
      val values = resultsOf(k, "")
      for {
        applied <- app(constructors(k), arguments*)
        conclusion <- app(predicate, applied)
        premises <- recursive.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((l, child) =>
          l.flatMap(list => app(predicate, child).map(list :+ _)))

        // Each premise, opened: ?v. G (yi, v) /\ !w. G (yi, w) ==> w = v
        openedPremises <- premises.foldLeft[Either[LogicError, List[(Term, Kernel.Thm)]]](Right(Nil)) { (l, premise) =>
          for {
            list <- l
            opened <- Conv.betaRoot(premise)
            body <- rightOf(opened)
            held <- assume(premise).flatMap(assumed => LogicError.lift(Kernel.eqMp(opened, assumed)))
          } yield list :+ ((body, held))
        }
        // Under `G (yi, vi) /\ !w. ...` for each i, with vi the fresh values
        instanceBodies <- openedPremises.zip(values).foldLeft[Either[LogicError, List[Term]]](Right(Nil)) {
          case (l, ((existential, _), v)) =>
            for {
              list <- l
              predicateOfV <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
              atV <- app(predicateOfV, v)
              reduced <- Conv.betaRoot(atV)
              body <- rightOf(reduced)
            } yield list :+ body
        }
        assumedInstances <- instanceBodies.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, body) =>
          l.flatMap(list => assume(body).map(list :+ _)))
        memberships <- assumedInstances.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, held) =>
          l.flatMap(list => rules.conjElim1(held).map(list :+ _)))
        uniquenesses <- assumedInstances.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, held) =>
          l.flatMap(list => rules.conjElim2(held).map(list :+ _)))

        // existence
        exists <- introduce(k, arguments, values, memberships)
        value <- valueOf(k, arguments, values)

        // uniqueness: G (Ck xs, w) ==> w = fk xs vs
        w = Term.variable("w", result)
        pairW <- pairOf(applied, w)
        atW <- app(graph, pairW)
        assumedAtW <- assume(atW)
        unfolded <- rules.spec(pairW, fixpoint)
        imageAtW <- LogicError.lift(Kernel.eqMp(unfolded, assumedAtW))
        opened <- carried.tools.applied(operator, List(graph, pairW))
        imageBody <- rightOf(opened)
        openedImage <- LogicError.lift(Kernel.eqMp(opened, imageAtW))
        clauses <- Datatype.disjuncts(logic, imageBody, count)
        goal <- equal(w, value)
        cases <- specification.constructors.indices.toList.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
          (acc, j) =>
            for {
              list <- acc
              proved <- uniqueAt(
                carried, k, j, clauses(j), applied, w, value, goal, arguments, values, memberships,
                uniquenesses, pairOf, valueOf, resultsOf, injectivity, distinctness, graph
              )
            } yield list :+ proved
        }
        unique <- byCases(openedImage, clauses, cases)
        uniqueStatement <- rules.disch(atW, unique).flatMap(rules.gen(w, _))
        bothHold <- rules.conjIntro(exists, uniqueStatement)

        atConclusion <- Conv.betaRoot(conclusion)
        exactlyOne <- rightOf(atConclusion)
        witnessedValue <- witnessed(exactlyOne, List(value), bothHold)
        folded <- Conv.sym(atConclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, witnessedValue)))

        // discharge the instances, then the premises
        eliminated <- openedPremises.zip(values).foldLeft[Either[LogicError, Kernel.Thm]](Right(folded)) {
          case (acc, ((_, heldPremise), v)) => acc.flatMap(rules.existsElim(heldPremise, v, _))
        }
        discharged <- premises.foldRight[Either[LogicError, Kernel.Thm]](Right(eliminated))((premise, acc) =>
          acc.flatMap(rules.disch(premise, _)))
        closed <- rules.genAll(discharged, arguments)
      } yield closed
    }

    /** Under clause `j` of the graph at `(Ck xs, w)`, `w = fk xs vs`. */
    private def uniqueAt(
      carried: Carried,
      k: Int,
      j: Int,
      clause: Term,
      applied: Term,
      w: FVar,
      value: Term,
      goal: Term,
      arguments: List[FVar],
      values: List[FVar],
      memberships: List[Kernel.Thm],
      uniquenesses: List[Kernel.Thm],
      pairOf: (Term, Term) => Either[LogicError, Term],
      valueOf: (Int, List[Term], List[Term]) => Either[LogicError, Term],
      resultsOf: (Int, String) => List[FVar],
      injectivity: Map[String, Kernel.Thm],
      distinctness: Map[(String, String), Kernel.Thm],
      graph: Term
    ): Either[LogicError, Kernel.Thm] = {
      import carried.*
      import carried.tools.*
      val specification = carried.universe.specification
      val others = argumentsOf(j, "'")
      val otherValues = resultsOf(j, "'")
      for {
        assumedClause <- assume(clause)
        inside <- {
          for {
            body <- carried.existentialBody(clause, others ++ otherValues)
            assumedBody <- assume(body)
            parts <- conjuncts(assumedBody, 1 + otherValues.length)
            pairEquation = parts.head
            // PAIR (Ck xs) w = PAIR (Cj ys) (fj ys us)
            components <- peelPair(carried, pairEquation)
            (sameConstructor, sameValue) = components
            result <-
              if (j != k) {
                val (first, second) = if (k < j) (k, j) else (j, k)
                val names = (specification.constructors(first).name, specification.constructors(second).name)
                for {
                  refusal <- distinctness.get(names).toRight(MissingDefinition(distinct(names._1, names._2)))
                  oriented <- if (k < j) Right(sameConstructor) else Conv.sym(sameConstructor)
                  sides <- Term.destEq(oriented.conclusion).toRight(NotOfForm("an equation", oriented.conclusion))
                  firstArguments <- argumentsFrom(sides._1)
                  secondArguments <- argumentsFrom(sides._2)
                  atThem <- rules.specAll(refusal, firstArguments ++ secondArguments)
                  absurd <- rules.notElim(atThem, oriented)
                  result <- rules.falsityElim(goal, absurd)
                } yield result
              } else {
                val name = specification.constructors(k).name
                for {
                  equalArguments <-
                    if (arguments.isEmpty) Right(Nil)
                    else
                      for {
                        injective <- injectivity.get(name).toRight(MissingDefinition(name))
                        atThem <- rules.specAll(injective, arguments ++ others)
                        split <- rules.mp(atThem, sameConstructor)
                        list <- conjuncts(split, arguments.length)
                      } yield list
                  // the recursive arguments agree, so each G (y'i, u'i) is G (yi, u'i), and u'i = vi
                  recursiveEquations = specification.constructors(k).arguments.zip(equalArguments).collect {
                    case (Argument.Recursive, e) => e
                  }
                  resultEquations <- parts.tail.zip(recursiveEquations).zip(uniquenesses).zip(otherValues)
                    .foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) {
                      case (l, (((membership, argumentEquation), unique), u)) =>
                        for {
                          list <- l
                          // G (PAIR y'i u'i) to G (PAIR yi u'i)
                          hole = Term.variable("hole_", Term.typeOf(Term.destEq(argumentEquation.conclusion).get._1))
                          pairAtHole <- pairOf(hole, u)
                          template <- app(graph, pairAtHole)
                          moved <- congruence(List(hole), template, List(argumentEquation))
                          back <- Conv.sym(moved)
                          atOriginal <- LogicError.lift(Kernel.eqMp(back, membership))
                          equal <- rules.spec(u, unique).flatMap(rules.mp(_, atOriginal))
                        } yield list :+ equal
                    }
                  // w = fk ys' us' = fk xs vs
                  flippedArguments <- equalArguments.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, e) =>
                    l.flatMap(list => Conv.sym(e).map(list :+ _)))
                  holes = (others ++ otherValues).map(v => Term.variable(s"${v.name}_", v.ty))
                  template <- valueOf(k, holes.take(others.length), holes.drop(others.length))
                  moved <- congruence(holes, template, flippedArguments ++ resultEquations)
                  result <- Conv.trans(sameValue, moved)
                } yield result
              }
          } yield result
        }
        result <- opened(assumedClause, others ++ otherValues, inside)
      } yield result
    }

    private def argumentsFrom(term: Term): Either[LogicError, List[Term]] = {
      def strip(current: Term, acc: List[Term]): List[Term] = current match {
        case App(fn, argument) => strip(fn, argument :: acc)
        case _ => acc
      }
      Right(strip(term, Nil))
    }

    /** `PAIR a b = PAIR c d` gives `a = c` and `b = d`. */
    private def peelPair(carried: Carried, equation: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
      carried.tools.pairParts(equation)

    /** `h (Ck xs) = fk xs (h y0) ...`, from the graph being functional. */
    private def equationAt(
      carried: Carried,
      k: Int,
      arguments: List[FVar],
      everywhere: Kernel.Thm,
      predicate: Term,
      graph: Term,
      h: Term,
      introduce: (Int, List[Term], List[Term], List[Kernel.Thm]) => Either[LogicError, Kernel.Thm],
      pairOf: (Term, Term) => Either[LogicError, Term],
      valueOf: (Int, List[Term], List[Term]) => Either[LogicError, Term]
    ): Either[LogicError, Kernel.Thm] = {
      import carried.*
      import carried.tools.*
      val recursive = recursiveOf(k, arguments)

      /** `|- G (PAIR t (h t))` and the uniqueness at `t`, from the functional graph. */
      def valueAt(point: Term): Either[LogicError, (Kernel.Thm, Kernel.Thm, Term)] =
        for {
          atPoint <- rules.spec(point, everywhere)
          opened <- Conv.betaRoot(atPoint.conclusion)
          exactlyOne <- LogicError.lift(Kernel.eqMp(opened, atPoint))
          chosen <- tools.witness(exactlyOne)
          // chosen: (\v. G (t, v) /\ !w. ...) (select (\v. ...)), unreduced
          reduced <- Conv.betaRoot(chosen.conclusion)
          both <- LogicError.lift(Kernel.eqMp(reduced, chosen))
          member <- rules.conjElim1(both)
          unique <- rules.conjElim2(both)
          selected <- member.conclusion match {
            case App(_, App(App(_, _), v)) => Right(v)
            case other => Left(NotOfForm("G (PAIR t v)", other))
          }
        } yield (member, unique, selected)

      for {
        applied <- app(constructors(k), arguments*)
        atConstructor <- valueAt(applied)
        (_, uniqueAtConstructor, chosenAtConstructor) = atConstructor
        atChildren <- recursive.foldLeft[Either[LogicError, List[(Kernel.Thm, Kernel.Thm, Term)]]](Right(Nil))((l, child) =>
          l.flatMap(list => valueAt(child).map(list :+ _)))
        childValues = atChildren.map(_._3)
        viaEquations <- introduce(k, arguments, childValues, atChildren.map(_._1))
        value <- valueOf(k, arguments, childValues)
        // the value chosen at Ck xs is fk xs (chosen at yi)
        equal <- rules.spec(value, uniqueAtConstructor).flatMap(rules.mp(_, viaEquations))
        flipped <- Conv.sym(equal)
        // h x = select (\v. ...), by a root contraction: rewrite both sides into h form
        hAtConstructor <- app(h, applied)
        contractedAtConstructor <- Conv.betaRoot(hAtConstructor)
        hAtChildren <- recursive.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (l, child) =>
          for { list <- l; hChild <- app(h, child); contracted <- Conv.betaRoot(hChild) } yield list :+ contracted
        }
        left <- Conv.trans(contractedAtConstructor, flipped)
        holes = recursive.zipWithIndex.map { case (child, index) => Term.variable(s"hole$index", Term.typeOf(childValues(index))) }
        template <- valueOf(k, arguments, holes)
        backToH <- hAtChildren.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil))((l, e) =>
          l.flatMap(list => Conv.sym(e).map(list :+ _)))
        rewritten <- congruence(holes, template, backToH)
        result <- Conv.trans(left, rewritten)
        closed <- rules.genAll(result, arguments)
      } yield closed
    }
  }

  /* ================================================================ definitions */

  /**
   * Names a function by structural recursion. `clauses(k)` is the right-hand side for constructor
   * `k` as a function of its arguments and then of the recursive values, over the free
   * `parameters`; what comes back is the theory with `name` declared and one equation per
   * constructor, `!params args. name params (Ck args) = clause`, with the clause reduced.
   */
  def defineRecursive(
    datatype: Datatype,
    ground: Ground,
    theory: Theory,
    name: String,
    parameters: List[FVar],
    clauses: List[Term]
  ): Either[LogicError, (Theory, Term, List[Kernel.Thm])] = {
    val specification = datatype.specification
    val count = specification.constructors.length

    /** What clause `k` returns: its type with one arrow peeled per argument and per recursive value. */
    def resultOf(k: Int): Either[LogicError, Type] = {
      val arrows = specification.constructors(k).arguments.length +
        specification.constructors(k).arguments.count(_ == Argument.Recursive)
      (0 until arrows).foldLeft[Either[LogicError, Type]](Right(Term.typeOf(clauses(k)))) { (acc, _) =>
        acc.flatMap(ty => Type.destFun(ty).map(_._2).toRight(NotOfForm("a clause taking every argument", clauses(k))))
      }
    }

    for {
      _ <- if (clauses.length == count) Right(()) else Left(NotOfForm("one clause per constructor", Term.variable(name, Type.Bool)))
      result <- resultOf(0)
      _ <- (1 until count).foldLeft[Either[LogicError, Unit]](Right(())) { (acc, k) =>
        acc.flatMap(_ => resultOf(k).flatMap(other =>
          if (other == result) Right(()) else Left(NotOfForm("a clause returning what the first one returns", clauses(k)))))
      }
      // A clause with a free variable that is not a parameter is refused by `Kernel.defineConstant`
      // below, naming the variable, which is the refusal a caller needs and needs nowhere else.

      logic <- ground.classical.logic.over(theory)
      tools = Tools(ground, logic, theory, datatype.notation)
      rules = logic.rules
      general <- datatype.fact(recursion(specification.typeName))
      // The type variables of the theorem, the result's and the type's own parameters alike, are
      // read off the clauses by matching each quantifier's type against the clause it receives,
      // so a clause over `btree(num, num)` instantiates the parameters as well as the result.
      domains <- quantifierTypes(logic, general.conclusion, count)
      instantiation <- domains.zip(clauses).foldLeft[Either[LogicError, Map[String, Type]]](Right(Map.empty)) {
        case (acc, (domain, clause)) =>
          for {
            sofar <- acc
            matched <- Type.matchType(domain, Term.typeOf(clause)).toRight(NotOfForm("a clause of its constructor's shape", clause))
            merged <- matched.foldLeft[Either[LogicError, Map[String, Type]]](Right(sofar)) { case (m, (name, ty)) =>
              m.flatMap(current => current.get(name) match {
                case Some(existing) if existing != ty => Left(NotOfForm("clauses agreeing on every type variable", clause))
                case _ => Right(current + (name -> ty))
              })
            }
          } yield merged
      }
      typed = Kernel.instType(instantiation, general)
      atClauses <- rules.specAll(typed, clauses)
      predicate <- logic.destExistsPredicate(atClauses.conclusion).toRight(NotOfForm("an existential", atClauses.conclusion))
      choice <- tools.select(Term.typeOf(predicate) match {
        case TyApp("fun", List(domain, _)) => domain
        case other => other
      })
      chosen <- tools.app(choice, predicate)
      body <- LogicError.lift(Term.absAll(parameters, chosen))
      defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      (extended, definition) = defined
      wide <- ground.classical.logic.over(extended)
      wideTools = Tools(ground, wide, extended, datatype.notation)
      constant <- LogicError.lift(extended.constant(name, Term.typeOf(body)))
      applied <- wideTools.app(constant, parameters*)
      unfolded <- Conv.unfold(definition, parameters)
      witnessed <- wideTools.witness(atClauses)
      opened <- Conv.betaRoot(witnessed.conclusion)
      atChoice <- LogicError.lift(Kernel.eqMp(opened, witnessed))
      // the statement at the choice, moved onto the name
      hole = Term.variable("h_", Term.typeOf(applied))
      holePredicate <- wideTools.app(predicate, hole)
      template <- Conv.betaRoot(holePredicate).flatMap(rightOf)
      moved <- Conv.sym(unfolded).flatMap(back => wideTools.congruence(List(hole), template, List(back)))
      atName <- LogicError.lift(Kernel.eqMp(moved, atChoice))
      parts <- wideTools.conjuncts(atName, count)
      equations <- parts.zipWithIndex.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { case (acc, (part, k)) =>
        // At the instance the clauses asked for, which is not the type as declared when the
        // clauses fixed its parameters.
        val arguments = specification.constructors(k).arguments.zipWithIndex.map {
          case (Argument.Of(ty), position) => Term.variable(s"a$position", Type.substitute(instantiation, ty))
          case (Argument.Recursive, position) =>
            Term.variable(s"y$position", Type.substitute(instantiation, datatype.carrier))
        }
        for {
          list <- acc
          atArguments <- wide.rules.specAll(part, arguments)
          sides <- Term.destEq(atArguments.conclusion).toRight(NotOfForm("an equation", atArguments.conclusion))
          reduced <- Conv.betaNormalise(sides._2)
          equation <- Conv.trans(atArguments, reduced)
          closed <- wide.rules.genAll(equation, parameters ++ arguments)
        } yield list :+ closed
      }
    } yield (extended, constant, equations)
  }
}
