package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.Logic
import garden.xeno.symbolum.theories.{Chain, Real}

/**
 * What a term denotes in a model, and the two places that could quietly be wrong.
 *
 * The first is the arithmetic, and it is checked against the theory rather than against a second
 * opinion: `sub`, `div`, `le` and the numerals are evaluated by unfolding the equations the kernel
 * proved when they were introduced, so a test that they come out right is a test that the unfolding
 * works, not that somebody transcribed those definitions correctly.
 *
 * The second is the logical constants `Evaluate.LogicDefinitions` lists, which [[Evaluate]] does
 * interpret directly, and that is the one duplication in the design. It is closed here exhaustively
 * rather than by sampling: over `bool` there are four assignments to a binary connective and all
 * four are tried, so the agreement between the built-in and the definition is settled rather than
 * made likely.
 */
class EvaluateSpec extends AnyFlatSpec with Matchers {


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

  import Model.*

  private val reals = Real.standard
  private val evaluate = Evaluate.standard

  private def proposition(text: String): Term =
    reals.proposition(text).fold(error => fail(s"could not read $text: ${error.message}"), identity)

  private def at(text: String, assignment: Map[String, Value]): Option[Boolean] =
    evaluate.proposition(proposition(text), assignment)

  private val bools: Vector[Value] = Vector(Truth(false), Truth(true))

  /* ------------------------------------------------------------------- the naturals */

  private lazy val chain = Chain.standard
  private lazy val numbers = Evaluate.over(chain.reals, Model.Numbers)

  private def onNumbers(text: String, assignment: Map[String, Value]): Option[Boolean] = {
    val claim = chain.widest
      .proposition(text)
      .fold(error => fail(s"could not read $text: ${error.message}"), identity)
    numbers.proposition(claim, assignment)
  }

  "The naturals" should "be computed exactly, which is the difference from the reals here" in {
    // Two reals a millionth of an ulp apart are the same number to this evaluator, on purpose. Two
    // naturals one apart are two numbers, and a model that blurred them would make the successor
    // its own fixed point somewhere.
    val point = Map("x" -> Whole(BigInt(3)), "y" -> Whole(BigInt(5)))

    onNumbers("NUM_ADD (x:num) (y:num) = NUM_MUL (x:num) (y:num)", point) shouldBe Some(false)
    onNumbers("NUM_ADD (x:num) (y:num) = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC ZERO)))))))", point) shouldBe
      Some(true)
    onNumbers("NUM_LE (x:num) (y:num)", point) shouldBe Some(true)
    onNumbers("NUM_LT (y:num) (x:num)", point) shouldBe Some(false)
    onNumbers("real_of_num (NUM_ADD (x:num) (y:num)) = 8", point) shouldBe Some(true)
  }

  it should "be reached through the model, since their definitions cannot be unfolded" in {
    // Every constant above is **defined** rather than declared, so in principle the unfolding would
    // serve and no model would be needed. It cannot: they are defined through the recursion theorem,
    // whose body is a choice over a predicate, and choice is not something a model of this shape
    // computes. This is the measurement that says so, and it is why `Model.Numbers` is consulted
    // rather than shadowed.
    //
    // The reals' seven primitives joined the list with `docs/adr/0053`: each is defined as an
    // operation on cuts, carved by a type definition and reached by `mk_cut`, and a model of this
    // shape computes a cut no more than it computes a choice. So they are read from the model too.
    chain.reals.definitions.keySet shouldBe Set(
      "BIT0", "BIT1", "div", Real.NonStrictOrder, "sub",
      Real.Zero, Real.One, Real.Addition, Real.Multiplication, Real.Negation, Real.Inverse, Real.Order
    )
    Model.Numbers.constants.keySet should contain("NUM_ADD")
  }

  "The finite operators" should "be computed from their recurrences and stop where asked" in {
    // `Sum f n` runs from nought up to but not including `n`, which is the off-by-one to check
    // first, and this checks it against a summand whose values are known by hand.
    val squares = Mapping(
      TyApp("num", Nil),
      {
        case Whole(index) => Some(Quantity((index * index).toDouble))
        case _ => None
      }
    )
    val point = Map("f" -> squares, "n" -> Whole(BigInt(4)))

    onNumbers("Sum (f:num->real) (n:num) = 14", point) shouldBe Some(true)
    onNumbers("Prod (f:num->real) (n:num) = 0", point) shouldBe Some(true)
    onNumbers("Power 2 (n:num) = 16", Map("n" -> Whole(BigInt(4)))) shouldBe Some(true)
    onNumbers("Power 2 (n:num) = 1", Map("n" -> Whole(BigInt(0)))) shouldBe Some(true)
  }

  it should "decline past the bound rather than compute a million terms" in {
    // Not a limit of the arithmetic: a screening loop that asked for a sum of a million terms per
    // candidate would have stopped being a screen. A point past the bound is a point where the
    // question was not asked, which every caller here already knows how to skip.
    val constant = Mapping(TyApp("num", Nil), _ => Some(Quantity(1.0)))

    onNumbers("Sum (f:num->real) (n:num) = 1", Map("f" -> constant, "n" -> Whole(BigInt(Model.Terms)))) should
      not be empty
    onNumbers("Sum (f:num->real) (n:num) = 1", Map("f" -> constant, "n" -> Whole(BigInt(Model.Terms) + 1))) shouldBe
      None
    onNumbers("Power 2 (n:num) = 1", Map("n" -> Whole(BigInt(Model.Terms) + 1))) shouldBe None
  }

  it should "have nothing to say where the answer is not a number" in {
    // Two to the two thousandth overflows a `Double` and comes back as an infinity, which is not a
    // value: a caller reading one as a number would have a witness made of nothing.
    onNumbers("Power 2 (n:num) = 1", Map("n" -> Whole(BigInt(1500)))) shouldBe None
  }

  it should "decline a value of the wrong shape rather than answer about it" in {
    // The guard that makes a mistyped assignment produce no answer instead of a wrong one. Two free
    // variables called `x` at different types are distinct to the kernel and collide here, and what
    // happens then is that every operation over the value declines. The same rule now has to hold
    // for the naturals, whose operations would otherwise meet a `Quantity` where they expect a
    // `Whole`.
    def applied(name: String, argument: Value): Option[Value] =
      Model.Numbers.constants(name) match {
        case Mapping(_, apply) => apply(argument)
        case other => fail(s"$name is $other")
      }

    applied("SUC", Quantity(1.0)) shouldBe None
    applied("NUM_ADD", Quantity(1.0)) shouldBe None
    applied("real_of_num", Truth(true)) shouldBe None
    applied("Power", Whole(BigInt(2))) shouldBe None
    applied("Sum", Quantity(1.0)) shouldBe None

    // And one step in: the outer application succeeds because the first argument is right, and the
    // inner one declines.
    applied("NUM_ADD", Whole(BigInt(1))) match {
      case Some(Mapping(_, apply)) => apply(Quantity(2.0)) shouldBe None
      case other => fail(s"NUM_ADD at one is $other")
    }
  }

  "A witness" should "print as something a reader can check" in {
    // The last place a constructor name belongs. A sampled summand is a closure, and a witness
    // printed as `Mapping(num,Lambda$0x78000150e898@13cd7ea5)` is a rumour rather than a
    // counterexample.
    Model.show(Whole(BigInt(7))) shouldBe "7"
    Model.show(Quantity(1.5)) shouldBe "1.5"
    Model.show(Truth(true)) shouldBe "true"
    Model.show(Element("agent", 2)) shouldBe "agent#2"

    val summand = Mapping(
      TyApp("num", Nil),
      {
        case Whole(index) => Some(Quantity(index.toDouble))
        case _ => None
      }
    )
    Model.show(summand) shouldBe "<0.0, 1.0, 2.0, 3.0, ...>"
    Model.show(Mapping(TyApp("real", Nil), _ => None)) shouldBe "a function of real"
  }

  /* ------------------------------------------------------------------ arithmetic */

  "The intended model" should "compute with the numerals the theory defines" in {
    // Nothing here is written into the model: `12` is `BIT0 (BIT0 (BIT1 1))` and every one of those
    // bits is unfolded from its own defining equation on the way through.
    at("2 + 2 = 4", Map.empty) shouldBe Some(true)
    at("2 + 2 = 5", Map.empty) shouldBe Some(false)
    at("12 * 12 = 144", Map.empty) shouldBe Some(true)
  }

  it should "unfold the abbreviations rather than restate them" in {
    val point = Map("x" -> Quantity(2.0), "y" -> Quantity(5.0))

    at("x - y = neg 3", point) shouldBe Some(true)
    at("x / y = x * inv y", point) shouldBe Some(true)
    at("x <= y", point) shouldBe Some(true)
    at("x <= x", point) shouldBe Some(true)
    at("y <= x", point) shouldBe Some(false)
  }

  it should "have nothing to say where the theory has nothing to say" in {
    // `MUL_INVERSE` holds only under `~(x = 0)`, so a model that answered here would be claiming
    // more than the theory does. `None` is not `false`: no caller counts it as a counterexample.
    at("inv x * x = 1", Map("x" -> Quantity(2.0))) shouldBe Some(true)
    at("inv x * x = 1", Map("x" -> Quantity(0.0))) shouldBe None
  }

  it should "keep the order and the equality from contradicting each other" in {
    // Two values within the tolerance are equal, and neither is below the other. Without this the
    // model would report `x < y` and `x = y` together for values a rounding apart, and trichotomy,
    // which is `LT_TOTAL`, would be false of the very model the axioms are supposed to describe.
    val apart = Discovery.Tolerance / 10.0

    Evaluate.indistinguishable(1.0, 1.0 + apart) shouldBe true
    Evaluate.strictlyLess(1.0, 1.0 + apart) shouldBe false
    Evaluate.strictlyLess(1.0, 2.0) shouldBe true
  }

  /* ------------------------------------------------ the connectives, exhaustively */

  "Each built-in connective" should "agree with the definition the kernel holds for it" in {
    val binary = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))

    for (name <- Vector(Logic.Conjunction, Logic.Disjunction, Logic.Implication)) {
      val builtIn = value(reals.logic.theory.constant(name, binary))
      val defined = value(Right(body(name)))

      for (left <- bools; right <- bools) {
        val fromBuiltIn = applyTwice(builtIn, left, right)
        val fromDefinition = applyTwice(defined, left, right)

        withClue(s"$name at $left and $right: ") {
          fromBuiltIn shouldBe fromDefinition
          fromBuiltIn should not be None
        }
      }
    }
  }

  it should "agree with it for negation too, which takes one argument" in {
    val builtIn = value(reals.logic.theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)))
    val defined = value(Right(body(Logic.Negation)))

    for (argument <- bools) {
      withClue(s"negation at $argument: ") {
        evaluate.applyTo(builtIn, argument) shouldBe evaluate.applyTo(defined, argument)
      }
    }
  }

  it should "agree with it for the two constants" in {
    evaluate.value(body(Logic.Truth), Map.empty) shouldBe Some(Truth(true))
    evaluate.value(body(Logic.Falsity), Map.empty) shouldBe Some(Truth(false))
  }

  /* ------------------------------------------------------------------ quantifiers */

  "A quantifier" should "be decided over a finite type" in {
    at("!p:bool. p", Map.empty) shouldBe Some(false)
    at("!p:bool. p ==> p", Map.empty) shouldBe Some(true)
    at("?p:bool. p", Map.empty) shouldBe Some(true)
    at("?p:bool. p /\\ ~ p", Map.empty) shouldBe Some(false)
  }

  it should "not be decided over the reals, at any number of points" in {
    // The refusal that keeps this honest. `!x:real. p x` is not made true by a hundred points or by
    // a million, so the evaluator declines and whoever wants sampling strips the quantifier and
    // samples the variable, which is what `Refutation` does and says it does.
    at("!x:real. x + 0 = x", Map.empty) shouldBe None
    at("?x:real. x < 0", Map.empty) shouldBe None
  }

  /* ------------------------------------------------------------- a declared domain */

  "A declared type and an uninterpreted constant over it" should "evaluate under a model" in {
    // The case the whole file was built for, and the first thing in this repository to reason about
    // something that is not a number. Three agents in a cycle: each threatens the next.
    val agents = TyApp("agent", Nil)
    val relation = Type.fun(agents, Type.fun(agents, Type.Bool))

    val extended = for {
      withType <- reals.theory.declareTypeOperator("agent", 0)
      withConstant <- withType.declareConstant("threatens", relation)
      threatens <- withConstant.constant("threatens", relation)
      universal <- withConstant.constant(Logic.Universal, Logic.quantifierType(agents))
    } yield (threatens, universal)

    val (threatens, universal) =
      extended.fold(error => fail(s"could not extend the theory: ${error.message}"), identity)

    val cycle: Value = Mapping(
      agents,
      {
        case Element(_, from) =>
          Some(Mapping(agents, {
            case Element(_, to) => Some(Truth((from + 1) % 3 == to))
            case _ => None
          }))
        case _ => None
      }
    )

    val model = Model.Reals.sizing("agent", 3).interpreting("threatens", cycle)
    val over = Evaluate.over(reals, model)

    val a = Term.variable("a", agents)
    val selfThreat = for {
      body <- Term.appAll(threatens, List(a, a))
      quantified <- Term.app(universal, lam(a, body))
    } yield quantified

    val claim = selfThreat.fold(error => fail(s"could not build the term: ${error.message}"), identity)

    // Decided, not sampled: three agents is a carrier, so the quantifier is a conjunction over it.
    over.proposition(claim, Map.empty) shouldBe Some(false)

    // And the model is what decides it. Declaring the type costs nothing and says nothing, which is
    // why declaring one is conservative; every answer here came from the model, not the theory.
    val everyone = Model.Reals.sizing("agent", 3).interpreting(
      "threatens",
      Mapping(agents, _ => Some(Mapping(agents, _ => Some(Truth(true)))))
    )
    Evaluate.over(reals, everyone).proposition(claim, Map.empty) shouldBe Some(true)
  }

  it should "decide equality between two of its inhabitants" in {
    // An uninterpreted type still has an identity on it, and it is the kernel's `=` at that type
    // rather than anything a model supplies. With three inhabitants both of these are decided by
    // enumeration, which is what having a carrier buys.
    val agents = TyApp("agent", Nil)
    val model = Model.Reals.sizing("agent", 3)
    val over = Evaluate.over(reals, model)

    val extended = for {
      withType <- reals.theory.declareTypeOperator("agent", 0)
      universal <- withType.constant(Logic.Universal, Logic.quantifierType(agents))
      existential <- withType.constant(Logic.Existential, Logic.quantifierType(agents))
    } yield (universal, existential)

    val (universal, existential) =
      extended.fold(error => fail(s"could not extend the theory: ${error.message}"), identity)

    val a = Term.variable("a", agents)
    val b = Term.variable("b", agents)

    val reflexive = for {
      body <- Term.eq(a, a)
      quantified <- Term.app(universal, lam(a, body))
    } yield quantified

    // Three inhabitants, so two of them differ, and the model is what makes that true: a carrier of
    // one would make the same statement false.
    val distinct = for {
      same <- Term.eq(a, b)
      different <- reals.logic.mkNot(same)
      inner <- Term.app(existential, lam(b, different))
      outer <- Term.app(universal, lam(a, inner))
    } yield outer

    over.proposition(force(reflexive), Map.empty) shouldBe Some(true)
    over.proposition(force(distinct), Map.empty) shouldBe Some(true)
    Evaluate.over(reals, Model.Reals.sizing("agent", 1))
      .proposition(force(distinct), Map.empty) shouldBe Some(false)
  }

  it should "give nothing rather than something wrong on an assignment of the wrong type" in {
    // Nothing type-checks an assignment, so this is the guard that keeps a mistake from becoming an
    // answer. `x` is a real and the value offered is a truth value: every operation over it declines
    // rather than treating the bits as a number.
    val wrong = Map("x" -> Truth(true))

    at("x + 1 = 1 + x", wrong) shouldBe None
    at("0 < x", wrong) shouldBe None
    at("neg x = x", wrong) shouldBe None
    at("x - 1 = x", wrong) shouldBe None

    // And the other way: a truth value asked to be a number.
    at("p:bool /\\ p:bool", Map("p" -> Quantity(1.0))) shouldBe None
  }

  it should "have nothing to say when the model does not size the type" in {
    val agents = TyApp("agent", Nil)
    val unsized = Term.variable("a", agents)

    Evaluate.over(reals, Model.Reals).value(unsized, Map.empty) shouldBe None
    Evaluate.over(reals, Model.Reals).inhabitants(agents) shouldBe None
    Evaluate.over(reals, Model.Reals.sizing("agent", 2)).inhabitants(agents).map(_.length) shouldBe
      Some(2)
  }

  /* ----------------------------------------------------------------------- reading */

  /** The right-hand side of the equation the kernel proved when the constant was introduced. */
  private def body(name: String): Term = {
    val theorem = reals.logic
      .definitionOf(name)
      .fold(error => fail(s"no definition for $name: ${error.message}"), identity)

    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .getOrElse(fail(s"the definition of $name is not an equation"))
  }

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private def value(term: Either[KernelError, Term]): Value = {
    val built = term.fold(error => fail(s"could not build: ${error.message}"), identity)
    evaluate.value(built, Map.empty).getOrElse(fail(s"no value for ${reals.show(built)}"))
  }

  private def applyTwice(function: Value, left: Value, right: Value): Option[Value] =
    evaluate.applyTo(function, left).flatMap(partial => evaluate.applyTo(partial, right))
}
