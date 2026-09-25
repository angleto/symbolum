package garden.xeno.symbolum.theories

import org.scalacheck.{Gen, Shrink}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The notation, printed and read back: over generated statements, and over the ones this repository
 * has actually proved.
 *
 * `RulesPropertySpec` already runs `parse(show(t)) == t` over the logic's connectives and
 * `NumeralSpec` over the numerals. Neither reaches the notation this theory adds, which is the one
 * every axiom in `Real.scala` is read through and the one a session is shown its formalisation in.
 * `docs/evaluation.md` names that as the gap in track P; this closes it.
 *
 * == Two populations, and the second one is why this file was wrong ==
 *
 * The generator below produces statements of the **arithmetic** over `real`, which is the notation
 * whose precedences can disagree, and it is a good population for that question. It was the only
 * population here until 2026-09-12, and the sentence beside it read as though the round trip held
 * of everything this repository prints. It did not: `Product` and `Word` landed fourteen lemmas
 * over a type variable, every one of them printed `prod(a, b)` where the parser reads
 * `prod('a, 'b)`, and this file passed throughout, because no generated statement has a type
 * variable in it.
 *
 * So the second population is the real one: every statement `docs/lemmas.md` carries, read back
 * through `Chain.widest`, which is the signature it was printed with. It is not a sample and not a
 * generator, it is the document, and it fails naming the lemmas that do not read back. That is the
 * guard that catches the next development to arrive with a shape nobody's generator produces.
 *
 * == What makes this notation the hard case ==
 *
 * `-` is two operators. It is infix subtraction at the precedence of addition and prefix negation
 * at the tightest precedence there is, and the reader decides between them by position. A printer
 * that parenthesised by precedence alone would render `neg x * y` as `-x * y`, which reads back as
 * `neg (x * y)`, and no amount of testing with hand-written examples finds that reliably because
 * nobody writes the hard cases on purpose. The generator below produces `neg` and `sub` at every
 * depth for that reason.
 *
 * The second hazard is that arithmetic sits above the connectives, so `x + y = y + x` has to read
 * as an equation between sums rather than as a sum involving an equation. Every generated
 * proposition is therefore wrapped in connectives and quantifiers, which is the shape an axiom
 * actually has.
 *
 * == Why shrinking is off ==
 *
 * A counterexample here is a precedence disagreement, and precedence is a property of a term's
 * context rather than of its size. Shrinking removes exactly the context that produced the
 * disagreement and reports a smaller term that round-trips, which is a failure that reads as a
 * pass. This repository has been bitten by that once already, on a generator over source text.
 */
class NotationRoundTripSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {


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

  /**
   * Two hundred, matching `RulesPropertySpec`, and measured rather than copied.
   *
   * Each case is a print and a parse and no derivation, so the whole property ran in well under a
   * second at this count, measured no later than 2026-09-14, against the five seconds a
   * kernel-driven property cost then. The count is what makes the two-operator `-` show up: at
   * ScalaTest's default of ten, a generated statement containing both a negation and a subtraction
   * at the same depth appeared in roughly one run in three.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private implicit def noShrink[A]: Shrink[A] = Shrink.shrinkAny

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val reals = Real.standard
  private val logic = reals.logic

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val binary: Type = Type.fun(real, Type.fun(real, real))
  private val relation: Type = Type.fun(real, Type.fun(real, Type.Bool))

  private val variables: Vector[FVar] =
    Vector("x", "y", "z").map(name => Term.variable(name, real))

  private def constant(name: String, ty: Type): Term =
    force(LogicError.lift(reals.theory.constant(name, ty)))

  private def applied(name: String, ty: Type, arguments: List[Term]): Term =
    force(LogicError.lift(Term.appAll(constant(name, ty), arguments)))

  private val numerals: Gen[Term] =
    Gen.chooseNum(0, 40).map(value => force(Numeral.of(reals, BigInt(value))))

  private def quantity(depth: Int): Gen[Term] =
    if (depth <= 0) Gen.oneOf(Gen.oneOf(variables).map(v => v: Term), numerals)
    else
      Gen.frequency(
        (3, Gen.oneOf(Gen.oneOf(variables).map(v => v: Term), numerals)),
        (2, binaryOf(Real.Addition, depth)),
        // Subtraction and negation are weighted up together: they are the pair that shares the
        // symbol `-`, and a statement that carries only one of them cannot exhibit the ambiguity.
        (3, binaryOf(Real.Subtraction, depth)),
        (2, binaryOf(Real.Multiplication, depth)),
        (1, binaryOf(Real.Division, depth)),
        (3, quantity(depth - 1).map(inner => applied(Real.Negation, Type.fun(real, real), List(inner)))),
        // `inv` has no notation and prints as an application of its name, which is the other way a
        // term can be written and the one the parenthesising of arguments is about.
        (1, quantity(depth - 1).map(inner => applied(Real.Inverse, Type.fun(real, real), List(inner))))
      )

  /**
   * `!x. body`, built over this theory rather than over the logic's.
   *
   * `Logic.mkForall` looks the quantifier up in the theory the `Logic` was built from, which knows
   * the connectives and not the type operator `real`, so it refuses a quantifier over a real. The
   * connectives themselves are fine through it, because they mention nothing but `bool`. The
   * asymmetry is a property of how the theories are layered and not of this file, so the quantifier
   * is assembled here from the same two public pieces `Logic` uses.
   */
  private def forall(variable: FVar, body: Term): Term =
    force(for {
      quantifier <- LogicError.lift(
        reals.theory.constant(Logic.Universal, Logic.quantifierType(variable.ty))
      )
      result <- LogicError.lift(Term.app(quantifier, lam(variable, body)))
    } yield result)

  private def binaryOf(name: String, depth: Int): Gen[Term] =
    for {
      left <- quantity(depth - 1)
      right <- quantity(depth - 1)
    } yield applied(name, binary, List(left, right))

  /**
   * A relation between two quantities.
   *
   * Equality is built from the kernel's own constructor rather than looked up in the theory: it is
   * primitive and polymorphic, so it is not among the constants this theory declares.
   */
  private def atom(depth: Int): Gen[Term] =
    for {
      left <- quantity(depth)
      right <- quantity(depth)
      shape <- Gen.oneOf(Real.Order, Real.NonStrictOrder, Term.EqualityName)
    } yield
      if (shape == Term.EqualityName)
        force(LogicError.lift(Term.appAll(Term.equalityAt(real), List(left, right))))
      else applied(shape, relation, List(left, right))

  private def proposition(depth: Int, arithmetic: Int): Gen[Term] =
    if (depth <= 0) atom(arithmetic)
    else
      Gen.frequency(
        (4, atom(arithmetic)),
        (2, for {
          left <- proposition(depth - 1, arithmetic)
          right <- proposition(depth - 1, arithmetic)
        } yield force(logic.mkConj(left, right))),
        (2, for {
          left <- proposition(depth - 1, arithmetic)
          right <- proposition(depth - 1, arithmetic)
        } yield force(logic.mkImp(left, right))),
        (1, for {
          left <- proposition(depth - 1, arithmetic)
          right <- proposition(depth - 1, arithmetic)
        } yield force(logic.mkDisj(left, right))),
        (1, proposition(depth - 1, arithmetic).map(inner => force(logic.mkNot(inner))))
      )

  private val statements: Gen[Term] =
    for {
      body <- proposition(2, 2)
      bound <- Gen.someOf(variables)
      quantified <- Gen.oneOf(true, false)
    } yield
      if (!quantified) body
      else bound.foldRight(body)((variable, inner) => forall(variable, inner))

  /* ------------------------------------------------------------- the property */

  /**
   * The property, over the form a session is actually shown.
   *
   * Printed plainly where that reads back and annotated where it does not, which is what `Readback`
   * does and the only form anything hands to a person. Asserting it over the plain form alone would
   * be asserting something this notation cannot do: a free variable prints as a bare name, so
   * `x = y` between two reals is refused for having no type in it, and the test below pins that.
   */
  "The arithmetic notation" should "read back every statement it prints" in {
    forAll(statements) { statement =>
      val text = legible(statement)

      force(reals.proposition(text)) shouldBe statement
    }
  }

  /**
   * A term as text that reads back, which is the plain form wherever the plain form suffices.
   *
   * `Signature.legible` since 2026-09-12, where this file carried its own copy of the rule and a
   * note saying the copy was deliberate because `tactics` depends on this module. The dependency
   * argument was right and the conclusion was not: the rule belongs **below** both, on the
   * signature, and `Readback` and `Library.listing` now take it from the same place. A test
   * asserting a round trip against its own idea of which form is printed asserts nothing about the
   * form anybody is shown.
   */
  private def legible(term: Term): String =
    reals.legible(term).getOrElse(fail(s"no form of ${reals.show(term)} reads back"))

  /**
   * The same for a quantity rather than a statement, which needs one qualification.
   *
   * A term that is nothing but a free variable prints as a bare name, and a bare name does not
   * determine its own type, so the reader refuses it rather than guessing `real`. That refusal is
   * correct and is pinned below; what this property is about is every quantity that does carry an
   * operator, which is what fixes the type.
   */
  it should "read back every quantity it prints that names its own type" in {
    forAll(quantity(3).suchThat(term => !term.isInstanceOf[FVar])) { term =>
      val text = reals.show(term)

      force(reals.term(text)) shouldBe term
    }
  }

  it should "annotate a statement whose free names carry no type, and not one that needs it not" in {
    // The counterexample the property found on its first run, kept as an example. `x = y` between
    // two free reals has no type anywhere in its five characters; `x < y` does, because `<` is a
    // relation on reals and not a polymorphic one.
    val equation =
      force(LogicError.lift(Term.appAll(Term.equalityAt(real), List(variables(0), variables(1)))))
    val comparison = applied(Real.Order, relation, List(variables(0), variables(1)))

    reals.show(equation) shouldBe "x = y"
    reals.term("x = y").isLeft shouldBe true
    force(reals.proposition(legible(equation))) shouldBe equation

    legible(comparison) shouldBe "x < y"
  }

  it should "refuse a bare variable rather than guessing what type it has" in {
    // Found by the property above rather than reasoned about in advance. `x` alone is a term of
    // this theory and prints as `x`, and nothing in that text says it is a real: the reader could
    // only recover the term by assuming the type, which is the guess `TypeError` exists to refuse.
    // Every quantity with an operator in it is determined by the operator.
    reals.term(reals.show(variables(0))) match {
      case Left(TypeError(_)) => succeed
      case Left(other) => fail(s"expected a type error, got $other")
      case Right(term) => fail(s"expected a refusal, got $term")
    }

    force(reals.term(reals.show(applied(Real.Negation, Type.fun(real, real), List(variables(0)))))) shouldBe
      applied(Real.Negation, Type.fun(real, real), List(variables(0)))
  }

  /* ------------------------------------------- the two cases the generator is for */

  it should "keep a negated factor apart from a negated product" in {
    // The witness for the `-` ambiguity, written out, so that a reader of this file can see the
    // shape the property is looking for rather than trusting that it appears.
    val x = variables(0)
    val y = variables(1)
    val negatedFactor =
      applied(
        Real.Multiplication,
        binary,
        List(applied(Real.Negation, Type.fun(real, real), List(x)), y)
      )
    val negatedProduct =
      applied(
        Real.Negation,
        Type.fun(real, real),
        List(applied(Real.Multiplication, binary, List(x, y)))
      )

    reals.show(negatedFactor) should not be reals.show(negatedProduct)
    force(reals.term(reals.show(negatedFactor))) shouldBe negatedFactor
    force(reals.term(reals.show(negatedProduct))) shouldBe negatedProduct
  }

  /* --------------------------------------------- the population the document actually carries */

  /**
   * The chain, for the second population only.
   *
   * Everything above is over `Real.standard`, which is the development whose notation the generator
   * is about. The document is printed through `Chain.widest`, which is a different and wider
   * signature, and reading its statements back through anything else would be asking a question
   * nobody's output answers.
   */
  private lazy val chain = Chain.standard
  private lazy val library = Library.of(chain)

  /**
   * Each generated line of `docs/lemmas.md`, as the name it carries and the statement beside it.
   *
   * Read off the document rather than regenerated, because the document is what a reader copies a
   * line out of. `LibrarySpec` is what asserts the document is what the command produces; this
   * asserts that what it holds can be read back, and the two together are the guarantee.
   */
  private def documented(): Vector[(String, String)] = {
    val file = new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(Lemmas.Document)),
      "UTF-8"
    )

    Lemmas
      .generatedPartOf(file)
      .fold(why => fail(why), identity)
      .linesIterator
      .toVector
      .filter(_.startsWith("  "))
      .map { line =>
        val trimmed = line.trim
        val split = trimmed.indexOf(' ')
        (trimmed.substring(0, split), trimmed.substring(split).trim)
      }
  }

  "Every statement in docs/lemmas.md" should "read back as the theorem it was printed from" in {
    // The repair the card asked for, and the population it asked for: all of them, not a
    // sample. Fourteen failed when this was first run, which is what a generator over `real` and
    // `num` could not have found: `Product` and `Word` print a type variable and nothing else here
    // does.
    //
    // Asserted through `term` rather than `proposition` because a definitional entry is an equation
    // between two functions and is not a proposition, and a document that listed only the
    // propositions would be a document with holes in it.
    val statements = documented()

    // The population, named, so that a reader of a green run knows what was interrogated. It is the
    // document's own lines and not the library's entries; the two agree because `LibrarySpec` says
    // so, and this test does not assume it.
    statements.size shouldBe library.entries.size

    val unreadable = statements
      .filterNot { case (_, statement) => statement.startsWith(Library.NotReadable) }
      .filterNot { case (_, statement) =>
        chain.widest.term(statement).exists(read => chain.widest.legible(read).contains(statement))
      }
      .map(_._1)

    withClue(s"listed in ${Lemmas.Document} and not readable back: ${unreadable.mkString(", ")}\n") {
      unreadable shouldBe empty
    }
  }

  it should "be readable at all, so that none of them needs the marker" in {
    // The other half, and it is a different claim. The test above says a line that does not carry
    // the marker reads back; this says no line carries it. Today nothing in the library is in that
    // state, and a lemma that ends up in it is a printing defect to repair rather than a line to
    // file away.
    val marked = documented().collect {
      case (name, statement) if statement.startsWith(Library.NotReadable) => name
    }

    withClue(s"printed with ${Library.NotReadable}: ${marked.mkString(", ")}\n") {
      marked shouldBe empty
    }
  }

  it should "read back a polymorphic statement through the quote the parser asks for" in {
    // The witness, written out, so that a reader of this file sees the shape the assertion above is
    // looking for. `FST_PAIR` is over `'a` and `'b`, and the printer wrote them without their
    // quotes until 2026-09-12, which made a document of 186 lines carry fourteen nobody could read.
    val statement = chain.product.facts(Product.FirstOfPair).conclusion

    chain.widest.show(statement) shouldBe "!x:'a. !y:'b. FST (PAIR x y) = x"
    chain.widest.legible(statement) shouldBe Some("!x:'a. !y:'b. FST (PAIR x y) = x")
    force(chain.widest.term(chain.widest.show(statement))) shouldBe statement
  }

  it should "keep a subtraction apart from a sum with a negation" in {
    val x = variables(0)
    val y = variables(1)
    val subtracted = applied(Real.Subtraction, binary, List(x, y))
    val added =
      applied(
        Real.Addition,
        binary,
        List(x, applied(Real.Negation, Type.fun(real, real), List(y)))
      )

    force(reals.term(reals.show(subtracted))) shouldBe subtracted
    force(reals.term(reals.show(added))) shouldBe added
    subtracted should not be added
  }
}
