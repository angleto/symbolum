package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Two-by-two matrices over the reals, as a pair of pairs, with the multiplicativity of the
 * determinant.
 *
 * The third consumer of `Product` and the one the pair was listed for. The gap audit that asked for
 * `prod` named *"matrices, vectors, finite index types"* in one breath and traced all three to the
 * same absence: a matrix is a function on a pair of indices, or equivalently a pair of rows, and
 * neither is a term until a pair is. `Word` took the first half of that list on 2026-09-11 and this
 * takes the second.
 *
 * == Why there is no `defineType` here, and that is the decision rather than the shortcut ==
 *
 * `num`, `prod` and `word` are all carved out of a larger type by a predicate, because in each case
 * the larger type holds things that are not what is wanted: an inductive subset inside an infinite
 * type, the one-point functions inside `'a -> 'b -> bool`, the padded encodings inside
 * `prod(num, num -> 'a)`. **A 2x2 matrix has no such predicate.** Every element of
 * `prod(prod(real,real), prod(real,real))` is a 2x2 matrix and every 2x2 matrix is one of them, so
 * a fourth use of `Kernel.defineType` would carve out the whole of the type it was given. What it
 * would buy is a name in the type language and a distinct equality; what it would cost is a
 * bijection to cross in every one of the twenty-four derivations below, and `Word` is the measured
 * example of what that costs: its cheapest fact is 1214 inferences, of which the bijection is most.
 * The trade would be worth making for a type whose equality has to be coarser than its encoding's,
 * which is exactly the argument `Word` makes and exactly the argument that does not apply here.
 *
 * So the matrix type is `prod(prod(real,real), prod(real,real))` spelled out, [[Matrix.Matrices]],
 * and [[Matrix.Constructor]] is a **defined constant** rather than an abstraction function. The
 * consequence a reader should know: a matrix and a pair of pairs are the same thing here, and
 * nothing stops a caller writing `FST (FST m)` where `MAT_E11 m` was meant. They are equal, so
 * nothing goes wrong; what is lost is the refusal that would have told the caller they had left the
 * development's vocabulary. `MatrixSpec` pins that they are equal, so the cost of the decision is
 * visible rather than implied.
 *
 * == What is proved, and the one that justifies the rest ==
 *
 * `|- !x y. MAT_DET (MAT_MUL x y) = MAT_DET x * MAT_DET y`. It is the statement this repository
 * cites for what a numerical library cannot hand anybody: a floating-point determinant of a product
 * agrees with the product of the determinants to within a rounding error that nothing reports, and
 * the identity that is being appealed to is not the thing computed. Here it is a theorem, and
 * `MatrixSpec` reads back what it rests on rather than describing it.
 *
 * Around it: the constructor and its four accessors with their characterising laws, addition,
 * scalar multiplication, multiplication, the identity and the transpose, each in constructor form;
 * then commutativity and associativity of addition, associativity of multiplication, both
 * distributive laws, the identity on both sides, the transpose of a product and of a transpose, and
 * the determinant of the identity, of a transpose and of a scalar multiple.
 *
 * == How they are proved: one driver, and it is mostly `Ring` ==
 *
 * [[Matrix.prove]] is the whole of the automation and it is four steps. A matrix variable is
 * replaced by `MAT2` of four **fresh real variables**; the rules of [[Matrix.Unfolding]] reduce
 * every operation to the constructor applied to four real terms; the four component equations go to
 * `Ring`; and the variables are put back by [[Matrix.Surjective]] read right to left. Nothing about
 * matrices is decided anywhere in it. That is the point rather than an economy: once the
 * definitions are unfolded, every law here **is** a ring identity in eight variables, and a
 * development that proved them some other way would be proving them twice.
 *
 * `Ring` takes the determinant goal without complaint, which was the open question when this was
 * planned. Expanded it is
 * `(a*e + b*g) * (c*f + d*h) - (a*f + b*h) * (c*e + d*g) = (a*d - b*c) * (e*h - f*g)`, eight
 * variables and sixteen monomials before cancellation, and [[Polynomial]]'s collecting normal form
 * settles it; the inference count is in `MatrixSpec` and in the report below.
 *
 * **The driver refuses in three distinguishable ways and they are not merged.** A side that the
 * rules do not reduce to the constructor is `NotOfForm` naming the term it stopped at; a component
 * the ring cannot settle when the rules have **not** reached a fixed point is `NotNormalised`, which
 * says the rewriting ran out rather than that the identity is false; a component the ring cannot
 * settle when they **have** is the ring's own refusal, passed through. That is the distinction
 * `Induct.afterRewriting` makes for the same reason, and card 5f0cd494 is the finding behind it: a
 * rewriter that stopped early and a false identity are the same `Left` otherwise, and a caller told
 * the second goes and checks mathematics that was never the problem.
 *
 * == What is not here, with the measurement rather than the intention ==
 *
 * **No 3x3 and no n x n.** The question was asked with a number rather than a preference.
 * `MAT_DET_MUL` at 2x2 is one call to `Ring` on an identity in 8 variables whose two sides expand
 * to 8 monomials each, and the derivation is of the size `MatrixSpec` prints. At 3x3 the same
 * identity is an equation in 18 variables whose expansion is **6 x 6 x 6 = 216 monomials before
 * cancellation** on the left against 36 on the right, and the normal form `Polynomial` builds is
 * sorted, so the cost is superlinear in the monomial count rather than linear. The measured ratio
 * on the ladder in `Ring`'s own docstring is that `(x + 1)^12` reaches 507 nodes where a twelvefold
 * expansion reaches 98305; the honest reading of that is that 3x3 is **not** a small multiple of
 * this file and might not terminate inside `Rewrite.DefaultLimit` at all. `MatrixSpec` prints the
 * 2x2 figure so that anybody proposing 3x3 starts from a number.
 *
 * And the size is the smaller half of it. A general `n x n` determinant is a sum over permutations,
 * which needs a type of permutations, a sign, and an induction over a finite index set: three
 * developments that do not exist, and `Word` is the nearest thing to the first of them. The path is
 * real and it is not one file.
 *
 * **No inverse and no `MAT_DET_NOT_ZERO ==> ...`.** An inverse is `MAT_SMUL (inv (MAT_DET x))` of
 * the adjugate, so the term is writable today; what it needs is the non-vanishing side condition
 * carried through every law, which is `Field`'s business rather than `Ring`'s and is a second
 * development. Consumers counted: zero.
 *
 * **No proof that multiplication does not commute.** It does not, and the counterexample is small
 * (`MAT2 0 1 0 0` against `MAT2 0 0 1 0`), but it is a **refutation** rather than an identity, so
 * the driver above cannot reach it: it would take [[Matrix.Injective]], the numeral fact
 * `~(1 = 0)`, and a negation introduction. `MatrixSpec` asserts that no `MAT_MUL_SYM` is in the
 * library and names the library it asked, because "absent from this development" and "absent from
 * the system" are two claims and the second one went wrong here once already, in `WordSpec` on
 * 2026-09-11.
 */
final class Matrix private (
  val ring: Ring,
  val product: Product,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm],
  private val unfolding: Matrix.Unfolding
) extends Signature {

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /**
   * Prove an equation about matrices, or say which of the three things it could not do.
   *
   * The driver the eighteen facts below the characterisation are proved with, exported because a
   * consumer stating its own matrix identity wants it and because a procedure only its own file can
   * call is a procedure nobody can check against a new example. See the class comment for the four
   * steps and for the three refusals.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] = Matrix.establish(unfolding, goal)

  /** The same, on a statement written in this development's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] = proposition(text).flatMap(prove)
}

object Matrix {

  /* ------------------------------------------------------------------ the names */

  /**
   * The constructor, named for the dimension it is about.
   *
   * `MAT2` rather than `MAT`, so that the one thing this development does not cover is in the name
   * of every statement it proves. A 3x3 development would define `MAT3` and would not have to
   * rename this one, which is the whole of the reason; `docs/naming.md` allows digits in a name and
   * `Natural`'s `IND_0` is the precedent.
   */
  val Constructor: String = "MAT2"

  /** The four entries, row first: `MAT_E12` is row one, column two. */
  val Entry11: String = "MAT_E11"
  val Entry12: String = "MAT_E12"
  val Entry21: String = "MAT_E21"
  val Entry22: String = "MAT_E22"

  /** The operations. `MAT_SMUL` is multiplication by a real, which is not `MAT_MUL`. */
  val Add: String = "MAT_ADD"
  val ScalarMul: String = "MAT_SMUL"
  val Mul: String = "MAT_MUL"
  val Identity: String = "MAT_ID"
  val Transpose: String = "MAT_TRANSPOSE"
  val Determinant: String = "MAT_DET"

  /** `|- !a b c d. MAT_E11 (MAT2 a b c d) = a`, and the three like it. */
  val Entry11OfConstructor: String = "MAT_E11_MAT2"
  val Entry12OfConstructor: String = "MAT_E12_MAT2"
  val Entry21OfConstructor: String = "MAT_E21_MAT2"
  val Entry22OfConstructor: String = "MAT_E22_MAT2"

  /**
   * `|- !m. m = MAT2 (MAT_E11 m) (MAT_E12 m) (MAT_E21 m) (MAT_E22 m)`.
   *
   * Spelled `SURJECTIVE` and stated in this direction because `Product.Surjective` is, and
   * `docs/naming.md` forbids a second spelling of a concept the corpus already spells one way. Read
   * **right to left** it is the rule that puts a matrix variable back after the driver has taken it
   * apart, and that direction is built inside [[construct]] rather than exported: as a rewrite rule
   * the direction written here does not terminate.
   */
  val Surjective: String = "MAT2_SURJECTIVE"

  /**
   * `|- !a b c d e f g h. (MAT2 a b c d = MAT2 e f g h) = (a = e /\ b = f /\ c = g /\ d = h)`.
   *
   * Derived from the four accessor laws and nothing else, in the obvious way: apply each accessor
   * to the assumed equation. So it adds no content, and it is stated anyway because it is what a
   * consumer rewrites with to turn one equation between matrices into four between reals. It has
   * **no consumer inside this file** and that is written here rather than discovered: the driver
   * rebuilds by congruence instead, which needs no lemma at all.
   */
  val Injective: String = "MAT2_INJECTIVE"

  /** Each operation, applied to constructors, in constructor form. */
  val AddOfConstructors: String = "MAT_ADD_MAT2"
  val ScalarMulOfConstructor: String = "MAT_SMUL_MAT2"
  val MulOfConstructors: String = "MAT_MUL_MAT2"
  val TransposeOfConstructor: String = "MAT_TRANSPOSE_MAT2"
  val DeterminantOfConstructor: String = "MAT_DET_MAT2"

  /** The laws of addition. */
  val AddSym: String = "MAT_ADD_SYM"
  val AddAssoc: String = "MAT_ADD_ASSOC"

  /**
   * The laws of multiplication, and the two distributive laws are two laws.
   *
   * Matrix multiplication does not commute, so `x * (y + z)` and `(x + y) * z` are not each other
   * read backwards and neither follows from the other. Spelling the side out in the name is what
   * stops a reader taking one of them for both.
   */
  val MulAssoc: String = "MAT_MUL_ASSOC"
  val MulDistributeLeft: String = "MAT_MUL_DISTRIBUTE_LEFT"
  val MulDistributeRight: String = "MAT_MUL_DISTRIBUTE_RIGHT"
  val MulIdentityLeft: String = "MAT_MUL_ID_LEFT"
  val MulIdentityRight: String = "MAT_MUL_ID_RIGHT"

  /** The transpose is an involution, and it reverses a product. */
  val TransposeTranspose: String = "MAT_TRANSPOSE_TRANSPOSE"
  val TransposeMul: String = "MAT_TRANSPOSE_MUL"

  /** The determinant: of the identity, of a transpose, of a scalar multiple, and of a product. */
  val DeterminantIdentity: String = "MAT_DET_ID"
  val DeterminantTranspose: String = "MAT_DET_TRANSPOSE"
  val DeterminantScalarMul: String = "MAT_DET_SMUL"

  /** `|- !x y. MAT_DET (MAT_MUL x y) = MAT_DET x * MAT_DET y`, which is what the rest is for. */
  val DeterminantMul: String = "MAT_DET_MUL"

  /* ------------------------------------------------------------------ the types */

  /** `real`. */
  val Values: Type = TyApp(Real.TypeName, Nil)

  /** `prod(real,real)`, a row. */
  val Rows: Type = TyApp(Product.TypeName, List(Values, Values))

  /** `prod(prod(real,real),prod(real,real))`, which is what a 2x2 matrix is here. */
  val Matrices: Type = TyApp(Product.TypeName, List(Rows, Rows))

  /** The same, as the parser reads it, so that an annotation in a definition is written once. */
  val MatrixText: String = "prod(prod(real,real),prod(real,real))"

  /* -------------------------------------------------------------- the definitions */

  /**
   * The bodies of the eleven definitions, as text, in the order they are introduced.
   *
   * Each one is a **definition** and costs no axiom, which is the claim `ChainSpec` checks by
   * counting the theory's axioms at this stage rather than by reading this sentence.
   */
  val Definitions: Vector[(String, String)] = Vector(
    Constructor -> "\\a:real. \\b:real. \\c:real. \\d:real. PAIR (PAIR a b) (PAIR c d)",
    Entry11 -> s"\\m:$MatrixText. FST (FST m)",
    Entry12 -> s"\\m:$MatrixText. SND (FST m)",
    Entry21 -> s"\\m:$MatrixText. FST (SND m)",
    Entry22 -> s"\\m:$MatrixText. SND (SND m)",
    Add -> s"\\m:$MatrixText. \\n:$MatrixText. MAT2 (MAT_E11 m + MAT_E11 n) (MAT_E12 m + MAT_E12 n) (MAT_E21 m + MAT_E21 n) (MAT_E22 m + MAT_E22 n)",
    ScalarMul -> s"\\k:real. \\m:$MatrixText. MAT2 (k * MAT_E11 m) (k * MAT_E12 m) (k * MAT_E21 m) (k * MAT_E22 m)",
    Mul -> s"\\m:$MatrixText. \\n:$MatrixText. MAT2 (MAT_E11 m * MAT_E11 n + MAT_E12 m * MAT_E21 n) (MAT_E11 m * MAT_E12 n + MAT_E12 m * MAT_E22 n) (MAT_E21 m * MAT_E11 n + MAT_E22 m * MAT_E21 n) (MAT_E21 m * MAT_E12 n + MAT_E22 m * MAT_E22 n)",
    Identity -> "MAT2 1 0 0 1",
    Transpose -> s"\\m:$MatrixText. MAT2 (MAT_E11 m) (MAT_E21 m) (MAT_E12 m) (MAT_E22 m)",
    Determinant -> s"\\m:$MatrixText. MAT_E11 m * MAT_E22 m - MAT_E12 m * MAT_E21 m"
  )

  /**
   * What every derived fact says, as text, in the order they are derived.
   *
   * The device `Product.Statements` and `Word.Statements` use and for the same stated purpose: the
   * kernel checked that each is a theorem, and what is unchecked is that the derivation **arrived
   * at the statement intended**. [[construct]] parses each of these and compares, so a proof that
   * reaches a true theorem about the wrong matrices fails the build rather than being handed out.
   *
   * Compared as terms rather than as printed text. Nothing here is polymorphic, so these would read
   * back either way; comparing the parse is the stronger check and costs the same.
   */
  val Statements: Vector[(String, String)] = Vector(
    Entry11OfConstructor -> "!a:real. !b:real. !c:real. !d:real. MAT_E11 (MAT2 a b c d) = a",
    Entry12OfConstructor -> "!a:real. !b:real. !c:real. !d:real. MAT_E12 (MAT2 a b c d) = b",
    Entry21OfConstructor -> "!a:real. !b:real. !c:real. !d:real. MAT_E21 (MAT2 a b c d) = c",
    Entry22OfConstructor -> "!a:real. !b:real. !c:real. !d:real. MAT_E22 (MAT2 a b c d) = d",
    Surjective ->
      s"!m:$MatrixText. m = MAT2 (MAT_E11 m) (MAT_E12 m) (MAT_E21 m) (MAT_E22 m)",
    Injective ->
      ("!a:real. !b:real. !c:real. !d:real. !e:real. !f:real. !g:real. !h:real. " +
        "(MAT2 a b c d = MAT2 e f g h) = (a = e /\\ b = f /\\ c = g /\\ d = h)"),
    AddOfConstructors ->
      ("!a:real. !b:real. !c:real. !d:real. !e:real. !f:real. !g:real. !h:real. " +
        "MAT_ADD (MAT2 a b c d) (MAT2 e f g h) = MAT2 (a + e) (b + f) (c + g) (d + h)"),
    ScalarMulOfConstructor ->
      ("!k:real. !a:real. !b:real. !c:real. !d:real. " +
        "MAT_SMUL k (MAT2 a b c d) = MAT2 (k * a) (k * b) (k * c) (k * d)"),
    MulOfConstructors ->
      ("!a:real. !b:real. !c:real. !d:real. !e:real. !f:real. !g:real. !h:real. " +
        "MAT_MUL (MAT2 a b c d) (MAT2 e f g h) = " +
        "MAT2 (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h)"),
    TransposeOfConstructor ->
      "!a:real. !b:real. !c:real. !d:real. MAT_TRANSPOSE (MAT2 a b c d) = MAT2 a c b d",
    DeterminantOfConstructor ->
      "!a:real. !b:real. !c:real. !d:real. MAT_DET (MAT2 a b c d) = a * d - b * c",
    AddSym -> s"!x:$MatrixText. !y:$MatrixText. MAT_ADD x y = MAT_ADD y x",
    AddAssoc ->
      (s"!x:$MatrixText. !y:$MatrixText. !z:$MatrixText. " +
        "MAT_ADD (MAT_ADD x y) z = MAT_ADD x (MAT_ADD y z)"),
    MulAssoc ->
      (s"!x:$MatrixText. !y:$MatrixText. !z:$MatrixText. " +
        "MAT_MUL (MAT_MUL x y) z = MAT_MUL x (MAT_MUL y z)"),
    MulDistributeLeft ->
      (s"!x:$MatrixText. !y:$MatrixText. !z:$MatrixText. " +
        "MAT_MUL x (MAT_ADD y z) = MAT_ADD (MAT_MUL x y) (MAT_MUL x z)"),
    MulDistributeRight ->
      (s"!x:$MatrixText. !y:$MatrixText. !z:$MatrixText. " +
        "MAT_MUL (MAT_ADD x y) z = MAT_ADD (MAT_MUL x z) (MAT_MUL y z)"),
    MulIdentityLeft -> s"!x:$MatrixText. MAT_MUL MAT_ID x = x",
    MulIdentityRight -> s"!x:$MatrixText. MAT_MUL x MAT_ID = x",
    TransposeTranspose -> s"!x:$MatrixText. MAT_TRANSPOSE (MAT_TRANSPOSE x) = x",
    TransposeMul ->
      (s"!x:$MatrixText. !y:$MatrixText. " +
        "MAT_TRANSPOSE (MAT_MUL x y) = MAT_MUL (MAT_TRANSPOSE y) (MAT_TRANSPOSE x)"),
    DeterminantIdentity -> "MAT_DET MAT_ID = 1",
    DeterminantTranspose -> s"!x:$MatrixText. MAT_DET (MAT_TRANSPOSE x) = MAT_DET x",
    DeterminantScalarMul ->
      s"!k:real. !x:$MatrixText. MAT_DET (MAT_SMUL k x) = k * k * MAT_DET x",
    DeterminantMul ->
      s"!x:$MatrixText. !y:$MatrixText. MAT_DET (MAT_MUL x y) = MAT_DET x * MAT_DET y"
  )

  /**
   * The six derived by hand, in the order [[construct]] builds them.
   *
   * Named rather than taken as a prefix of [[Statements]], which is what this was: `take(6)` and
   * `drop(6)` are a coupling to the order of a list somebody will reorder, and the failure would be
   * a development handing out a lemma under the wrong name.
   */
  private val ByHand: Vector[String] = Vector(
    Entry11OfConstructor,
    Entry12OfConstructor,
    Entry21OfConstructor,
    Entry22OfConstructor,
    Surjective,
    Injective
  )

  /** Everything else, each proved by the driver. */
  private val Driven: Vector[String] = Statements.map(_._1).filterNot(ByHand.contains)

  /**
   * The standard development, which is the chain's.
   *
   * Unlike `Word.standard` this does **not** build a second copy beside the chain, and the
   * difference is a decision taken on the evidence of that one. A second copy exists there so that
   * `WordSpec` can measure what the words cost over a base with nothing else in it; the same
   * question here is answered by `Derivation.axiomsOf` on each fact, which reads the derivation
   * rather than the base, so a second copy would cost a second `Product` and a second `prod` type
   * operator and answer nothing the first cannot.
   */
  lazy val standard: Matrix = Chain.standard.matrix

  /**
   * The development over a ring, a product and a theory that already holds both.
   *
   * The chain entry point and the only one. `base` is the widest theory the chain has assembled,
   * not `product.theory`: the decision of 2026-09-12 is that a development goes **in** the chain,
   * and the three arguments are what this needs rather than a choice about where it sits. The
   * product has to be the one over `base` or the `PAIR` in the definitions is a different constant
   * from the one the facts are about, which `docs/adr/0008` is the record of and which shows up as
   * a rewrite rule that silently never fires.
   *
   * The ring is the one `base` was built from and is used unchanged: a theorem of a theory is a
   * theorem of every extension of it, and every component equation below is settled by it.
   */
  def construct(ring: Ring, product: Product, base: Theory): Either[LogicError, Matrix] = {
    val notation = product.notation

    def define(
      theory: Theory,
      name: String,
      text: String
    ): Either[LogicError, (Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, notation, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    def defineAll(
      start: Theory
    ): Either[LogicError, (Theory, Map[String, Kernel.Thm])] =
      Definitions.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
        Right((start, Map.empty))
      ) { (acc, entry) =>
        val (name, text) = entry
        for {
          state <- acc
          (theory, made) = state
          defined <- define(theory, name, text)
        } yield (defined._1, made.updated(name, defined._2))
      }

    for {
      built <- defineAll(base)
      (theory, definitions) = built
      logic <- product.classical.logic.over(theory)

      // The two type instances of the pair's own facts. `Matching` is a term matcher and does not
      // instantiate a type variable, so a polymorphic lemma used as a rewrite rule against a
      // concrete term matches nothing at all and fails silently by not firing. Instantiating here
      // is the workaround and not a repair: the general defect is somebody else's, and this
      // development never meets it because everything it states is monomorphic.
      firstOfPair <- product.fact(Product.FirstOfPair)
      secondOfPair <- product.fact(Product.SecondOfPair)
      surjectivePair <- product.fact(Product.Surjective)
      inside = Map(Classical.TypeVariable -> Values, Classical.CodomainVariable -> Values)
      outside = Map(Classical.TypeVariable -> Rows, Classical.CodomainVariable -> Rows)

      crossing <- Rewrite.Rule.all(
        logic,
        Vector(
          Kernel.instType(inside, firstOfPair),
          Kernel.instType(outside, firstOfPair),
          Kernel.instType(inside, secondOfPair),
          Kernel.instType(outside, secondOfPair)
        ) ++ Vector(Constructor, Entry11, Entry12, Entry21, Entry22).map(definitions)
      )

      constructor <- LogicError.lift(theory.constant(Constructor, constructorType))

      entries <- accessorLaws(logic, theory, crossing, constructor)
      folded <- folding(
        logic,
        theory,
        crossing,
        constructor,
        Kernel.instType(inside, surjectivePair),
        Kernel.instType(outside, surjectivePair)
      )
      surjective <- surjectiveConstructor(logic, folded)
      injective <- injectiveConstructor(logic, theory, constructor, entries)

      entryRules <- Rewrite.Rule.all(
        logic,
        entries ++ Vector(Add, ScalarMul, Mul, Identity, Transpose, Determinant).map(definitions)
      )
      foldingRule <- Rewrite.Rule.of(logic, folded)
      unfolding = Unfolding(logic, ring, theory, constructor, entryRules, foldingRule)

      byHand = ByHand.zip(entries :+ surjective :+ injective).toMap
      said = Statements.toMap
      driven <- Driven.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
        (acc, name) =>
          for {
            proved <- acc
            text <- said.get(name).toRight(MissingDefinition(name))
            goal <- Parser.proposition(theory, notation, text)
            theorem <- establish(unfolding, goal)
          } yield proved.updated(name, theorem)
      }
      facts = byHand ++ driven

      // Each statement checked against the text a person reads it by, here rather than in the
      // spec: a development that built something other than what it says it built must not be
      // handed out at all, which is how `Product` and `Word` both end.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Matrix(ring, product, theory, notation, logic, definitions, facts, unfolding)
  }

  /* --------------------------------------------------------------- the driver */

  /**
   * What [[establish]] works with: the rules that take an operation apart and the one that puts a
   * matrix variable back.
   *
   * Held together rather than passed as five arguments because the five are one thing: a rule set
   * whose fixed point is the constructor applied to four real terms, plus its inverse. Splitting
   * them at a call site is how one of them comes to be built from a different theory than the
   * others, which `docs/adr/0008` makes loud and which is still a bad afternoon.
   */
  private[theories] final case class Unfolding(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    constructor: Term,
    entries: Vector[Rewrite.Rule],
    folding: Rewrite.Rule
  ) {

    /** One of the four accessors, as a term of this theory. */
    def accessor(name: String): Either[LogicError, Term] =
      LogicError.lift(theory.constant(name, Type.fun(Matrices, Values)))
  }

  /**
   * Prove an equation about matrices by proving it about their entries.
   *
   * The four steps the class comment names. What is worth saying here is why the entries are
   * **fresh variables** rather than `MAT_E11 x` applied to the original: `Ring` normalises a
   * polynomial in whatever its atoms are, and `MAT_E11 x` is a perfectly good atom, so both work.
   * The fresh variables are chosen because the goal handed to `Ring` is then an identity in eight
   * letters that a reader can check by hand, and because a refusal reports that identity rather
   * than one wearing four accessor applications per term.
   */
  private[theories] def establish(
    unfolding: Unfolding,
    goal: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      (bound, body) = stripped
      free = Term.freeVariables(body)
      subjects = free.toVector.filter(_.ty == Matrices).sortBy(_.name)
      opened <- expansion(unfolding, subjects, free)
      (expand, restore) = opened

      substituted <- LogicError.lift(Term.substitute(expand, body))
      proved <- close(unfolding, substituted)

      back <- LogicError.lift(Kernel.inst(restore, proved))
      folded <- Rewrite.inTheorem(Vector(unfolding.folding), back)
      // `NotOfForm` and not `NotEqualTo`, which is what this was until `LogicError.Standing`
      // existed. `NotEqualTo` is raised where two sides reached a fixed point of one conversion and
      // differ, which decides the identity; here it is the theorem this method assembled failing to
      // be the goal it was asked for, which decides nothing and is a defect above the kernel.
      // `Linarith.prove` has the same check and has always spelt it this way.
      _ <-
        if (folded.conclusion == body) Right(())
        else Left(NotOfForm("the goal as stated", folded.conclusion))

      result <- unfolding.logic.rules.genAll(folded, bound.toList)
    } yield result

  /**
   * A matrix variable to its four entries, and the way back.
   *
   * Two maps rather than one because they run in opposite directions and at different times: the
   * first is a substitution into a **term** before anything is proved, the second an
   * instantiation of a **theorem** after. A single map would have to be inverted, and inverting a
   * substitution is only possible because this one happens to be injective, which is a property
   * nobody should have to notice.
   */
  private def expansion(
    unfolding: Unfolding,
    subjects: Vector[FVar],
    taken: Set[FVar]
  ): Either[LogicError, (Map[FVar, Term], Map[FVar, Term])] =
    subjects.foldLeft[Either[LogicError, (Map[FVar, Term], Map[FVar, Term], Set[FVar])]](
      Right((Map.empty, Map.empty, taken))
    ) { (acc, subject) =>
      for {
        state <- acc
        (expand, restore, used) = state

        fresh = Vector(Entry11 -> "11", Entry12 -> "12", Entry21 -> "21", Entry22 -> "22")
          .foldLeft((Vector.empty[(String, FVar)], used)) { case ((made, avoid), (name, suffix)) =>
            val variable = Conv.freshVariable(subject.name + suffix, Values, avoid)
            (made :+ (name -> variable), avoid + variable)
          }
        (named, nowUsed) = fresh

        constructed <- LogicError.lift(
          Term.appAll(unfolding.constructor, named.map(_._2).toList)
        )
        projections <- named.foldLeft[Either[LogicError, Map[FVar, Term]]](Right(restore)) {
          (soFar, entry) =>
            val (name, variable) = entry
            for {
              made <- soFar
              accessor <- unfolding.accessor(name)
              applied <- LogicError.lift(Term.app(accessor, subject))
            } yield made.updated(variable, applied)
        }
      } yield (expand.updated(subject, constructed), projections, nowUsed)
    }.map { case (expand, restore, _) => (expand, restore) }

  /**
   * The equation with no matrix variable left in it, settled.
   *
   * Two cases and they are different questions rather than two paths to one. An equation between
   * **reals** is what `Ring` decides, and `Induct.afterRewriting` is exactly the rewrite-then-close
   * shape with the exhausted-rewriter diagnostic already in it. An equation between **matrices** is
   * not a ring identity at all: the ring has never heard of `prod`, and handing it one would get a
   * refusal about a term rather than about the mathematics. So that side is taken apart into four
   * real equations first, and the four are what `Ring` sees.
   */
  private def close(unfolding: Unfolding, statement: Term): Either[LogicError, Kernel.Thm] =
    Term.destEq(statement) match {
      case None => Left(NotOfForm("an equation", statement))

      case Some((left, right)) if Term.typeOf(left) == Matrices =>
        byComponents(unfolding, left, right)

      case Some(_) =>
        Induct.afterRewriting(unfolding.entries, statement)(unfolding.ring.prove)
    }

  /** `|- left = right` between matrices, from four equations between reals. */
  private def byComponents(
    unfolding: Unfolding,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftEquation <- Rewrite.rewrite(unfolding.entries, left)
      rightEquation <- Rewrite.rewrite(unfolding.entries, right)
      leftNormal <- rightOf(leftEquation)
      rightNormal <- rightOf(rightEquation)

      ls <- destConstructor(leftNormal).toRight(reduced(leftNormal))
      rs <- destConstructor(rightNormal).toRight(reduced(rightNormal))

      first <- component(unfolding, ls._1, rs._1)
      second <- component(unfolding, ls._2, rs._2)
      third <- component(unfolding, ls._3, rs._3)
      fourth <- component(unfolding, ls._4, rs._4)

      partial <- Conv.apTerm(unfolding.constructor, first)
      twoOf <- LogicError.lift(Kernel.mkComb(partial, second))
      threeOf <- LogicError.lift(Kernel.mkComb(twoOf, third))
      rebuilt <- LogicError.lift(Kernel.mkComb(threeOf, fourth))

      half <- Conv.trans(leftEquation, rebuilt)
      result <- Conv.sym(rightEquation).flatMap(Conv.trans(half, _))
    } yield result

  /**
   * One component, with the two refusals kept apart.
   *
   * The ring saying no means one of two things and they call for opposite actions: either the
   * identity is false, or the rewriting stopped before it had finished and the ring was shown a
   * term with operations still in it. Asking which costs one pass of the conversion and is asked
   * only on the failing path, which is `Rewrite.finished`'s own instruction.
   */
  private def component(
    unfolding: Unfolding,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      equation <- LogicError.lift(Term.eq(left, right))
      proved <- unfolding.ring.prove(equation).left.flatMap { refusal =>
        Rewrite
          .finished(unfolding.entries, equation)
          .flatMap(settled => if (settled) Left(refusal) else Left(NotNormalised(equation)))
      }
    } yield proved

  /** The four arguments of a constructor, or nothing if that is not what this is. */
  private def destConstructor(term: Term): Option[(Term, Term, Term, Term)] = term match {
    case App(App(App(App(Const(Constructor, _), a), b), c), d) => Some((a, b, c, d))
    case _ => None
  }

  /** The refusal that names what the rules could not reduce, rather than that something failed. */
  private def reduced(term: Term): LogicError =
    NotOfForm(s"a matrix the rules reduce to $Constructor of four reals", term)

  /* ----------------------------------------------------- the six derived by hand */

  /**
   * `|- !a b c d. MAT_E11 (MAT2 a b c d) = a`, and the three like it.
   *
   * The bridge every other fact crosses, and the only place `FST` and `SND` appear in a derivation
   * here: `MAT_E11` unfolds to `FST (FST -)`, the constructor unfolds to a pair of pairs, and the
   * pair's own two laws take it from there. Everything above this line is stated about `MAT2` and
   * never about `PAIR`.
   *
   * The result is checked against the variable it should be rather than assumed to be it. A rule
   * set that stopped one step early would otherwise produce `FST (PAIR a b) = FST (PAIR a b)`,
   * which is a true theorem and is not this lemma.
   */
  private def accessorLaws(
    logic: Logic,
    theory: Theory,
    crossing: Vector[Rewrite.Rule],
    constructor: Term
  ): Either[LogicError, Vector[Kernel.Thm]] = {
    val letters = List("a", "b", "c", "d").map(name => Term.variable(name, Values))

    Vector(Entry11, Entry12, Entry21, Entry22).zip(letters).foldLeft[
      Either[LogicError, Vector[Kernel.Thm]]
    ](Right(Vector.empty)) { (acc, entry) =>
      val (name, expected) = entry

      for {
        made <- acc
        accessor <- LogicError.lift(theory.constant(name, Type.fun(Matrices, Values)))
        subject <- LogicError.lift(Term.appAll(constructor, letters))
        applied <- LogicError.lift(Term.app(accessor, subject))
        equation <- Rewrite.rewrite(crossing, applied)
        found <- rightOf(equation)
        // The same assembly check as above and spelt the same way: what the rewriting produced is
        // not the entry this law is about, which is a defect here rather than a fact about any
        // identity.
        _ <- if (found == expected) Right(()) else Left(NotOfForm(s"the entry $expected", found))
        law <- logic.rules.genAll(equation, letters)
      } yield made :+ law
    }
  }

  /**
   * `|- !m. MAT2 (MAT_E11 m) (MAT_E12 m) (MAT_E21 m) (MAT_E22 m) = m`.
   *
   * Surjective pairing, twice, in the direction that terminates as a rewrite rule. The left side is
   * unfolded by the same rules the accessors were proved with, which takes it to
   * `PAIR (PAIR (FST (FST m)) (SND (FST m))) (PAIR (FST (SND m)) (SND (SND m)))`; the right side is
   * taken to the same term by `Product.Surjective` at the outer pair and then at each of the two
   * rows. The two have to meet **on the nose**, and if they do not this refuses rather than
   * trying something else, which is `Rewrite.prove`'s stated discipline applied by hand.
   */
  private def folding(
    logic: Logic,
    theory: Theory,
    crossing: Vector[Rewrite.Rule],
    constructor: Term,
    insidePair: Kernel.Thm,
    outsidePair: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val m = Term.variable("m", Matrices)

    for {
      first <- LogicError.lift(theory.constant(Product.First, Type.fun(Matrices, Rows)))
      second <- LogicError.lift(theory.constant(Product.Second, Type.fun(Matrices, Rows)))
      pairing <- LogicError.lift(
        theory.constant(Product.Pairing, Type.fun(Rows, Type.fun(Rows, Matrices)))
      )

      atMatrix <- rules.spec(m, outsidePair)
      firstRow <- LogicError.lift(Term.app(first, m))
      secondRow <- LogicError.lift(Term.app(second, m))
      atFirst <- rules.spec(firstRow, insidePair)
      atSecond <- rules.spec(secondRow, insidePair)

      partial <- Conv.apTerm(pairing, atFirst)
      rows <- LogicError.lift(Kernel.mkComb(partial, atSecond))
      openedUp <- Conv.trans(atMatrix, rows)

      accessors <- Vector(Entry11, Entry12, Entry21, Entry22)
        .foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, name) =>
          for {
            made <- acc
            accessor <- LogicError.lift(theory.constant(name, Type.fun(Matrices, Values)))
            applied <- LogicError.lift(Term.app(accessor, m))
          } yield made :+ applied
        }
      rebuilt <- LogicError.lift(Term.appAll(constructor, accessors))
      unfolded <- Rewrite.rewrite(crossing, rebuilt)

      result <- Conv.sym(openedUp).flatMap(Conv.trans(unfolded, _))
      law <- rules.gen(m, result)
    } yield law
  }

  /** The same fact the way `Product.Surjective` is written, which is the way it is stated. */
  private def surjectiveConstructor(
    logic: Logic,
    folded: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val m = Term.variable("m", Matrices)

    for {
      instance <- logic.rules.spec(m, folded)
      turned <- Conv.sym(instance)
      law <- logic.rules.gen(m, turned)
    } yield law
  }

  /**
   * `|- !a b c d e f g h. (MAT2 a b c d = MAT2 e f g h) = (a = e /\ b = f /\ c = g /\ d = h)`.
   *
   * Both directions, joined by `Kernel.deductAntisym`, which is what a biconditional is in this
   * kernel: equality at `bool`. The forward direction applies each accessor to the assumed equation
   * and reads the four laws off both sides; the backward direction is congruence on the constructor
   * and needs no property of matrices at all. The same shape as `Product.pairInjective` one file
   * over, at four components instead of two, and it costs the accessor laws rather than the
   * representation.
   */
  private def injectiveConstructor(
    logic: Logic,
    theory: Theory,
    constructor: Term,
    entries: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val front = List("a", "b", "c", "d").map(name => Term.variable(name, Values))
    val back = List("e", "f", "g", "h").map(name => Term.variable(name, Values))

    for {
      left <- LogicError.lift(Term.appAll(constructor, front))
      right <- LogicError.lift(Term.appAll(constructor, back))
      same <- LogicError.lift(Term.eq(left, right))
      assumed <- LogicError.lift(Kernel.assume(same))

      forwards <- Vector(Entry11, Entry12, Entry21, Entry22).zip(entries).foldLeft[
        Either[LogicError, Vector[Kernel.Thm]]
      ](Right(Vector.empty)) { (acc, item) =>
        val (name, law) = item

        for {
          made <- acc
          accessor <- LogicError.lift(theory.constant(name, Type.fun(Matrices, Values)))
          carried <- Conv.apTerm(accessor, assumed)
          onLeft <- rules.specAll(law, front)
          onRight <- rules.specAll(law, back)
          fromLeft <- Conv.sym(onLeft)
          through <- Conv.trans(fromLeft, carried)
          component <- Conv.trans(through, onRight)
        } yield made :+ component
      }

      // Taken apart by a pattern rather than by four indices. An index into a `Vector` whose
      // length the type does not carry throws where this returns a refusal, and throwing to signal
      // a refusal is the one thing this repository's error handling does not do.
      parts <- forwards.toList match {
        case first :: second :: third :: fourth :: Nil => Right((first, second, third, fourth))
        case other => Left(NotOfForm(s"four component equations, not ${other.size}", same))
      }
      (firstEqual, secondEqual, thirdEqual, fourthEqual) = parts

      innermost <- rules.conjIntro(thirdEqual, fourthEqual)
      middle <- rules.conjIntro(secondEqual, innermost)
      forward <- rules.conjIntro(firstEqual, middle)

      conjunction = forward.conclusion
      assumedAll <- LogicError.lift(Kernel.assume(conjunction))
      firstHalf <- rules.conjElim1(assumedAll)
      rest <- rules.conjElim2(assumedAll)
      secondHalf <- rules.conjElim1(rest)
      tail <- rules.conjElim2(rest)
      thirdHalf <- rules.conjElim1(tail)
      fourthHalf <- rules.conjElim2(tail)

      partial <- Conv.apTerm(constructor, firstHalf)
      twoOf <- LogicError.lift(Kernel.mkComb(partial, secondHalf))
      threeOf <- LogicError.lift(Kernel.mkComb(twoOf, thirdHalf))
      backward <- LogicError.lift(Kernel.mkComb(threeOf, fourthHalf))

      equivalence = Kernel.deductAntisym(backward, forward)
      law <- rules.genAll(equivalence, front ++ back)
    } yield law
  }

  /* ------------------------------------------------------------------- internals */

  /** `real -> real -> real -> real -> prod(prod(real,real),prod(real,real))`. */
  private def constructorType: Type =
    Type.fun(Values, Type.fun(Values, Type.fun(Values, Type.fun(Values, Matrices))))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
