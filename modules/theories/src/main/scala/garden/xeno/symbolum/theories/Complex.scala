package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The complex numbers, as a type defined over the pairs of reals, with `cis`, De Moivre, the polar
 * form, the `n`-th roots and the roots of unity.
 *
 * `docs/adr/0060` is the decision. `complex` is the seventh type `Kernel.defineType` carves in the
 * chain and the eighth in the repository, `pterm` beside the chain being the other, and it carves
 * the **whole** of `prod(real,real)`: the predicate is `\p. T`. That is the case `Matrix` argues
 * against for its own type, and the argument is right there: a bijection with every pair buys a
 * name and costs a bijection to cross. What decides the other way here is the notation. `+`, `*`
 * and `-` stand for the complex operations as they stand for the reals' (`docs/adr/0018`), and the
 * elaborator picks a constant by the type its operands settle. Over `prod(real,real)` that type is
 * also a row of a matrix and the carrier of anything else built from two reals, so `p * q` would read
 * as the complex product for every pair of reals in the signature, which is a reading nobody checking
 * a statement can see. A type of its own is what keeps the overload to the numbers it means.
 *
 * Nothing here is asserted. The type, `COMPLEX` and every operation are definitions; every
 * fact is derived, and what it rests on is what the reals rest on: choice, eta and infinity.
 *
 * == One driver for every identity ==
 *
 * `Complex.Driver` proves an equation between complex numbers by proving it of the two parts:
 * `COMPLEX_EQ` turns `L = R` into `Re L = Re R /\ Im L = Im R`, the component rules (`RE_ADD`,
 * `IM_MUL` and the rest) push `Re` and `Im` through every operation down to real atoms, and `Ring`
 * settles what is left. An operation the rules do not open, `complex_pow` or a variable, stays an
 * atom: `Re (complex_pow z n)` is a real like any other, which is what lets the power laws be proved
 * by induction with this as the closer. Where an identity needs a fact, the induction hypothesis or
 * `r * inv r = 1`, the closer is `Linarith` over that fact's components instead.
 *
 * == The inverse at zero ==
 *
 * `complex_inv z` is `COMPLEX (Re z / |z|^2) (-(Im z) / |z|^2)`, with no case for zero, and
 * `complex_inv 0 = 0` is still a theorem: both parts are `0 * inv 0`, which is zero whatever `inv 0`
 * is. So this needs no answer to what the reals' `inv 0` is, which their interface does not publish.
 *
 * == The polar form and the roots ==
 *
 * The angle of `z` is `acos (Re z / |z|)` when `Im z` is not negative and `2 pi` minus it when it is,
 * and `ARG_SPEC` says the chosen one lands in `[0, 2 pi)`. The `n`-th root of `|z| cis t` is
 * `exp (ln |z| / n) cis (t / n)`, by De Moivre and `Power (exp u) n = exp (n u)`. The sum of a root
 * of unity's powers is the geometric series, which vanishes unless the root is one, and `cis t` is not
 * one strictly between `0` and `2 pi` because `cos` falls on `[0, pi]`.
 *
 * == The fundamental theorem of algebra ==
 *
 * Published here and derived in [[Fundamental]], by the polar route `docs/adr/0061` records: the
 * modulus of a polynomial attains a least value over the plane, and d'Alembert's lemma, which spends
 * the roots above, says that a value which is not zero is not the least.
 *
 * == The finite Fourier transform, and the Collatz iterate ==
 *
 * Published here and derived in [[FiniteFourier]] and [[CollatzFourier]], as `docs/adr/0062`
 * records: the transform over the roots of unity inverts, by their orthogonality, and its real
 * reading writes the `t`-th iterate of the shortcut Collatz map as a series over the residues modulo
 * `2^t` whose coefficients are the transforms of each class's slope and offset.
 */
final class Complex private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm],
  driver: Complex.Driver
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /**
   * An identity between complex numbers, proved part by part and closed by `Ring`, or the refusal
   * of the step that could not: an equation is asked of, nothing else.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] = driver.identity(goal)

  /** The same, on a statement written in this development's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] = proposition(text).flatMap(prove)
}

object Complex {

  /* ------------------------------------------------------------------ the names */

  val TypeName: String = "complex"
  val Abstraction: String = "mk_complex"
  val Representation: String = "dest_complex"

  /** The carved subset is all of it. */
  val RepresentationBody: String = "\\p:prod(real,real). T"

  val Constructor: String = "COMPLEX"
  val RealPart: String = "Re"
  val ImaginaryPart: String = "Im"
  val OfReal: String = "complex_of_real"
  val ImaginaryUnit: String = "ii"
  val Add: String = "complex_add"
  val Negation: String = "complex_neg"
  val Subtraction: String = "complex_sub"
  val Multiplication: String = "complex_mul"
  val Conjugate: String = "cnj"
  val NormSquared: String = "complex_norm_sq"
  val Norm: String = "complex_norm"
  val Inverse: String = "complex_inv"
  val Summation: String = "complex_sum"
  val Cis: String = "cis"
  val Argument: String = "complex_arg"
  val Power: String = "complex_pow"

  /** The definitions that are not a recursion, in the order they are made. */
  val Bodies: Vector[(String, String)] = Vector(
    Constructor -> "\\x:real. \\y:real. mk_complex (PAIR x y)",
    RealPart -> "\\z:complex. FST (dest_complex z)",
    ImaginaryPart -> "\\z:complex. SND (dest_complex z)",
    OfReal -> "\\x:real. COMPLEX x 0",
    ImaginaryUnit -> "COMPLEX 0 1",
    Add -> "\\z:complex. \\w:complex. COMPLEX (Re z + Re w) (Im z + Im w)",
    Negation -> "\\z:complex. COMPLEX (-(Re z)) (-(Im z))",
    Subtraction -> "\\z:complex. \\w:complex. COMPLEX (Re z - Re w) (Im z - Im w)",
    Multiplication -> "\\z:complex. \\w:complex. COMPLEX (Re z * Re w - Im z * Im w) (Re z * Im w + Im z * Re w)",
    Conjugate -> "\\z:complex. COMPLEX (Re z) (-(Im z))",
    NormSquared -> "\\z:complex. Re z * Re z + Im z * Im z",
    Norm -> "\\z:complex. sqrt (complex_norm_sq z)",
    Inverse -> "\\z:complex. COMPLEX (Re z / complex_norm_sq z) (-(Im z) / complex_norm_sq z)",
    Summation -> "\\f:num->complex. \\n:num. COMPLEX (Sum (\\i:num. Re (f i)) n) (Sum (\\i:num. Im (f i)) n)",
    Cis -> "\\t:real. COMPLEX (cos t) (sin t)"
  )

  /** Defined after the operators read at `complex`, because its body is written with them. */
  val ArgumentBody: String =
    "\\z:complex. select (\\t:real. 0 <= t /\\ t < 2 * pi /\\ z = complex_of_real (complex_norm z) * cis t)"

  val ReOfConstructor: String = "RE_COMPLEX"
  val ImOfConstructor: String = "IM_COMPLEX"
  val Surjective: String = "COMPLEX_SURJECTIVE"
  val Injective: String = "COMPLEX_INJECTIVE"
  val Extensional: String = "COMPLEX_EQ"

  /** `Re` and `Im` of each operation: the rules the driver pushes the parts through with. */
  val Components: Vector[(String, String)] = Vector(
    "RE_ADD" -> "!z:complex. !w:complex. Re (z + w) = Re z + Re w",
    "IM_ADD" -> "!z:complex. !w:complex. Im (z + w) = Im z + Im w",
    "RE_NEG" -> "!z:complex. Re (complex_neg z) = -(Re z)",
    "IM_NEG" -> "!z:complex. Im (complex_neg z) = -(Im z)",
    "RE_SUB" -> "!z:complex. !w:complex. Re (z - w) = Re z - Re w",
    "IM_SUB" -> "!z:complex. !w:complex. Im (z - w) = Im z - Im w",
    "RE_MUL" -> "!z:complex. !w:complex. Re (z * w) = Re z * Re w - Im z * Im w",
    "IM_MUL" -> "!z:complex. !w:complex. Im (z * w) = Re z * Im w + Im z * Re w",
    "RE_OF_REAL" -> "!x:real. Re (complex_of_real x) = x",
    "IM_OF_REAL" -> "!x:real. Im (complex_of_real x) = 0",
    "RE_II" -> "Re ii = 0",
    "IM_II" -> "Im ii = 1",
    "RE_CNJ" -> "!z:complex. Re (cnj z) = Re z",
    "IM_CNJ" -> "!z:complex. Im (cnj z) = -(Im z)",
    "RE_INV" -> "!z:complex. Re (complex_inv z) = Re z / complex_norm_sq z",
    "IM_INV" -> "!z:complex. Im (complex_inv z) = -(Im z) / complex_norm_sq z",
    "RE_SUM" -> "!f:num->complex. !n:num. Re (complex_sum f n) = Sum (\\i:num. Re (f i)) n",
    "IM_SUM" -> "!f:num->complex. !n:num. Im (complex_sum f n) = Sum (\\i:num. Im (f i)) n",
    "RE_CIS" -> "!t:real. Re (cis t) = cos t",
    "IM_CIS" -> "!t:real. Im (cis t) = sin t"
  )

  /** Which definition each component rule opens. */
  private val Opens: Map[String, String] = Map(
    "RE_ADD" -> Add, "IM_ADD" -> Add, "RE_NEG" -> Negation, "IM_NEG" -> Negation,
    "RE_SUB" -> Subtraction, "IM_SUB" -> Subtraction, "RE_MUL" -> Multiplication, "IM_MUL" -> Multiplication,
    "RE_OF_REAL" -> OfReal, "IM_OF_REAL" -> OfReal, "RE_II" -> ImaginaryUnit, "IM_II" -> ImaginaryUnit,
    "RE_CNJ" -> Conjugate, "IM_CNJ" -> Conjugate, "RE_INV" -> Inverse, "IM_INV" -> Inverse,
    "RE_SUM" -> Summation, "IM_SUM" -> Summation, "RE_CIS" -> Cis, "IM_CIS" -> Cis
  )

  /** The field, the embedding and the conjugate: identities the driver proves with nothing owed. */
  val Identities: Vector[(String, String)] = Vector(
    "COMPLEX_ADD_SYM" -> "!z:complex. !w:complex. z + w = w + z",
    "COMPLEX_ADD_ASSOC" -> "!z:complex. !w:complex. !v:complex. (z + w) + v = z + (w + v)",
    "COMPLEX_ADD_ZERO" -> "!z:complex. z + complex_of_real 0 = z",
    "COMPLEX_ADD_INVERSE" -> "!z:complex. z + complex_neg z = complex_of_real 0",
    "COMPLEX_SUB" -> "!z:complex. !w:complex. z - w = z + complex_neg w",
    "COMPLEX_MUL_SYM" -> "!z:complex. !w:complex. z * w = w * z",
    "COMPLEX_MUL_ASSOC" -> "!z:complex. !w:complex. !v:complex. (z * w) * v = z * (w * v)",
    "COMPLEX_MUL_ONE" -> "!z:complex. z * complex_of_real 1 = z",
    "COMPLEX_DISTRIBUTE" -> "!z:complex. !w:complex. !v:complex. z * (w + v) = z * w + z * v",
    "COMPLEX_INV_ZERO" -> "complex_inv (complex_of_real 0) = complex_of_real 0",
    "II_SQUARED" -> "ii * ii = complex_neg (complex_of_real 1)",
    "COMPLEX_OF_REAL_ADD" -> "!x:real. !y:real. complex_of_real (x + y) = complex_of_real x + complex_of_real y",
    "COMPLEX_OF_REAL_MUL" -> "!x:real. !y:real. complex_of_real (x * y) = complex_of_real x * complex_of_real y",
    "CNJ_CNJ" -> "!z:complex. cnj (cnj z) = z",
    "CNJ_ADD" -> "!z:complex. !w:complex. cnj (z + w) = cnj z + cnj w",
    "CNJ_MUL" -> "!z:complex. !w:complex. cnj (z * w) = cnj z * cnj w",
    "COMPLEX_MUL_CNJ" -> "!z:complex. z * cnj z = complex_of_real (complex_norm_sq z)",
    "COMPLEX_NORM_SQ_MUL" -> "!z:complex. !w:complex. complex_norm_sq (z * w) = complex_norm_sq z * complex_norm_sq w"
  )

  /** Everything derived by hand or by induction, in the order it is derived. */
  val Derived: Vector[(String, String)] = Vector(
    "COMPLEX_MUL_INVERSE" -> "!z:complex. ~(z = complex_of_real 0) ==> z * complex_inv z = complex_of_real 1",
    "COMPLEX_ONE_NOT_ZERO" -> "~(complex_of_real 1 = complex_of_real 0)",
    "COMPLEX_ENTIRE" -> "!z:complex. !w:complex. z * w = complex_of_real 0 ==> z = complex_of_real 0 \\/ w = complex_of_real 0",
    "COMPLEX_NORM_SQ_NONNEG" -> "!z:complex. 0 <= complex_norm_sq z",
    "COMPLEX_NORM_SQ_ZERO" -> "!z:complex. complex_norm_sq z = 0 ==> z = complex_of_real 0",
    "COMPLEX_NORM_NONNEG" -> "!z:complex. 0 <= complex_norm z",
    "COMPLEX_NORM_SQUARED" -> "!z:complex. complex_norm z * complex_norm z = complex_norm_sq z",
    "COMPLEX_NORM_MUL" -> "!z:complex. !w:complex. complex_norm (z * w) = complex_norm z * complex_norm w",
    "COMPLEX_NORM_ZERO" -> "!z:complex. complex_norm z = 0 ==> z = complex_of_real 0",
    "COMPLEX_POW_ZERO" -> "!z:complex. complex_pow z 0 = complex_of_real 1",
    "COMPLEX_POW_SUC" -> "!z:complex. !n:num. complex_pow z (SUC n) = z * complex_pow z n",
    "COMPLEX_POW_ADD" -> "!z:complex. !n:num. !m:num. complex_pow z (n + m) = complex_pow z n * complex_pow z m",
    "COMPLEX_POW_MUL" -> "!z:complex. !n:num. !m:num. complex_pow z (n * m) = complex_pow (complex_pow z n) m",
    "COMPLEX_MUL_POW" -> "!z:complex. !w:complex. !n:num. complex_pow (z * w) n = complex_pow z n * complex_pow w n",
    "COMPLEX_POW_ONE" -> "!n:num. complex_pow (complex_of_real 1) n = complex_of_real 1",
    "COMPLEX_POW_OF_REAL" -> "!x:real. !n:num. complex_pow (complex_of_real x) n = complex_of_real (Power x n)",
    "COMPLEX_POW_ZERO_BASE" -> "!n:num. 0 < n ==> complex_pow (complex_of_real 0) n = complex_of_real 0",
    "COMPLEX_SUM_ZERO" -> "!f:num->complex. complex_sum f 0 = complex_of_real 0",
    "COMPLEX_SUM_SUC" -> "!f:num->complex. !n:num. complex_sum f (SUC n) = complex_sum f n + f n",
    "COMPLEX_SUM_ONE" -> "!n:num. complex_sum (\\r:num. complex_of_real 1) n = complex_of_real (real_of_num n)",
    "COMPLEX_GEOMETRIC" ->
      "!v:complex. !n:num. (complex_of_real 1 - v) * complex_sum (\\r:num. complex_pow v r) n = complex_of_real 1 - complex_pow v n",
    "COS_NEG" -> "!x:real. cos (-x) = cos x",
    "SIN_NEG" -> "!x:real. sin (-x) = -(sin x)",
    "SIN_NONNEG" -> "!x:real. 0 <= x /\\ x <= pi ==> 0 <= sin x",
    "EXP_POWER" -> "!u:real. !n:num. Power (exp u) n = exp (real_of_num n * u)",
    "CIS_ZERO" -> "cis 0 = complex_of_real 1",
    "CIS_ADD" -> "!s:real. !t:real. cis (s + t) = cis s * cis t",
    "CIS_PERIODIC" -> "!t:real. cis (t + 2 * pi) = cis t",
    "COMPLEX_NORM_CIS" -> "!t:real. complex_norm (cis t) = 1",
    "DE_MOIVRE" -> "!t:real. !n:num. complex_pow (cis t) n = cis (real_of_num n * t)",
    "CIS_NOT_ONE" -> "!t:real. 0 < t /\\ t < 2 * pi ==> ~(cis t = complex_of_real 1)",
    "ARG_SPEC" ->
      "!z:complex. 0 <= complex_arg z /\\ complex_arg z < 2 * pi /\\ z = complex_of_real (complex_norm z) * cis (complex_arg z)",
    "COMPLEX_POLAR" -> "!z:complex. ?t:real. z = complex_of_real (complex_norm z) * cis t",
    "COMPLEX_ROOT" -> "!z:complex. !n:num. 0 < n ==> (?w:complex. complex_pow w n = z)",
    "ROOT_OF_UNITY" -> "!m:num. 0 < m ==> complex_pow (cis (2 * pi / real_of_num m)) m = complex_of_real 1",
    "ROOTS_OF_UNITY_SUM_DIVIDES" ->
      ("!m:num. !h:num. 0 < m /\\ NUM_DIVIDES m h ==> " +
        "complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num m)) (h * r)) m = complex_of_real (real_of_num m)"),
    "ROOTS_OF_UNITY_SUM_NOT_DIVIDES" ->
      ("!m:num. !h:num. 0 < m /\\ ~NUM_DIVIDES m h ==> " +
        "complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num m)) (h * r)) m = complex_of_real 0")
  )

  /** Everything published, as the text a person checks it by. */
  val Statements: Vector[(String, String)] =
    Vector(
      ReOfConstructor -> "!x:real. !y:real. Re (COMPLEX x y) = x",
      ImOfConstructor -> "!x:real. !y:real. Im (COMPLEX x y) = y",
      Surjective -> "!z:complex. z = COMPLEX (Re z) (Im z)",
      Injective -> "!a:real. !b:real. !c:real. !d:real. (COMPLEX a b = COMPLEX c d) = (a = c /\\ b = d)",
      Extensional -> "!z:complex. !w:complex. (z = w) = (Re z = Re w /\\ Im z = Im w)"
    ) ++ Components ++ Identities ++ Derived ++ Fundamental.Statements ++ FiniteFourier.Statements ++
      CollatzFourier.Statements

  /** `complex`. */
  val Complexes: Type = TyApp(TypeName, Nil)
  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Pairs: Type = TyApp(Product.TypeName, List(Reals, Reals))

  /** The development over the standard chain. */
  lazy val standard: Complex = Chain.standard.complex

  /**
   * The development over the chain's links it reads, extending `base`.
   *
   * `lookup` answers a fact of any link below by name, which is what the derivations spend: the
   * pair's projections, the reals' laws, `sqrt`, the trigonometric addition laws, `pi`, the sums
   * and the arithmetic of `num`.
   */
  def construct(
    classical: Classical,
    naturals: Natural,
    peano: Peano,
    ring: Ring,
    magnitude: Magnitude,
    product: Product,
    lookup: String => Either[LogicError, Kernel.Thm],
    reals: RealTheory,
    within: Kernel.Thm,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Complex] = {
    val read = notation
      .withInfix("+", Add, Real.AdditionPrecedence)
      .withInfix("-", Subtraction, Real.AdditionPrecedence)
      .withInfix("*", Multiplication, Real.MultiplicationPrecedence)

    def define(theory: Theory, name: String, text: String): Either[LogicError, (Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, read, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    for {
      narrow <- classical.logic.over(base)
      truth <- truthTheorem(narrow)
      predicate <- Parser.term(base, read, RepresentationBody)
      sample <- Parser.term(base, read, "PAIR (0:real) (0:real)")
      witness <- holds(predicate, sample, truth)
      typed <- LogicError.lift(Kernel.defineType(base, TypeName, Abstraction, Representation, witness))
      (withType, (absOfRep, repOfAbs)) = typed

      introduced <- Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](Right((withType, Map.empty))) {
        case (acc, (name, text)) =>
          for {
            state <- acc
            made <- define(state._1, name, text)
          } yield (made._1, state._2 + (name -> made._2))
      }
      (withBodies, bodies) = introduced
      argued <- define(withBodies, Argument, ArgumentBody)
      (withArgument, argumentDefinition) = argued

      wide <- classical.logic.over(withArgument)
      recursion <- naturals.recursion
      b = Term.variable("b", Complexes)
      powered <- Recursion.define(
        wide, naturals, withArgument, read, recursion, Power, Complexes,
        "complex_of_real 1", "\\v:complex. \\i:num. (b:complex) * v", Some(b)
      )
      (theory, powerDefinition, powerAtZero, powerAtSuccessor) = powered
      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      induction <- naturals.fact(Natural.Induction)

      definitions = bodies + (Argument -> argumentDefinition) + (Power -> powerDefinition)
      proofs = Proofs(logic, classical, theory, read, ring, linarith, product, lookup, induction, definitions)
      characterised <- proofs.characterisation(absOfRep, repOfAbs, truth)
      components <- proofs.components(characterised)
      driver = Driver(logic, ring, linarith, theory, read, characterised(Extensional), components.values.toVector :+ definitions(NormSquared))
      identities <- Identities.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
        case (acc, (name, text)) =>
          for {
            made <- acc
            goal <- Parser.proposition(theory, read, text)
            proved <- driver.identity(goal)
          } yield made + (name -> proved)
      }
      derived <- proofs.derived(driver, characterised ++ components ++ identities, powerAtZero, powerAtSuccessor)
      base = characterised ++ components ++ identities ++ derived
      kit = ComplexKit(logic, classical, theory, read, ring, linarith, driver, induction,
        name => base.get(name).toRight(MissingDefinition(name)).orElse(lookup(name)), within, reals, definitions)
      fundamental <- Fundamental.prove(kit, base)
      semiring <- Semiring.construct(peano)
      fourier <- FiniteFourier.prove(kit, semiring, base ++ fundamental)
      collatz <- CollatzFourier.prove(kit, semiring, recursion, base ++ fundamental ++ fourier)
      facts = base ++ fundamental ++ fourier ++ collatz

      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(theory, read, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Complex(theory, read, logic, definitions, facts, driver)
  }

  /** `|- T`, from `|- x = x` read as an equation with truth. */
  private def truthTheorem(logic: Logic): Either[LogicError, Kernel.Thm] = {
    val x = Term.variable("x", Type.Bool)
    val reflexive = Conv.refl(x)
    for {
      withTruth <- logic.rules.eqTruthIntro(reflexive)
      result <- LogicError.lift(Kernel.eqMp(withTruth, reflexive))
    } yield result
  }

  /** `|- P a`, for `P` a predicate whose body is `T`. */
  private def holds(predicate: Term, argument: Term, truth: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      applied <- LogicError.lift(Term.app(predicate, argument))
      reduced <- Conv.betaRoot(applied)
      back <- Conv.sym(reduced)
      result <- LogicError.lift(Kernel.eqMp(back, truth))
    } yield result

  /* ------------------------------------------------------------ the arithmetic */

  /** The constants `Linarith` reads through: everything else is an atom to it. */
  private val Arithmetic: Set[String] = Set(
    Real.Addition, Real.Subtraction, Real.Multiplication, Real.Negation, Real.Order, Real.NonStrictOrder,
    Real.Bit0, Real.Bit1, Real.Zero, Real.One, Term.EqualityName,
    Logic.Conjunction, Logic.Disjunction, Logic.Implication, Logic.Negation, Logic.Truth, Logic.Falsity
  )

  /** The two constants `Linarith` refuses a goal for when what they divide by is not a numeral. */
  private val Quotients: Set[String] = Set(Real.Inverse, Real.Division)

  private def headOf(t: Term): Term = t match {
    case App(f, _) => headOf(f)
    case other => other
  }

  private def mentionsQuotient(t: Term): Boolean = t match {
    case Const(name, _) => Quotients(name)
    case App(f, x) => mentionsQuotient(f) || mentionsQuotient(x)
    case Abs(_, body) => mentionsQuotient(body)
    case _ => false
  }

  /**
   * `t` with every atom that holds a quotient replaced by a variable, the same atom by the same one.
   *
   * `Linarith` refuses a goal dividing by anything but a numeral, because cancelling a symbolic
   * denominator is `Field`'s to assume. Nothing here asks it to cancel one: `inv (complex_norm z)` is
   * an atom whose value nothing in the argument depends on, and what is linear in it is linear in a
   * variable standing for it. So the implication is proved at the variables and instantiated back,
   * which the kernel checks like any instantiation.
   */
  private def abstractQuotients(
    t: Term,
    seen: Map[Term, FVar],
    avoid: Set[FVar]
  ): Either[LogicError, (Term, Map[Term, FVar])] =
    headOf(t) match {
      case Const(name, _) if Arithmetic(name) =>
        t match {
          case App(f, x) =>
            for {
              left <- abstractQuotients(f, seen, avoid)
              right <- abstractQuotients(x, left._2, avoid)
              rebuilt <- LogicError.lift(Term.app(left._1, right._1))
            } yield (rebuilt, right._2)
          case _ => Right((t, seen))
        }
      case _ if mentionsQuotient(t) =>
        seen.get(t) match {
          case Some(v) => Right((v, seen))
          case None =>
            val v = Conv.freshVariable("q", Term.typeOf(t), avoid ++ seen.values)
            Right((v, seen.updated(t, v)))
        }
      case _ => Right((t, seen))
    }

  /** `goal` from `facts` by `Linarith`, as one implication, its quotients abstracted, detached. */
  private[theories] def conclude(logic: Logic, linarith: Linarith, facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      implication <- facts.reverse.foldLeft[Either[LogicError, Term]](Right(goal)) { (acc, f) =>
        acc.flatMap(g => logic.mkImp(f.conclusion, g))
      }
      abstracted <- abstractQuotients(implication, Map.empty, Term.freeVariables(implication).toSet)
      general <- linarith.prove(abstracted._1)
      proved <- LogicError.lift(Kernel.inst(abstracted._2.map(_.swap), general))
      result <- facts.foldLeft[Either[LogicError, Kernel.Thm]](Right(proved))((acc, f) => acc.flatMap(logic.rules.mp(_, f)))
    } yield result

  /* --------------------------------------------------------------- the driver */

  /**
   * Proves an equation by its parts.
   *
   * `rules` are the component rules and the definition of `complex_norm_sq`; `closing` is what
   * settles each part once they have been applied, `Ring` unless a caller has a fact to hand.
   */
  private[theories] final case class Driver(
    logic: Logic,
    ring: Ring,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    extensional: Kernel.Thm,
    components: Vector[Kernel.Thm],
    extra: Vector[Kernel.Thm] = Vector.empty,
    closing: Option[Term => Either[LogicError, Kernel.Thm]] = None
  ) {
    private val rules = logic.rules

    /** The same driver with `more` rewritten with first. */
    def using(more: Kernel.Thm*): Driver = copy(extra = more.toVector ++ extra)

    /** The same driver closing each part with `Linarith` over the parts of `facts`. */
    def from(facts: Kernel.Thm*): Either[LogicError, Driver] =
      for {
        parts <- facts.toVector.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, f) =>
          acc.flatMap(made => partsOf(f).map(made ++ _))
        }
      } yield copy(closing = Some(goal => conclude(parts, goal)))

    /** `goal` from `facts` by `Linarith`, as one implication detached. */
    def conclude(facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
      Complex.conclude(logic, linarith, facts, goal)

    private def ruleSet: Either[LogicError, Vector[Rewrite.Rule]] = Rewrite.Rule.all(logic, extra ++ components)

    /** A fact with its parts opened: two real equations for a complex one, itself rewritten else. */
    def partsOf(fact: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
      Term.destEq(fact.conclusion) match {
        case Some((left, right)) if Term.typeOf(left) == Complexes =>
          for {
            opened <- rules.spec(left, extensional).flatMap(rules.spec(right, _))
            both <- LogicError.lift(Kernel.eqMp(opened, fact))
            re <- rules.conjElim1(both)
            im <- rules.conjElim2(both)
            set <- ruleSet
            reOpen <- Rewrite.inTheorem(set, re)
            imOpen <- Rewrite.inTheorem(set, im)
          } yield Vector(reOpen, imOpen)
        case _ =>
          for {
            set <- ruleSet
            opened <- Rewrite.inTheorem(set, fact)
          } yield Vector(opened)
      }

    /** A real equation or inequality, after the rules, closed. */
    def real(goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        set <- ruleSet
        proved <- Induct.afterRewriting(set, goal)(closing.getOrElse(ring.prove))
      } yield proved

    /** `L = R` at complex type, by `COMPLEX_EQ` and the two parts. */
    def equation(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        opened <- rules.spec(left, extensional).flatMap(rules.spec(right, _))
        parts <- Term.destEq(opened.conclusion).map(_._2).toRight(NotOfForm("an equation", opened.conclusion))
        halves <- logic.destConj(parts).toRight(NotOfForm("a conjunction", parts))
        re <- real(halves._1)
        im <- real(halves._2)
        both <- rules.conjIntro(re, im)
        back <- Conv.sym(opened)
        result <- LogicError.lift(Kernel.eqMp(back, both))
      } yield result

    /** A universally quantified equation, at either type. */
    def identity(goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        stripped <- Logic.stripForall(goal)
        (bound, body) = stripped
        proved <- Term.destEq(body) match {
          case Some((left, right)) if Term.typeOf(left) == Complexes => equation(left, right)
          case Some(_) => real(body)
          case None => Left(NotOfForm("an equation", body))
        }
        result <- rules.genAll(proved, bound.toList)
      } yield result

    /** The same, read from text. */
    def identity(text: String): Either[LogicError, Kernel.Thm] =
      Parser.proposition(theory, notation, text).flatMap(identity)
  }

  /* ----------------------------------------------------------------- the proofs */

  private final case class Proofs(
    logic: Logic,
    classical: Classical,
    theory: Theory,
    notation: Notation,
    ring: Ring,
    linarith: Linarith,
    product: Product,
    lookup: String => Either[LogicError, Kernel.Thm],
    induction: Kernel.Thm,
    definitions: Map[String, Kernel.Thm]
  ) {
    private val rules = logic.rules
    private val said = Statements.toMap

    private def statement(name: String): Either[LogicError, Term] =
      said.get(name).toRight(MissingDefinition(name)).flatMap(Parser.proposition(theory, notation, _))
    private def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    private def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Reals)
    private def complex(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Complexes)
    private def assume(t: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(t))
    private def fact(name: String): Either[LogicError, Kernel.Thm] = lookup(name)
    private def constant(name: String, ty: Type): Either[LogicError, Term] = LogicError.lift(theory.constant(name, ty))

    private def conclude(facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
      Complex.conclude(logic, linarith, facts, goal)

    private def concludeText(facts: Seq[Kernel.Thm], goal: String): Either[LogicError, Kernel.Thm] =
      proposition(goal).flatMap(conclude(facts, _))

    private def ringEquation(text: String): Either[LogicError, Kernel.Thm] = proposition(text).flatMap(ring.prove)

    /** `|- f a = f b` from `|- a = b`, for `f` a constant of type `from -> to`. */
    private def carried(name: String, from: Type, to: Type, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      constant(name, Type.fun(from, to)).flatMap(Conv.apTerm(_, equation))

    private def premise(implication: Kernel.Thm): Either[LogicError, Term] =
      logic.destImp(implication.conclusion).map(_._1).toRight(NotOfForm("an implication", implication.conclusion))

    /** `instance`'s antecedent by `Linarith` from `facts`, detached. */
    private def discharged(instance: Kernel.Thm, facts: Seq[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        wanted <- premise(instance)
        held <- conclude(facts, wanted)
        result <- rules.mp(instance, held)
      } yield result

    private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

    /** `name`'s statement with its quantifiers stripped. */
    private def body(name: String): Either[LogicError, (Vector[FVar], Term)] =
      statement(name).flatMap(Logic.stripForall)

    /** The pair's facts at `real` and `real`. */
    private def atReals(name: String): Either[LogicError, Kernel.Thm] =
      product
        .fact(name)
        .map(Kernel.instType(Map(Classical.TypeVariable -> Reals, Classical.CodomainVariable -> Reals), _))

    /* ------------------------------------------------------ the characterisation */

    def characterisation(
      absOfRep: Kernel.Thm,
      repOfAbs: Kernel.Thm,
      truth: Kernel.Thm
    ): Either[LogicError, Map[String, Kernel.Thm]] = {
      val r = Term.variable("r", Pairs)
      val z = Term.variable("z", Complexes)
      val w = Term.variable("w", Complexes)
      for {
        // dest (mk r) = r for every r: the characterisation's left side is `(\p. T) r`, which holds.
        sides <- Term.destEq(repOfAbs.conclusion).toRight(NotOfForm("an equation", repOfAbs.conclusion))
        predicateAt <- sides._1 match {
          case App(p, a) => holds(p, a, truth)
          case other => Left(NotOfForm("a predicate applied", other))
        }
        repAbs <- LogicError.lift(Kernel.eqMp(repOfAbs, predicateAt)).flatMap(rules.gen(r, _))

        first <- atReals(Product.FirstOfPair)
        second <- atReals(Product.SecondOfPair)
        surjectivePair <- atReals(Product.Surjective)
        crossing <- Rewrite.Rule.all(
          logic,
          Vector(repAbs, first, second) ++ Vector(Constructor, RealPart, ImaginaryPart).map(definitions)
        )
        reOf <- byRewriting(ReOfConstructor, crossing)
        imOf <- byRewriting(ImOfConstructor, crossing)

        // z = COMPLEX (Re z) (Im z): unfold the right side to mk (PAIR (FST d) (SND d)), fold the pair.
        constructor <- constant(Constructor, Type.fun(Reals, Type.fun(Reals, Complexes)))
        re <- constant(RealPart, Type.fun(Complexes, Reals))
        im <- constant(ImaginaryPart, Type.fun(Complexes, Reals))
        abs <- constant(Abstraction, Type.fun(Pairs, Complexes))
        rep <- constant(Representation, Type.fun(Complexes, Pairs))
        reZ <- LogicError.lift(Term.app(re, z))
        imZ <- LogicError.lift(Term.app(im, z))
        rebuilt <- LogicError.lift(Term.appAll(constructor, List(reZ, imZ)))
        opening <- Rewrite.Rule.all(logic, Vector(Constructor, RealPart, ImaginaryPart).map(definitions))
        unfolded <- Rewrite.rewrite(opening, rebuilt)
        d <- LogicError.lift(Term.app(rep, z))
        pairAt <- rules.spec(d, surjectivePair).flatMap(Conv.sym)
        abstracted <- Conv.apTerm(abs, pairAt)
        back <- LogicError.lift(Kernel.inst(Map(Term.variable("a", Complexes) -> z), absOfRep))
        folded <- Conv.trans(unfolded, abstracted).flatMap(Conv.trans(_, back))
        surjective <- Conv.sym(folded).flatMap(rules.gen(z, _))

        injective <- injectiveConstructor(constructor, reOf, imOf)
        extensional <- extensionality(constructor, re, im, surjective)
      } yield Map(
        ReOfConstructor -> reOf,
        ImOfConstructor -> imOf,
        Surjective -> surjective,
        Injective -> injective,
        Extensional -> extensional
      )
    }

    /** `name`'s statement, an equation, by rewriting its left side with `set`. */
    private def byRewriting(name: String, set: Vector[Rewrite.Rule]): Either[LogicError, Kernel.Thm] =
      for {
        stripped <- body(name)
        (bound, goal) = stripped
        sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
        equation <- Rewrite.rewrite(set, sides._1)
        found <- rightOf(equation)
        _ <- if (found == sides._2) Right(()) else Left(NotOfForm(s"$name's right side", found))
        result <- rules.genAll(equation, bound.toList)
      } yield result

    private def injectiveConstructor(constructor: Term, reOf: Kernel.Thm, imOf: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val List(a, b, c, d) = List("a", "b", "c", "d").map(Term.variable(_, Reals))
      for {
        left <- LogicError.lift(Term.appAll(constructor, List(a, b)))
        right <- LogicError.lift(Term.appAll(constructor, List(c, d)))
        same <- LogicError.lift(Term.eq(left, right))
        assumed <- assume(same)
        reEq <- part(RealPart, assumed, reOf, List(a, b), List(c, d))
        imEq <- part(ImaginaryPart, assumed, imOf, List(a, b), List(c, d))
        forward <- rules.conjIntro(reEq, imEq)
        both <- assume(forward.conclusion)
        first <- rules.conjElim1(both)
        second <- rules.conjElim2(both)
        partial <- Conv.apTerm(constructor, first)
        backward <- LogicError.lift(Kernel.mkComb(partial, second))
        result <- rules.genAll(Kernel.deductAntisym(backward, forward), List(a, b, c, d))
      } yield result
    }

    /** `|- x = y` from `|- COMPLEX x _ = COMPLEX y _` through the part named. */
    private def part(name: String, equation: Kernel.Thm, law: Kernel.Thm, front: List[Term], back: List[Term]) =
      for {
        accessor <- constant(name, Type.fun(Complexes, Reals))
        moved <- Conv.apTerm(accessor, equation)
        onLeft <- rules.specAll(law, front).flatMap(Conv.sym)
        onRight <- rules.specAll(law, back)
        result <- Conv.trans(onLeft, moved).flatMap(Conv.trans(_, onRight))
      } yield result

    private def extensionality(constructor: Term, re: Term, im: Term, surjective: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val z = Term.variable("z", Complexes)
      val w = Term.variable("w", Complexes)
      for {
        same <- LogicError.lift(Term.eq(z, w))
        assumed <- assume(same)
        reEq <- Conv.apTerm(re, assumed)
        imEq <- Conv.apTerm(im, assumed)
        forward <- rules.conjIntro(reEq, imEq)
        both <- assume(forward.conclusion)
        first <- rules.conjElim1(both)
        second <- rules.conjElim2(both)
        partial <- Conv.apTerm(constructor, first)
        parts <- LogicError.lift(Kernel.mkComb(partial, second))
        atZ <- rules.spec(z, surjective)
        atW <- rules.spec(w, surjective).flatMap(Conv.sym)
        backward <- Conv.trans(atZ, parts).flatMap(Conv.trans(_, atW))
        result <- rules.genAll(Kernel.deductAntisym(backward, forward), List(z, w))
      } yield result
    }

    /** `Re` and `Im` of each operation, each by opening that one definition. */
    def components(characterised: Map[String, Kernel.Thm]): Either[LogicError, Map[String, Kernel.Thm]] =
      Components.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) { case (acc, (name, _)) =>
        for {
          made <- acc
          opens <- Opens.get(name).toRight(MissingDefinition(name))
          set <- Rewrite.Rule.all(
            logic,
            Vector(definitions(opens), characterised(ReOfConstructor), characterised(ImOfConstructor))
          )
          proved <- byRewriting(name, set)
        } yield made + (name -> proved)
      }

    /* ---------------------------------------------------------- by hand and by induction */

    def derived(
      driver0: Driver,
      known: Map[String, Kernel.Thm],
      powerAtZero: Kernel.Thm,
      powerAtSuccessor: Kernel.Thm
    ): Either[LogicError, Map[String, Kernel.Thm]] = {
      val z = Term.variable("z", Complexes)
      val w = Term.variable("w", Complexes)
      val x = Term.variable("x", Reals)
      val t = Term.variable("t", Reals)
      val n = Term.variable("n", Numbers)
      val normSq = definitions(NormSquared)
      val driver = driver0
      val induct = Induct.withCloser(logic, driver.identity, induction)

      def cx(name: String): Kernel.Thm = known(name)

      for {
        // ---------------------------------------------------------------- the inverse
        normSqZero <- {
          // a * a + b * b = 0 gives a = 0 and b = 0, each by the sign of a square
          for {
            hT <- proposition("complex_norm_sq z = 0")
            h <- assume(hT)
            opened <- Conv.unfold(normSq, List(z))
            sum <- Conv.sym(opened).flatMap(Conv.trans(_, h))
            reZero <- squareZero("Re z", sum)
            imZero <- squareZero("Im z", sum)
            closing <- driver.from(reZero, imZero)
            zero <- complex("complex_of_real 0")
            result <- closing.equation(z, zero)
            out <- rules.disch(hT, result).flatMap(rules.gen(z, _))
          } yield out
        }
        normSqNonneg <- for {
          opened <- Conv.unfold(normSq, List(z))
          a <- real("Re z").flatMap(v => fact("SQUARE_NONNEG").flatMap(rules.spec(v, _)))
          b <- real("Im z").flatMap(v => fact("SQUARE_NONNEG").flatMap(rules.spec(v, _)))
          result <- concludeText(Seq(opened, a, b), "0 <= complex_norm_sq z")
          out <- rules.gen(z, result)
        } yield out
        mulInverse <- for {
          hT <- proposition("~(z = complex_of_real 0)")
          h <- assume(hT)
          nT <- proposition("complex_norm_sq z = 0")
          notZero <- for {
            zeroed <- assume(nT).flatMap(a => rules.spec(z, normSqZero).flatMap(rules.mp(_, a)))
            absurd <- rules.notElim(h, zeroed)
            out <- rules.notIntro(nT, absurd)
          } yield out
          nTerm <- real("complex_norm_sq z")
          inverse <- fact("MUL_INVERSE").flatMap(rules.spec(nTerm, _)).flatMap(rules.mp(_, notZero))
          division <- fact(Real.Division)
          closing <- driver.using(division).from(inverse)
          left <- complex("z * complex_inv z")
          one <- complex("complex_of_real 1")
          result <- closing.equation(left, one)
          out <- rules.disch(hT, result).flatMap(rules.gen(z, _))
        } yield out
        oneNotZero <- for {
          oneZero <- proposition("complex_of_real 1 = complex_of_real 0")
          assumed <- assume(oneZero)
          parts <- driver.partsOf(assumed)
          absurd <- concludeText(parts, "F")
          out <- rules.notIntro(oneZero, absurd)
        } yield out
        entire <- for {
          hT <- proposition("z * w = complex_of_real 0")
          h <- assume(hT)
          zeroZ <- proposition("z = complex_of_real 0")
          zeroW <- proposition("w = complex_of_real 0")
          left <- assume(zeroZ).flatMap(rules.disjIntro1(zeroW, _))
          right <- for {
            notZero <- logic.mkNot(zeroZ).flatMap(assume)
            identityT <- complex("complex_inv z * (z * w)").flatMap(l =>
              complex("(z * complex_inv z) * w").flatMap(r => driver.equation(l, r)))
            inverse <- rules.spec(z, mulInverse).flatMap(rules.mp(_, notZero))
            rewritten <- Limit.rewriteInProposition(h, identityT).flatMap(Limit.rewriteInProposition(inverse, _))
            closing <- driver.from(rewritten)
            zero <- complex("complex_of_real 0")
            wZero <- closing.equation(w, zero)
            out <- rules.disjIntro2(zeroZ, wZero)
          } yield out
          cased <- classical.cases(zeroZ, left, right)
          out <- rules.disch(hT, cased).flatMap(rules.genAll(_, List(z, w)))
        } yield out

        // ---------------------------------------------------------------- the norm
        sqrtFact <- for {
          nTerm <- real("complex_norm_sq z")
          nonneg <- rules.spec(z, normSqNonneg)
          root <- fact("SQRT").flatMap(rules.spec(nTerm, _)).flatMap(rules.mp(_, nonneg))
          opened <- Conv.unfold(definitions(Norm), List(z)).flatMap(Conv.sym)
          named <- Limit.rewriteInProposition(opened, root)
        } yield named
        normNonneg <- rules.conjElim1(sqrtFact).flatMap(rules.gen(z, _))
        normSquared <- rules.conjElim2(sqrtFact).flatMap(rules.gen(z, _))
        normMul <- for {
          y <- real("complex_norm z * complex_norm w")
          nzw <- real("complex_norm_sq (z * w)")
          unique <- fact("SQRT_UNIQUE").flatMap(rules.specAll(_, List(nzw, y)))
          nonZ <- rules.spec(z, normNonneg)
          nonW <- rules.spec(w, normNonneg)
          positive <- concludeText(Seq(nonZ, nonW), "0 <= complex_norm z * complex_norm w")
          regrouped <- ringEquation(
            "(complex_norm z * complex_norm w) * (complex_norm z * complex_norm w) = " +
              "(complex_norm z * complex_norm z) * (complex_norm w * complex_norm w)")
          squaredZ <- rules.spec(z, normSquared)
          squaredW <- rules.spec(w, normSquared)
          step <- Limit.rewriteInProposition(squaredZ, regrouped).flatMap(Limit.rewriteInProposition(squaredW, _))
          multiplicative <- rules.specAll(cx("COMPLEX_NORM_SQ_MUL"), List(z, w)).flatMap(Conv.sym)
          square <- Conv.trans(step, multiplicative)
          both <- rules.conjIntro(positive, square)
          rooted <- rules.mp(unique, both)
          result <- complex("z * w").flatMap(zw => Conv.unfold(definitions(Norm), List(zw))).flatMap(Conv.trans(_, rooted))
          out <- rules.genAll(result, List(z, w))
        } yield out
        normZero <- for {
          hT <- proposition("complex_norm z = 0")
          h <- assume(hT)
          squared <- rules.spec(z, normSquared)
          zero <- concludeText(Seq(h, squared), "complex_norm_sq z = 0")
          result <- rules.spec(z, normSqZero).flatMap(rules.mp(_, zero))
          out <- rules.disch(hT, result).flatMap(rules.gen(z, _))
        } yield out

        // ---------------------------------------------------------------- the power
        powZero <- named("COMPLEX_POW_ZERO", powerAtZero)
        powSuc <- named("COMPLEX_POW_SUC", powerAtSuccessor)
        powAdd <- numAdd.flatMap(adding => statement("COMPLEX_POW_ADD").flatMap(induct.prove(_, Vector(powZero, powSuc) ++ adding)))
        powMul <- for {
          suc <- fact("NUM_MUL_SUC")
          zeroTimes <- fact("NUM_MUL_ZERO")
          goal <- statement("COMPLEX_POW_MUL")
          proved <- induct.prove(goal, Vector(zeroTimes, suc, powAdd, powZero, powSuc))
        } yield proved
        mulPow <- statement("COMPLEX_MUL_POW").flatMap(induct.prove(_, Vector(powZero, powSuc)))
        powOne <- statement("COMPLEX_POW_ONE").flatMap(induct.prove(_, Vector(powZero, powSuc)))
        powOfReal <- for {
          zeroP <- fact("POWER_ZERO")
          sucP <- fact("POWER_SUC")
          goal <- statement("COMPLEX_POW_OF_REAL")
          proved <- induct.prove(goal, Vector(powZero, powSuc, zeroP, sucP))
        } yield proved
        powZeroBase <- for {
          hT <- proposition("0 < (n:num)")
          h <- assume(hT)
          cases <- fact("NUM_CASES").flatMap(rules.spec(n, _))
          split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
          goal <- proposition("complex_pow (complex_of_real 0) n = complex_of_real 0")
          atZero <- for {
            isZero <- assume(split._1)
            moved <- Limit.rewriteInProposition(isZero, h)
            absurd <- rightOf(isZero).flatMap(zero => fact("NUM_LT_IRREFL").flatMap(rules.spec(zero, _))).flatMap(rules.notElim(_, moved))
            out <- rules.falsityElim(goal, absurd)
          } yield out
          atSuccessor <- for {
            exists <- assume(split._2)
            m = Term.variable("m", Numbers)
            instanceT <- logic.destExistsPredicate(split._2).toRight(NotOfForm("an existential", split._2))
              .flatMap(p => LogicError.lift(Term.app(p, m))).flatMap(Conv.betaRoot).flatMap(rightOf)
            instance <- assume(instanceT)
            successorT <- proposition("complex_pow (complex_of_real 0) (SUC m) = complex_of_real 0")
            successor <- driver.using(powSuc).identity(successorT)
            moved <- Conv.sym(instance).flatMap(Limit.rewriteInProposition(_, successor))
            out <- rules.existsElim(exists, m, moved)
          } yield out
          result <- rules.disjElim(cases, atZero, atSuccessor)
          out <- rules.disch(hT, result).flatMap(rules.gen(n, _))
        } yield out

        // ---------------------------------------------------------------- the sum
        sumZero <- fact("SUM_ZERO").flatMap(s => statement("COMPLEX_SUM_ZERO").flatMap(driver.using(s).identity))
        sumSuc <- fact("SUM_SUC").flatMap(s => statement("COMPLEX_SUM_SUC").flatMap(driver.using(s).identity))
        sumOne <- for {
          realZero <- fact("NUM_REAL_ZERO")
          realSuc <- fact("NUM_REAL_SUC")
          goal <- statement("COMPLEX_SUM_ONE")
          proved <- induct.prove(goal, Vector(sumZero, sumSuc, realZero, realSuc))
        } yield proved
        geometric <- for {
          goal <- statement("COMPLEX_GEOMETRIC")
          proved <- induct.proveBy(
            goal,
            base => driver.using(sumZero, powZero).identity(base),
            step =>
              for {
                closing <- driver.using(sumSuc, powSuc).from(step.hypothesis)
                out <- closing.identity(step.goal)
              } yield out
          )
        } yield proved

        // ---------------------------------------------------------------- the circle
        cosNeg <- negation("cos (-x) = cos x", cosine = true)
        sinNeg <- negation("sin (-x) = -(sin x)", cosine = false)
        sinNonneg <- sinNonnegative
        expPower <- exponentialPower

        cisZero <- for {
          s0 <- fact("SIN_ZERO")
          c0 <- fact("COS_ZERO")
          out <- statement("CIS_ZERO").flatMap(driver.using(s0, c0).identity)
        } yield out
        cisAdd <- for {
          sa <- fact("SIN_ADD")
          ca <- fact("COS_ADD")
          out <- statement("CIS_ADD").flatMap(driver.using(sa, ca).identity)
        } yield out
        cisPeriodic <- for {
          sp <- fact("SIN_PERIODIC")
          cp <- fact("COS_PERIODIC")
          out <- statement("CIS_PERIODIC").flatMap(driver.using(sp, cp).identity)
        } yield out
        normCis <- for {
          square <- fact("SIN_COS_SQUARED").flatMap(rules.spec(t, _))
          nT <- proposition("complex_norm_sq (cis t) = sin t * sin t + cos t * cos t")
          opened <- driver.identity(nT)
          one <- Conv.trans(opened, square)
          rooted <- carried("sqrt", Reals, Reals, one)
          sqrtOne <- fact("SQRT_ONE")
          unfolded <- complex("cis t").flatMap(c => Conv.unfold(definitions(Norm), List(c)))
          result <- Conv.trans(unfolded, rooted).flatMap(Conv.trans(_, sqrtOne))
          out <- rules.gen(t, result)
        } yield out
        deMoivre <- for {
          goal <- proposition("!n:num. complex_pow (cis t) n = cis (real_of_num n * t)")
          realZero <- fact("NUM_REAL_ZERO")
          realSuc <- fact("NUM_REAL_SUC")
          proved <- induct.proveBy(
            goal,
            base =>
              for {
                zeroRules <- Rewrite.Rule.all(logic, Vector(realZero))
                angle <- proposition("real_of_num 0 * t = 0").flatMap(Induct.afterRewriting(zeroRules, _)(ring.prove))
                cisAngle <- carried(Cis, Reals, Complexes, angle)
                zeroPow <- complex("cis t").flatMap(c => rules.spec(c, powZero))
                result <- Conv.trans(cisAngle, cisZero).flatMap(Conv.sym).flatMap(Conv.trans(zeroPow, _))
              } yield result,
            step =>
              for {
                k <- Right(step.variable)
                open <- complex("cis t").flatMap(c => rules.specAll(powSuc, List(c, k)))
                withHypothesis <- Limit.rewriteInProposition(step.hypothesis, open)
                added <- real("real_of_num " + k.name + " * t").flatMap(a => rules.specAll(cisAdd, List(t, a))).flatMap(Conv.sym)
                joined <- Conv.trans(withHypothesis, added)
                angleT <- proposition(s"t + real_of_num ${k.name} * t = real_of_num (SUC ${k.name}) * t")
                angle <- Rewrite.Rule.all(logic, Vector(realSuc)).flatMap(set => Induct.afterRewriting(set, angleT)(ring.prove))
                moved <- carried(Cis, Reals, Complexes, angle)
                result <- Conv.trans(joined, moved)
              } yield result
          )
          out <- rules.gen(t, proved)
        } yield out

        mine = known ++ Map(
          "COMPLEX_MUL_INVERSE" -> mulInverse, "COMPLEX_ENTIRE" -> entire, "COMPLEX_NORM_NONNEG" -> normNonneg,
          "COMPLEX_NORM_SQUARED" -> normSquared, "COMPLEX_NORM_ZERO" -> normZero, "COMPLEX_POW_ZERO" -> powZero,
          "COMPLEX_POW_SUC" -> powSuc, "COMPLEX_POW_ADD" -> powAdd, "COMPLEX_POW_MUL" -> powMul,
          "COMPLEX_MUL_POW" -> mulPow, "COMPLEX_POW_ONE" -> powOne, "COMPLEX_POW_OF_REAL" -> powOfReal,
          "COMPLEX_POW_ZERO_BASE" -> powZeroBase, "COMPLEX_SUM_ONE" -> sumOne, "COMPLEX_GEOMETRIC" -> geometric,
          "COS_NEG" -> cosNeg, "SIN_NEG" -> sinNeg, "SIN_NONNEG" -> sinNonneg, "EXP_POWER" -> expPower,
          "CIS_ZERO" -> cisZero, "CIS_PERIODIC" -> cisPeriodic, "DE_MOIVRE" -> deMoivre
        )
        cisNotOne <- notOne(mine, driver)
        polar <- polarForm(mine, driver)
        (argSpec, polarExists) = polar
        root <- roots(mine + ("ARG_SPEC" -> argSpec), driver)
        unity <- rootOfUnity(mine)
        divides <- sumDivides(mine + ("ROOT_OF_UNITY" -> unity))
        notDivides <- sumNotDivides(mine + ("ROOT_OF_UNITY" -> unity) + ("CIS_NOT_ONE" -> cisNotOne), driver)
      } yield Map(
        "COMPLEX_MUL_INVERSE" -> mulInverse,
        "COMPLEX_ONE_NOT_ZERO" -> oneNotZero,
        "COMPLEX_ENTIRE" -> entire,
        "COMPLEX_NORM_SQ_NONNEG" -> normSqNonneg,
        "COMPLEX_NORM_SQ_ZERO" -> normSqZero,
        "COMPLEX_NORM_NONNEG" -> normNonneg,
        "COMPLEX_NORM_SQUARED" -> normSquared,
        "COMPLEX_NORM_MUL" -> normMul,
        "COMPLEX_NORM_ZERO" -> normZero,
        "COMPLEX_POW_ZERO" -> powZero,
        "COMPLEX_POW_SUC" -> powSuc,
        "COMPLEX_POW_ADD" -> powAdd,
        "COMPLEX_POW_MUL" -> powMul,
        "COMPLEX_MUL_POW" -> mulPow,
        "COMPLEX_POW_ONE" -> powOne,
        "COMPLEX_POW_OF_REAL" -> powOfReal,
        "COMPLEX_POW_ZERO_BASE" -> powZeroBase,
        "COMPLEX_SUM_ZERO" -> sumZero,
        "COMPLEX_SUM_SUC" -> sumSuc,
        "COMPLEX_SUM_ONE" -> sumOne,
        "COMPLEX_GEOMETRIC" -> geometric,
        "COS_NEG" -> cosNeg,
        "SIN_NEG" -> sinNeg,
        "SIN_NONNEG" -> sinNonneg,
        "EXP_POWER" -> expPower,
        "CIS_ZERO" -> cisZero,
        "CIS_ADD" -> cisAdd,
        "CIS_PERIODIC" -> cisPeriodic,
        "COMPLEX_NORM_CIS" -> normCis,
        "DE_MOIVRE" -> deMoivre,
        "CIS_NOT_ONE" -> cisNotOne,
        "ARG_SPEC" -> argSpec,
        "COMPLEX_POLAR" -> polarExists,
        "COMPLEX_ROOT" -> root,
        "ROOT_OF_UNITY" -> unity,
        "ROOTS_OF_UNITY_SUM_DIVIDES" -> divides,
        "ROOTS_OF_UNITY_SUM_NOT_DIVIDES" -> notDivides
      )
    }

    private def numAdd: Either[LogicError, Vector[Kernel.Thm]] =
      for {
        zero <- fact("NUM_ADD_ZERO")
        suc <- fact("NUM_ADD_SUC")
      } yield Vector(zero, suc)

    /** A recursion equation re-quantified over the variables `name`'s statement uses. */
    private def named(name: String, recurrence: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        stripped <- body(name)
        instance <- rules.specAll(recurrence, stripped._1.toList)
        result <- rules.genAll(instance, stripped._1.toList)
      } yield result

    /** `|- a = 0` from `|- a * a + b * b = 0` or `|- b * b + a * a = 0`-shaped `sum`, `a` written. */
    private def squareZero(text: String, sum: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- real(text)
        others = Seq("Re z", "Im z").filterNot(_ == text)
        b <- real(others.head)
        squareA <- fact("SQUARE_NONNEG").flatMap(rules.spec(a, _))
        squareB <- fact("SQUARE_NONNEG").flatMap(rules.spec(b, _))
        alone <- concludeText(Seq(sum, squareA, squareB), s"$text * $text = 0")
        zero <- real("0")
        total <- fact("LT_TOTAL").flatMap(rules.specAll(_, List(a, zero)))
        goal <- proposition(s"$text = 0")
        split <- logic.destDisj(total.conclusion).toRight(NotOfForm("a disjunction", total.conclusion))
        split2 <- logic.destDisj(split._2).toRight(NotOfForm("a disjunction", split._2))
        below <- assume(split._1).flatMap(h => conclude(Seq(alone, h), goal))
        same <- assume(split2._1)
        above <- assume(split2._2).flatMap(h => conclude(Seq(alone, h), goal))
        inner <- assume(split._2).flatMap(rules.disjElim(_, same, above))
        result <- rules.disjElim(total, below, inner)
      } yield result

    /**
     * `cos (-x) = cos x` or `sin (-x) = -(sin x)`, from the addition law at `x` and `-x`.
     *
     * `a (s s + c c) = c (c a - s b) + s (s a + c b)` and `b (s s + c c) = c (s a + c b) - s (c a - s b)`
     * are ring identities in `a = cos (-x)`, `b = sin (-x)`, `c = cos x`, `s = sin x`; the bracketed
     * sums are one, one and zero, so what is left is linear.
     */
    private def negation(goal: String, cosine: Boolean): Either[LogicError, Kernel.Thm] = {
      val x = Term.variable("x", Reals)
      for {
        ca <- fact("COS_ADD")
        sa <- fact("SIN_ADD")
        c0 <- fact("COS_ZERO")
        s0 <- fact("SIN_ZERO")
        square <- fact("SIN_COS_SQUARED").flatMap(rules.spec(x, _))
        minus <- real("-x")
        cosSum <- rules.specAll(ca, List(x, minus)).flatMap(Conv.sym)
        sinSum <- rules.specAll(sa, List(x, minus)).flatMap(Conv.sym)
        cancel <- ringEquation("x + -x = 0")
        cosZero <- carried("cos", Reals, Reals, cancel).flatMap(Conv.trans(_, c0))
        sinZero <- carried("sin", Reals, Reals, cancel).flatMap(Conv.trans(_, s0))
        cosOne <- Conv.trans(cosSum, cosZero)
        sinNought <- Conv.trans(sinSum, sinZero)
        identityText =
          if (cosine)
            "cos (-x) * (sin x * sin x + cos x * cos x) = " +
              "cos x * (cos x * cos (-x) - sin x * sin (-x)) + sin x * (sin x * cos (-x) + cos x * sin (-x))"
          else
            "sin (-x) * (sin x * sin x + cos x * cos x) = " +
              "cos x * (sin x * cos (-x) + cos x * sin (-x)) - sin x * (cos x * cos (-x) - sin x * sin (-x))"
        identity <- ringEquation(identityText)
        rewritten <- Limit.rewriteInProposition(square, identity)
          .flatMap(Limit.rewriteInProposition(cosOne, _))
          .flatMap(Limit.rewriteInProposition(sinNought, _))
        result <- concludeText(Seq(rewritten), goal)
        out <- rules.gen(x, result)
      } yield out
    }

    /** `0 <= sin x` on `[0, pi]`: positive inside, zero at the two ends. */
    private def sinNonnegative: Either[LogicError, Kernel.Thm] = {
      val x = Term.variable("x", Reals)
      for {
        hT <- proposition("0 <= x /\\ x <= pi")
        h <- assume(hT)
        positive <- fact("SIN_POSITIVE")
        s0 <- fact("SIN_ZERO")
        sPi <- fact("SIN_PI")
        goal <- proposition("0 <= sin x")
        zero <- real("0")
        pi <- real("pi")
        cased <- trichotomy(zero, x, goal)(
          below =>
            trichotomy(x, pi, goal)(
              inside =>
                for {
                  both <- rules.conjIntro(below, inside)
                  p <- rules.spec(x, positive).flatMap(rules.mp(_, both))
                  out <- conclude(Seq(p), goal)
                } yield out,
              atPi =>
                for {
                  moved <- carried("sin", Reals, Reals, atPi).flatMap(Conv.trans(_, sPi))
                  out <- conclude(Seq(moved), goal)
                } yield out,
              beyond => conclude(Seq(h, beyond), goal)
            ),
          atZero =>
            for {
              moved <- Conv.sym(atZero).flatMap(carried("sin", Reals, Reals, _)).flatMap(Conv.trans(_, s0))
              out <- conclude(Seq(moved), goal)
            } yield out,
          negative => conclude(Seq(h, negative), goal)
        )
        out <- rules.disch(hT, cased).flatMap(rules.gen(x, _))
      } yield out
    }

    /** `goal` by `LT_TOTAL` at `a` and `b`, each case handed the assumption it is under. */
    private def trichotomy(a: Term, b: Term, goal: Term)(
      less: Kernel.Thm => Either[LogicError, Kernel.Thm],
      same: Kernel.Thm => Either[LogicError, Kernel.Thm],
      more: Kernel.Thm => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        total <- fact("LT_TOTAL").flatMap(rules.specAll(_, List(a, b)))
        split <- logic.destDisj(total.conclusion).toRight(NotOfForm("a disjunction", total.conclusion))
        split2 <- logic.destDisj(split._2).toRight(NotOfForm("a disjunction", split._2))
        first <- assume(split._1).flatMap(less)
        second <- assume(split2._1).flatMap(same)
        third <- assume(split2._2).flatMap(more)
        inner <- assume(split._2).flatMap(rules.disjElim(_, second, third))
        result <- rules.disjElim(total, first, inner)
      } yield result

    /** `Power (exp u) n = exp (real_of_num n * u)`, by induction on `n` through `EXP_ADD`. */
    private def exponentialPower: Either[LogicError, Kernel.Thm] = {
      val u = Term.variable("u", Reals)
      for {
        zeroP <- fact("POWER_ZERO")
        sucP <- fact("POWER_SUC")
        realZero <- fact("NUM_REAL_ZERO")
        realSuc <- fact("NUM_REAL_SUC")
        expZero <- fact("EXP_ZERO")
        expAdd <- fact("EXP_ADD")
        exp <- constant("exp", Type.fun(Reals, Reals))
        expU <- LogicError.lift(Term.app(exp, u))
        zeroRules <- Rewrite.Rule.all(logic, Vector(realZero))
        sucRules <- Rewrite.Rule.all(logic, Vector(realSuc))
        goal <- proposition("!n:num. Power (exp u) n = exp (real_of_num n * u)")
        proved <- Induct.withCloser(logic, ring.prove, induction).proveBy(
          goal,
          _ =>
            for {
              left <- rules.spec(expU, zeroP)
              angleT <- proposition("real_of_num 0 * u = 0")
              angle <- Induct.afterRewriting(zeroRules, angleT)(ring.prove)
              right <- Conv.apTerm(exp, angle).flatMap(Conv.trans(_, expZero))
              result <- Conv.sym(right).flatMap(Conv.trans(left, _))
            } yield result,
          step =>
            for {
              opened <- rules.specAll(sucP, List(expU, step.variable))
              withHypothesis <- Limit.rewriteInProposition(step.hypothesis, opened)
              k = step.variable.name
              product <- real(s"real_of_num $k * u").flatMap(a => rules.specAll(expAdd, List(u, a))).flatMap(Conv.sym)
              joined <- Conv.trans(withHypothesis, product)
              angleT <- proposition(s"u + real_of_num $k * u = real_of_num (SUC $k) * u")
              angle <- Induct.afterRewriting(sucRules, angleT)(ring.prove)
              moved <- Conv.apTerm(exp, angle)
              result <- Conv.trans(joined, moved)
            } yield result
        )
        out <- rules.gen(u, proved)
      } yield out
    }

    /* ------------------------------------------------- terms built rather than read */

    private def realMul(a: Term, b: Term): Either[LogicError, Term] =
      constant(Real.Multiplication, Type.fun(Reals, Type.fun(Reals, Reals)))
        .flatMap(c => LogicError.lift(Term.appAll(c, List(a, b))))

    private def realInv(a: Term): Either[LogicError, Term] =
      constant(Real.Inverse, Type.fun(Reals, Reals)).flatMap(c => LogicError.lift(Term.app(c, a)))

    private def equal(a: Term, b: Term): Either[LogicError, Term] = LogicError.lift(Term.eq(a, b))

    /** `|- d * q = x` for `q` a quotient of `x` by `d`, written `x / d` or `x * inv d`, given `~(d = 0)`. */
    private def cancelled(d: Term, q: Term, x: Term, nonzero: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        dq <- realMul(d, q)
        dInv <- realInv(d).flatMap(realMul(d, _))
        xTimes <- realMul(x, dInv)
        identity <- equal(dq, xTimes).flatMap(ring.prove)
        inverse <- fact("MUL_INVERSE").flatMap(rules.spec(d, _)).flatMap(rules.mp(_, nonzero))
        rewritten <- Limit.rewriteInProposition(inverse, identity)
        one <- real("1")
        xOne <- realMul(x, one)
        tidy <- equal(xOne, x).flatMap(ring.prove)
        result <- Conv.trans(rewritten, tidy)
      } yield result

    /** `|- ~(a = 0)` from `|- 0 < a`. */
    private def nonzero(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- positive.conclusion match {
          case App(_, a) => Right(a)
          case other => Left(NotOfForm("0 < a", other))
        }
        zero <- real("0")
        isZero <- equal(a, zero)
        assumed <- assume(isZero)
        f <- proposition("F")
        absurd <- conclude(Seq(positive, assumed), f)
        out <- rules.notIntro(isZero, absurd)
      } yield out

    /** `|- 0 < real_of_num n` from `|- 0 < n`. */
    private def positiveReal(n: Term, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        zero <- Parser.term(theory, notation, "0", Numbers)
        lifted <- fact("NUM_REAL_LT").flatMap(rules.specAll(_, List(zero, n))).flatMap(rules.mp(_, positive))
        realZero <- fact("NUM_REAL_ZERO")
        rn <- constant("real_of_num", Type.fun(Numbers, Reals)).flatMap(c => LogicError.lift(Term.app(c, n)))
        lt <- constant(Real.Order, Type.fun(Reals, Type.fun(Reals, Type.Bool)))
        zeroR <- real("0")
        goal <- LogicError.lift(Term.appAll(lt, List(zeroR, rn)))
        out <- conclude(Seq(lifted, realZero), goal)
      } yield out

    /** `|- 0 < complex_norm z` from `~(z = complex_of_real 0)`. */
    private def normPositive(mine: Map[String, Kernel.Thm], z: Term, notZero: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        r <- constant(Norm, Type.fun(Complexes, Reals)).flatMap(c => LogicError.lift(Term.app(c, z)))
        zero <- real("0")
        lt <- constant(Real.Order, Type.fun(Reals, Type.fun(Reals, Type.Bool)))
        goal <- LogicError.lift(Term.appAll(lt, List(zero, r)))
        nonneg <- rules.spec(z, mine("COMPLEX_NORM_NONNEG"))
        out <- trichotomy(zero, r, goal)(
          Right(_),
          same =>
            for {
              zeroed <- Conv.sym(same).flatMap(e => rules.spec(z, mine("COMPLEX_NORM_ZERO")).flatMap(rules.mp(_, e)))
              absurd <- rules.notElim(notZero, zeroed)
              out <- rules.falsityElim(goal, absurd)
            } yield out,
          below => conclude(Seq(nonneg, below), goal)
        )
      } yield out

    /** `?t. P t` for `P` the predicate of `existential`'s own body, from `P a`. */
    private def witnessed(predicateText: String, witness: Term, holdsAt: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        predicate <- Parser.term(theory, notation, predicateText)
        out <- rules.existsIntro(predicate, witness, holdsAt)
      } yield out

    /* --------------------------------------------------------------- not one */

    /** `cis t` is not one strictly inside a turn: `cos t` is below one there. */
    private def notOne(mine: Map[String, Kernel.Thm], driver: Driver): Either[LogicError, Kernel.Thm] = {
      val t = Term.variable("t", Reals)
      for {
        hT <- proposition("0 < t /\\ t < 2 * pi")
        h <- assume(hT)
        eT <- proposition("cis t = complex_of_real 1")
        e <- assume(eT)
        parts <- driver.partsOf(e)
        cosOne = parts(0)
        decreasing <- fact("COS_DECREASING")
        c0 <- fact("COS_ZERO")
        zero <- real("0")
        f <- proposition("F")
        piT <- real("pi")
        halfT <- proposition("t <= pi")
        firstHalf <- for {
          half <- assume(halfT)
          instance <- rules.specAll(decreasing, List(zero, t))
          lt <- discharged(instance, Seq(h, half))
          out <- conclude(Seq(lt, c0, cosOne), f)
        } yield out
        secondHalf <- for {
          notHalf <- logic.mkNot(halfT).flatMap(assume)
          beyond <- fact("LT_OF_NOT_LE").flatMap(rules.specAll(_, List(t, piT))).flatMap(rules.mp(_, notHalf))
          s <- real("2 * pi - t")
          instance <- rules.specAll(decreasing, List(zero, s))
          lt <- discharged(instance, Seq(h, beyond))
          same <- turned(t, "cos", mine("COS_NEG"))
          out <- conclude(Seq(lt, c0, cosOne, same), f)
        } yield out
        absurd <- classical.cases(halfT, firstHalf, secondHalf)
        refuted <- rules.notIntro(eT, absurd)
        out <- rules.disch(hT, refuted).flatMap(rules.gen(t, _))
      } yield out
    }

    /**
     * `|- f t = f (2 * pi - t)` for `f` `cos`, and `|- sin t = -(sin (2 * pi - t))` for `sin`: one
     * period back and a reflection, `COS_PERIODIC` or `SIN_PERIODIC` at `-(2 * pi - t)` and the
     * negation law at `2 * pi - t`.
     */
    private def turned(at: Term, function: String, negation: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val t = Term.variable("t", Reals)
      for {
        s <- real("2 * pi - t")
        minusS <- real("-(2 * pi - t)")
        back <- ringEquation("t = -(2 * pi - t) + 2 * pi")
        moved <- carried(function, Reals, Reals, back)
        periodic <- fact(if (function == "cos") "COS_PERIODIC" else "SIN_PERIODIC").flatMap(rules.spec(minusS, _))
        reflected <- rules.spec(s, negation)
        general <- Conv.trans(moved, periodic).flatMap(Conv.trans(_, reflected)).flatMap(rules.gen(t, _))
        out <- rules.spec(at, general)
      } yield out
    }

    /* ------------------------------------------------------------ the polar form */

    /**
     * Every `z` is `|z| cis t` for a `t` in `[0, 2 pi)`, and `complex_arg` is the one chosen.
     *
     * Away from zero, with `r = |z|`: `Re z / r` is in `[-1, 1]`, so `acos` of it is an angle `t0`
     * in `[0, pi]` with `r cos t0 = Re z`; then `(r sin t0)^2 = (Im z)^2` and `r sin t0 >= 0`, so
     * `r sin t0` is `Im z` or `-(Im z)`, and in the second case `2 pi - t0` turns it round.
     */
    private def polarForm(mine: Map[String, Kernel.Thm], driver: Driver): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
      val z = Term.variable("z", Complexes)
      val predicateText = "\\t:real. 0 <= t /\\ t < 2 * pi /\\ z = complex_of_real (complex_norm z) * cis t"
      for {
        zeroT <- proposition("z = complex_of_real 0")
        bounds <- fact("PI_BOUNDS")
        zero <- real("0")

        atZero <- for {
          e <- assume(zeroT)
          moved <- constant(Norm, Type.fun(Complexes, Reals)).flatMap(Conv.apTerm(_, e))
          normOfZero <- driver.identity("complex_norm_sq (complex_of_real 0) = 0")
            .flatMap(sq => constant("sqrt", Type.fun(Reals, Reals)).flatMap(Conv.apTerm(_, sq)))
          sqrtZero <- fact("SQRT_ZERO")
          unfolded <- complex("complex_of_real 0").flatMap(c => Conv.unfold(definitions(Norm), List(c)))
          normZero <- Conv.trans(moved, unfolded).flatMap(Conv.trans(_, normOfZero)).flatMap(Conv.trans(_, sqrtZero))
          c0 <- fact("COS_ZERO")
          s0 <- fact("SIN_ZERO")
          closing <- driver.using(c0, s0).from(e, normZero)
          right <- complex("complex_of_real (complex_norm z) * cis 0")
          equation <- closing.equation(z, right)
          range <- concludeText(Seq(bounds), "(0:real) <= 0 /\\ 0 < 2 * pi")
          lower <- rules.conjElim1(range)
          upper <- rules.conjElim2(range)
          all <- rules.conjIntro(upper, equation).flatMap(rules.conjIntro(lower, _))
          out <- witnessed(predicateText, zero, all)
        } yield out

        awayFromZero <- for {
          notZero <- logic.mkNot(zeroT).flatMap(assume)
          positive <- normPositive(mine, z, notZero)
          r <- real("complex_norm z")
          a <- real("Re z")
          b <- real("Im z")
          squared <- rules.spec(z, mine("COMPLEX_NORM_SQUARED"))
          opened <- Conv.unfold(definitions(NormSquared), List(z))
          sum <- concludeText(Seq(squared, opened), "Re z * Re z + Im z * Im z = complex_norm z * complex_norm z")
          squareB <- fact("SQUARE_NONNEG").flatMap(rules.spec(b, _))
          lt <- fact("LT_MUL")

          // -r <= a <= r, each by the product the opposite case would make positive
          upper <- for {
            caseT <- proposition("complex_norm z < Re z")
            above <- for {
              c <- assume(caseT)
              factors <- concludeText(Seq(c, positive), "0 < Re z - complex_norm z /\\ 0 < Re z + complex_norm z")
              left <- real("Re z - complex_norm z")
              right <- real("Re z + complex_norm z")
              product <- rules.specAll(lt, List(left, right)).flatMap(rules.mp(_, factors))
              out <- concludeText(Seq(sum, squareB, product), "Re z <= complex_norm z")
            } yield out
            notAbove <- for {
              c <- logic.mkNot(caseT).flatMap(assume)
              out <- fact("LE_OF_NOT_LT").flatMap(rules.specAll(_, List(r, a))).flatMap(rules.mp(_, c))
            } yield out
            out <- classical.cases(caseT, above, notAbove)
          } yield out
          lower <- for {
            caseT <- proposition("Re z < -(complex_norm z)")
            below <- for {
              c <- assume(caseT)
              factors <- concludeText(Seq(c, positive), "0 < -(complex_norm z) - Re z /\\ 0 < complex_norm z - Re z")
              left <- real("-(complex_norm z) - Re z")
              right <- real("complex_norm z - Re z")
              product <- rules.specAll(lt, List(left, right)).flatMap(rules.mp(_, factors))
              out <- concludeText(Seq(sum, squareB, product), "-(complex_norm z) <= Re z")
            } yield out
            notBelow <- for {
              c <- logic.mkNot(caseT).flatMap(assume)
              minusR <- real("-(complex_norm z)")
              out <- fact("LE_OF_NOT_LT").flatMap(rules.specAll(_, List(a, minusR))).flatMap(rules.mp(_, c))
            } yield out
            out <- classical.cases(caseT, below, notBelow)
          } yield out

          // x = Re z * inv r, in [-1, 1], and t0 = acos x
          rNonzero <- nonzero(positive)
          x <- real("Re z * inv (complex_norm z)")
          scaled <- cancelled(r, x, a, rNonzero)
          one <- real("1")
          xUpper <- for {
            caseT <- proposition("1 < Re z * inv (complex_norm z)")
            above <- for {
              c <- assume(caseT)
              factors <- concludeText(Seq(c, positive), "0 < Re z * inv (complex_norm z) - 1 /\\ 0 < complex_norm z")
              left <- real("Re z * inv (complex_norm z) - 1")
              product <- rules.specAll(lt, List(left, r)).flatMap(rules.mp(_, factors))
              out <- concludeText(Seq(scaled, upper, product), "Re z * inv (complex_norm z) <= 1")
            } yield out
            notAbove <- for {
              c <- logic.mkNot(caseT).flatMap(assume)
              out <- fact("LE_OF_NOT_LT").flatMap(rules.specAll(_, List(one, x))).flatMap(rules.mp(_, c))
            } yield out
            out <- classical.cases(caseT, above, notAbove)
          } yield out
          xLower <- for {
            caseT <- proposition("Re z * inv (complex_norm z) < 0 - 1")
            below <- for {
              c <- assume(caseT)
              factors <- concludeText(Seq(c, positive), "0 < (0 - 1) - Re z * inv (complex_norm z) /\\ 0 < complex_norm z")
              left <- real("(0 - 1) - Re z * inv (complex_norm z)")
              product <- rules.specAll(lt, List(left, r)).flatMap(rules.mp(_, factors))
              out <- concludeText(Seq(scaled, lower, product), "0 - 1 <= Re z * inv (complex_norm z)")
            } yield out
            notBelow <- for {
              c <- logic.mkNot(caseT).flatMap(assume)
              minusOne <- real("0 - 1")
              out <- fact("LE_OF_NOT_LT").flatMap(rules.specAll(_, List(x, minusOne))).flatMap(rules.mp(_, c))
            } yield out
            out <- classical.cases(caseT, below, notBelow)
          } yield out
          inRange <- rules.conjIntro(xLower, xUpper)
          acos <- fact("ACOS_SPEC").flatMap(rules.spec(x, _)).flatMap(rules.mp(_, inRange))
          t0 <- real("acos (Re z * inv (complex_norm z))")
          t0Low <- rules.conjElim1(acos)
          t0Rest <- rules.conjElim2(acos)
          t0High <- rules.conjElim1(t0Rest)
          cosT0 <- rules.conjElim2(t0Rest)
          times <- constant(Real.Multiplication, Type.fun(Reals, Type.fun(Reals, Reals))).flatMap(c => LogicError.lift(Term.app(c, r)))
          cosine <- Conv.apTerm(times, cosT0).flatMap(Conv.trans(_, scaled))

          // (r sin t0)^2 = b^2, and r sin t0 >= 0
          sinNonneg <- rules.conjIntro(t0Low, t0High).flatMap(both => rules.spec(t0, mine("SIN_NONNEG")).flatMap(rules.mp(_, both)))
          square <- fact("SIN_COS_SQUARED").flatMap(rules.spec(t0, _))
          generic <- proposition("(rho * sin theta) * (rho * sin theta) = rho * rho * (sin theta * sin theta + cos theta * cos theta) - (rho * cos theta) * (rho * cos theta)")
            .flatMap(ring.prove)
          identity <- LogicError.lift(Kernel.inst(Map(Term.variable("rho", Reals) -> r, Term.variable("theta", Reals) -> t0), generic))
          rewritten <- Limit.rewriteInProposition(square, identity).flatMap(Limit.rewriteInProposition(cosine, _))
          u <- real("complex_norm z * sin (acos (Re z * inv (complex_norm z)))")
          uu <- realMul(u, u)
          bb <- realMul(b, b)
          uSquared <- equal(uu, bb).flatMap(conclude(Seq(rewritten, sum), _))
          uNonneg <- concludeText(Seq(positive, sinNonneg),
            "0 <= complex_norm z * sin (acos (Re z * inv (complex_norm z)))")
          unique <- fact("SQRT_UNIQUE").flatMap(rules.specAll(_, List(bb, u)))
            .flatMap(i => rules.conjIntro(uNonneg, uSquared).flatMap(rules.mp(i, _)))
          rangeT0 <- concludeText(Seq(t0High, bounds), "acos (Re z * inv (complex_norm z)) < 2 * pi")

          signT <- proposition("0 <= Im z")
          upperHalf <- for {
            sign <- assume(signT)
            root <- fact("SQRT_SQUARE").flatMap(rules.spec(b, _)).flatMap(rules.mp(_, sign))
            uIsB <- Conv.sym(unique).flatMap(Conv.trans(_, root))
            closing <- driver.from(cosine, uIsB)
            right <- complex("complex_of_real (complex_norm z) * cis (acos (Re z * inv (complex_norm z)))")
            equation <- closing.equation(z, right)
            all <- rules.conjIntro(rangeT0, equation).flatMap(rules.conjIntro(t0Low, _))
            out <- witnessed(predicateText, t0, all)
          } yield out
          lowerHalf <- for {
            sign <- logic.mkNot(signT).flatMap(assume)
            negative <- fact("LT_OF_NOT_LE").flatMap(rules.specAll(_, List(zero, b))).flatMap(rules.mp(_, sign))
            minusB <- real("-(Im z)")
            flipped <- concludeText(Seq(negative), "0 <= -(Im z)")
            root <- fact("SQRT_SQUARE").flatMap(rules.spec(minusB, _)).flatMap(rules.mp(_, flipped))
            same <- ringEquation("-(Im z) * -(Im z) = Im z * Im z")
            rootB <- Limit.rewriteInProposition(same, root)
            uIsMinusB <- Conv.sym(unique).flatMap(Conv.trans(_, rootB))
            // t0 is not zero: there sin is zero, so u is, and b would be
            t0Positive <- {
              val goalT = proposition("0 < acos (Re z * inv (complex_norm z))")
              goalT.flatMap { goal =>
                trichotomy(zero, t0, goal)(
                  Right(_),
                  atZero =>
                    for {
                      s0 <- fact("SIN_ZERO")
                      sinZero <- Conv.sym(atZero).flatMap(carried("sin", Reals, Reals, _)).flatMap(Conv.trans(_, s0))
                      uZero <- Limit.rewriteInProposition(sinZero, uIsMinusB)
                      out <- conclude(Seq(uZero, negative), goal)
                    } yield out,
                  below => conclude(Seq(below, t0Low), goal)
                )
              }
            }
            t1 <- real("2 * pi - acos (Re z * inv (complex_norm z))")
            cosTurned <- turned(t0, "cos", mine("COS_NEG")).flatMap(Conv.sym)
            sinTurned <- turned(t0, "sin", mine("SIN_NEG")).flatMap { flipped =>
              for {
                sides <- Term.destEq(flipped.conclusion).toRight(NotOfForm("an equation", flipped.conclusion))
                sinS <- sides._2 match {
                  case App(_, inner) => Right(inner)
                  case other => Left(NotOfForm("a negation", other))
                }
                negated <- constant(Real.Negation, Type.fun(Reals, Reals)).flatMap(c => LogicError.lift(Term.app(c, sides._1)))
                out <- equal(sinS, negated).flatMap(conclude(Seq(flipped), _))
              } yield out
            }
            closing <- driver.using(cosTurned, sinTurned).from(cosine, uIsMinusB)
            right <- complex("complex_of_real (complex_norm z) * cis (2 * pi - acos (Re z * inv (complex_norm z)))")
            equation <- closing.equation(z, right)
            range <- concludeText(Seq(t0Positive, t0High, bounds),
              "0 <= 2 * pi - acos (Re z * inv (complex_norm z)) /\\ 2 * pi - acos (Re z * inv (complex_norm z)) < 2 * pi")
            l <- rules.conjElim1(range)
            h <- rules.conjElim2(range)
            all <- rules.conjIntro(h, equation).flatMap(rules.conjIntro(l, _))
            out <- witnessed(predicateText, t1, all)
          } yield out
          out <- classical.cases(signT, upperHalf, lowerHalf)
        } yield out

        exists <- classical.cases(zeroT, atZero, awayFromZero)

        // the argument is the angle chosen
        unfolded <- Conv.unfold(definitions(Argument), List(z))
        selected <- rightOf(unfolded)
        chosen <- classical.axiom(Classical.Choice).flatMap(Classical.witnessFrom(logic, _, exists))
        reduced <- Conv.betaRoot(chosen.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, chosen)))
        named <- Conv.sym(unfolded).flatMap(Limit.rewriteInProposition(_, reduced))
        argSpec <- rules.gen(z, named)

        equation <- rules.conjElim2(named).flatMap(rules.conjElim2)
        arg <- real("complex_arg z")
        polar <- witnessed("\\t:real. z = complex_of_real (complex_norm z) * cis t", arg, equation).flatMap(rules.gen(z, _))
      } yield (argSpec, polar)
    }

    /* ----------------------------------------------------------------- the roots */

    /** `w^n = z` for `n > 0`: zero's root is zero, and `|z| cis t`'s is `exp (ln |z| / n) cis (t / n)`. */
    private def roots(mine: Map[String, Kernel.Thm], driver: Driver): Either[LogicError, Kernel.Thm] = {
      val z = Term.variable("z", Complexes)
      val n = Term.variable("n", Numbers)
      val predicateText = "\\w:complex. complex_pow w n = z"
      for {
        hT <- proposition("0 < (n:num)")
        h <- assume(hT)
        zeroT <- proposition("z = complex_of_real 0")
        atZero <- for {
          e <- assume(zeroT)
          base <- rules.spec(n, mine("COMPLEX_POW_ZERO_BASE")).flatMap(rules.mp(_, h))
          equation <- Conv.sym(e).flatMap(Conv.trans(base, _))
          zero <- complex("complex_of_real 0")
          out <- witnessed(predicateText, zero, equation)
        } yield out
        awayFromZero <- for {
          notZero <- logic.mkNot(zeroT).flatMap(assume)
          positive <- normPositive(mine, z, notZero)
          rn <- real("real_of_num n")
          rnPositive <- positiveReal(n, h)
          rnNonzero <- nonzero(rnPositive)
          polar <- rules.spec(z, mine("ARG_SPEC")).flatMap(rules.conjElim2).flatMap(rules.conjElim2)

          u <- real("ln (complex_norm z) * inv (real_of_num n)")
          a <- real("complex_arg z * inv (real_of_num n)")
          s <- real("exp (ln (complex_norm z) * inv (real_of_num n))")
          w <- complex("complex_of_real (exp (ln (complex_norm z) * inv (real_of_num n))) * cis (complex_arg z * inv (real_of_num n))")
          cofS <- complex("complex_of_real (exp (ln (complex_norm z) * inv (real_of_num n)))")
          cisA <- complex("cis (complex_arg z * inv (real_of_num n))")

          e1 <- rules.specAll(mine("COMPLEX_MUL_POW"), List(cofS, cisA, n))
          e2 <- rules.specAll(mine("COMPLEX_POW_OF_REAL"), List(s, n)).flatMap(Limit.rewriteInProposition(_, e1))
          e3 <- rules.specAll(mine("EXP_POWER"), List(u, n)).flatMap(Limit.rewriteInProposition(_, e2))
          lnR <- real("ln (complex_norm z)")
          cancelU <- cancelled(rn, u, lnR, rnNonzero)
          e4 <- Limit.rewriteInProposition(cancelU, e3)
          expLn <- real("complex_norm z").flatMap(r => fact("EXP_LN").flatMap(rules.spec(r, _))).flatMap(rules.mp(_, positive))
          e5 <- Limit.rewriteInProposition(expLn, e4)
          e6 <- rules.specAll(mine("DE_MOIVRE"), List(a, n)).flatMap(Limit.rewriteInProposition(_, e5))
          arg <- real("complex_arg z")
          cancelA <- cancelled(rn, a, arg, rnNonzero)
          e7 <- Limit.rewriteInProposition(cancelA, e6)
          equation <- Conv.sym(polar).flatMap(Conv.trans(e7, _))
          out <- witnessed(predicateText, w, equation)
        } yield out
        cased <- classical.cases(zeroT, atZero, awayFromZero)
        out <- rules.disch(hT, cased).flatMap(rules.genAll(_, List(z, n)))
      } yield out
    }

    /* ----------------------------------------------------------- roots of unity */

    private def rootOfUnity(mine: Map[String, Kernel.Thm]): Either[LogicError, Kernel.Thm] = {
      val m = Term.variable("m", Numbers)
      for {
        hT <- proposition("0 < (m:num)")
        h <- assume(hT)
        q <- real("2 * pi / real_of_num m")
        rm <- real("real_of_num m")
        twoPi <- real("2 * pi")
        rmPositive <- positiveReal(m, h)
        rmNonzero <- nonzero(rmPositive)
        moivre <- rules.specAll(mine("DE_MOIVRE"), List(q, m))
        cancel <- cancelled(rm, q, twoPi, rmNonzero)
        turn <- carried(Cis, Reals, Complexes, cancel)
        shift <- ringEquation("2 * pi = 0 + 2 * pi").flatMap(carried(Cis, Reals, Complexes, _))
        zero <- real("0")
        periodic <- rules.spec(zero, mine("CIS_PERIODIC"))
        result <- Conv.trans(moivre, turn).flatMap(Conv.trans(_, shift)).flatMap(Conv.trans(_, periodic))
          .flatMap(Conv.trans(_, mine("CIS_ZERO")))
        out <- rules.disch(hT, result).flatMap(rules.gen(m, _))
      } yield out
    }

    /** The rules that open a power of the root at an exponent `m * k`. */
    private def unityRules(mine: Map[String, Kernel.Thm], atM: Kernel.Thm): Either[LogicError, Vector[Rewrite.Rule]] =
      for {
        assoc <- fact("NUM_MUL_ASSOC")
        set <- Rewrite.Rule.all(logic, Vector(assoc, mine("COMPLEX_POW_MUL"), atM, mine("COMPLEX_POW_ONE")))
      } yield set

    private def sumDivides(mine: Map[String, Kernel.Thm]): Either[LogicError, Kernel.Thm] = {
      val m = Term.variable("m", Numbers)
      val h = Term.variable("h", Numbers)
      val k = Term.variable("k", Numbers)
      for {
        hT <- proposition("0 < (m:num) /\\ NUM_DIVIDES m h")
        assumed <- assume(hT)
        positive <- rules.conjElim1(assumed)
        divides <- rules.conjElim2(assumed)
        exists <- fact("NUM_DIVIDES_ELIM").flatMap(rules.specAll(_, List(m, h))).flatMap(rules.mp(_, divides))
        instanceT <- proposition("(h:num) = m * k")
        instance <- assume(instanceT)
        atM <- rules.spec(m, mine("ROOT_OF_UNITY")).flatMap(rules.mp(_, positive))
        set0 <- unityRules(mine, atM)
        set <- Rewrite.Rule.all(logic, Vector(mine("COMPLEX_SUM_ONE"))).map(set0 ++ _)
        sumT <- complex("complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num m)) ((m * k) * r)) m")
        opened <- Rewrite.rewrite(set, sumT)
        family <- Parser.term(theory, notation,
          "\\y:num. complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num m)) (y * r)) m")
        congruent <- Conv.apTerm(family, instance).flatMap(Conv.betaSides)
        result <- Conv.trans(congruent, opened)
        out <- rules.existsElim(exists, k, result)
        closed <- rules.disch(hT, out).flatMap(rules.genAll(_, List(m, h)))
      } yield closed
    }

    private def sumNotDivides(mine: Map[String, Kernel.Thm], driver: Driver): Either[LogicError, Kernel.Thm] = {
      val m = Term.variable("m", Numbers)
      val h = Term.variable("h", Numbers)
      val k = Term.variable("k", Numbers)
      val i = Term.variable("i", Numbers)
      for {
        hT <- proposition("0 < (m:num) /\\ ~NUM_DIVIDES m h")
        assumed <- assume(hT)
        positive <- rules.conjElim1(assumed)
        notDivides <- rules.conjElim2(assumed)
        atM <- rules.spec(m, mine("ROOT_OF_UNITY")).flatMap(rules.mp(_, positive))
        w <- complex("cis (2 * pi / real_of_num m)")
        v <- complex("complex_pow (cis (2 * pi / real_of_num m)) h")
        powW <- constant(Power, Type.fun(Complexes, Type.fun(Numbers, Complexes))).flatMap(c => LogicError.lift(Term.app(c, w)))

        // the sum is the geometric one at v = w^h
        powMul <- Rewrite.Rule.all(logic, Vector(mine("COMPLEX_POW_MUL")))
        sumT <- complex("complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num m)) (h * r)) m")
        regrouped <- Rewrite.rewrite(powMul, sumT)
        geometric <- rules.specAll(mine("COMPLEX_GEOMETRIC"), List(v, m))

        // v^m = 1, through w^(m h)
        vm <- for {
          a <- rules.specAll(mine("COMPLEX_POW_MUL"), List(w, h, m)).flatMap(Conv.sym)
          swapped <- fact("NUM_MUL_SYM").flatMap(rules.specAll(_, List(h, m))).flatMap(Conv.apTerm(powW, _))
          c <- rules.specAll(mine("COMPLEX_POW_MUL"), List(w, m, h)).flatMap(Limit.rewriteInProposition(atM, _))
          one <- rules.spec(h, mine("COMPLEX_POW_ONE"))
          out <- Conv.trans(a, swapped).flatMap(Conv.trans(_, c)).flatMap(Conv.trans(_, one))
        } yield out
        product <- Limit.rewriteInProposition(vm, geometric)
        oneMinusOne <- complex("complex_of_real 1 - complex_of_real 1")
        zero <- complex("complex_of_real 0")
        cancels <- driver.equation(oneMinusOne, zero)
        productZero <- Conv.trans(product, cancels)

        // v is not one: h = m k + i with 0 < i < m, so v = w^i = cis (i * 2 pi / m)
        division <- fact("NUM_DIVISION").flatMap(rules.specAll(_, List(m, h))).flatMap(rules.mp(_, positive))
        innerT <- proposition("?i:num. (h:num) = m * k + i /\\ i < m")
        inner <- assume(innerT)
        partsT <- proposition("(h:num) = m * k + i /\\ i < m")
        parts <- assume(partsT)
        hIs <- rules.conjElim1(parts)
        iBelow <- rules.conjElim2(parts)
        f <- proposition("F")
        iPositive <- {
          val goalT = proposition("0 < (i:num)")
          goalT.flatMap { goal =>
            for {
              zeroN <- Parser.term(theory, notation, "0", Numbers)
              total <- fact("NUM_LT_TOTAL").flatMap(rules.specAll(_, List(zeroN, i)))
              split <- logic.destDisj(total.conclusion).toRight(NotOfForm("a disjunction", total.conclusion))
              split2 <- logic.destDisj(split._2).toRight(NotOfForm("a disjunction", split._2))
              less <- assume(split._1)
              same <- for {
                e <- assume(split2._1)
                added <- Conv.sym(e).flatMap(Limit.rewriteInProposition(_, hIs))
                tidy <- fact("NUM_ADD_ZERO")
                plain <- Rewrite.Rule.all(logic, Vector(tidy)).flatMap(Rewrite.inTheorem(_, added))
                dividesNow <- fact("NUM_DIVIDES_INTRO").flatMap(rules.specAll(_, List(m, h, k))).flatMap(rules.mp(_, plain))
                absurd <- rules.notElim(notDivides, dividesNow)
                out <- rules.falsityElim(goal, absurd)
              } yield out
              more <- for {
                below <- assume(split2._2)
                never <- fact("NUM_NOT_LT_ZERO").flatMap(rules.spec(i, _))
                absurd <- rules.notElim(never, below)
                out <- rules.falsityElim(goal, absurd)
              } yield out
              innerCases <- assume(split._2).flatMap(rules.disjElim(_, same, more))
              out <- rules.disjElim(total, less, innerCases)
            } yield out
          }
        }

        // w^h = w^i
        reduced <- for {
          moved <- Conv.apTerm(powW, hIs)
          set <- Rewrite.Rule.all(logic, Vector(mine("COMPLEX_POW_ADD"), mine("COMPLEX_POW_MUL"), atM, mine("COMPLEX_POW_ONE")))
          opened <- rightOf(moved).flatMap(Rewrite.rewrite(set, _))
          wi <- complex("complex_pow (cis (2 * pi / real_of_num m)) i")
          left <- complex("complex_of_real 1 * complex_pow (cis (2 * pi / real_of_num m)) i")
          unit <- driver.equation(left, wi)
          out <- Conv.trans(moved, opened).flatMap(Conv.trans(_, unit))
        } yield out
        q <- real("2 * pi / real_of_num m")
        moivre <- rules.specAll(mine("DE_MOIVRE"), List(q, i))
        vIsCis <- Conv.trans(reduced, moivre)

        // 0 < i * (2 pi / m) < 2 pi
        theta <- for {
          ri <- real("real_of_num i")
          rm <- real("real_of_num m")
          riPositive <- positiveReal(i, iPositive)
          rmPositive <- positiveReal(m, positive)
          rmNonzero <- nonzero(rmPositive)
          gap <- fact("NUM_REAL_LT").flatMap(rules.specAll(_, List(i, m))).flatMap(rules.mp(_, iBelow))
          bounds <- fact("PI_BOUNDS")
          lt <- fact("LT_MUL")
          divisionDefinition <- fact(Real.Division)
          divRules <- Rewrite.Rule.all(logic, Vector(divisionDefinition))
          qIs <- Rewrite.rewrite(divRules, q)
          inverse <- realInv(rm)
          invPositive <- fact("INV_POSITIVE").flatMap(rules.spec(rm, _)).flatMap(rules.mp(_, rmPositive))
          twoPi <- real("2 * pi")
          twoPiPositive <- concludeText(Seq(bounds), "0 < 2 * pi")
          qPositiveInv <- rules.conjIntro(twoPiPositive, invPositive)
            .flatMap(both => rules.specAll(lt, List(twoPi, inverse)).flatMap(rules.mp(_, both)))
          qPositive <- Conv.sym(qIs).flatMap(Limit.rewriteInProposition(_, qPositiveInv))
          lower <- rules.conjIntro(riPositive, qPositive).flatMap(both => rules.specAll(lt, List(ri, q)).flatMap(rules.mp(_, both)))
          difference <- real("real_of_num m - real_of_num i")
          differencePositive <- concludeText(Seq(gap), "0 < real_of_num m - real_of_num i")
          rest <- rules.conjIntro(differencePositive, qPositive)
            .flatMap(both => rules.specAll(lt, List(difference, q)).flatMap(rules.mp(_, both)))
          split <- proposition(
            "(real_of_num m - real_of_num i) * (2 * pi / real_of_num m) = " +
              "2 * pi * (real_of_num m * inv (real_of_num m)) - real_of_num i * (2 * pi / real_of_num m)"
          ).flatMap(ring.prove)
          mulInverse <- fact("MUL_INVERSE").flatMap(rules.spec(rm, _)).flatMap(rules.mp(_, rmNonzero))
          splitOne <- Limit.rewriteInProposition(mulInverse, split)
          restOpened <- Limit.rewriteInProposition(splitOne, rest)
          // linear in the product, which is an atom to LINARITH once it is a variable
          schema <- proposition("!y:real. 0 < 2 * pi * 1 - y ==> y < 2 * pi").flatMap(linarith.prove)
          theta <- real("real_of_num i * (2 * pi / real_of_num m)")
          upper <- rules.spec(theta, schema).flatMap(rules.mp(_, restOpened))
          out <- rules.conjIntro(lower, upper)
        } yield out
        angle <- rightOf(moivre).flatMap {
          case App(_, angle) => Right(angle)
          case other => Left(NotOfForm("cis of an angle", other))
        }
        notOne <- rules.spec(angle, mine("CIS_NOT_ONE")).flatMap(rules.mp(_, theta))
        oneT <- proposition("complex_of_real 1 - complex_pow (cis (2 * pi / real_of_num m)) h = complex_of_real 0")
        notZero <- for {
          e <- assume(oneT)
          closing <- driver.from(e)
          one <- complex("complex_of_real 1")
          vOne <- closing.equation(v, one)
          cisOne <- Conv.sym(vIsCis).flatMap(Conv.trans(_, vOne))
          absurd <- rules.notElim(notOne, cisOne)
          out <- rules.notIntro(oneT, absurd)
        } yield out

        // so the sum vanishes
        summed <- rightOf(regrouped)
        factor <- Term.destEq(oneT).map(_._1).toRight(NotOfForm("an equation", oneT))
        alternatives <- rules.specAll(mine("COMPLEX_ENTIRE"), List(factor, summed)).flatMap(rules.mp(_, productZero))
        goal <- equal(summed, zero)
        sumZero <- for {
          firstCase <- logic.destDisj(alternatives.conclusion).toRight(NotOfForm("a disjunction", alternatives.conclusion))
          left <- assume(firstCase._1).flatMap(e => rules.notElim(notZero, e)).flatMap(rules.falsityElim(goal, _))
          right <- assume(firstCase._2)
          out <- rules.disjElim(alternatives, left, right)
        } yield out
        result <- Conv.trans(regrouped, sumZero)
        afterI <- rules.existsElim(inner, i, result)
        afterK <- rules.existsElim(division, k, afterI)
        out <- rules.disch(hT, afterK).flatMap(rules.genAll(_, List(m, h)))
      } yield out
    }
  }
}
