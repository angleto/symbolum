package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on the naturals: addition, multiplication, the order, and the map into the reals.
 *
 * `Natural` carves `num` out of an infinite type and derives Peano's axioms; what it leaves is a
 * type with zero, a successor, induction and a case split and **nothing to compute with**. Until
 * this file, `+`, `*`, `<=` and `<` existed over the reals and nowhere else, so an index written
 * as `i + 1` and a bound written as `i < n` could not be stated over the naturals: a development
 * that wanted either had to put its indices in the reals and say nothing about them being whole.
 *
 * This is Peano arithmetic in the usual sense, which is what the name says: the two operations and
 * the order over the type whose axioms `Natural` proved. The axioms are not here, and that boundary
 * is the reason for two files rather than one: nothing below is assumed, and nothing here is
 * either.
 *
 * == Everything is defined, and the two operations by recursion ==
 *
 * `NUM_ADD` and `NUM_MUL` are definitions built on `Recursion.theorem`, each recursing on its
 * **second** argument:
 *
 * {{{
 *   |- !m. NUM_ADD m ZERO = m           |- !m. NUM_MUL m ZERO = ZERO
 *   |- !m n. NUM_ADD m (SUC n) = SUC (NUM_ADD m n)
 *   |- !m n. NUM_MUL m (SUC n) = NUM_ADD (NUM_MUL m n) m
 * }}}
 *
 * The second argument rather than the first, and it is not a free choice. HOL Light recurses
 * addition on the first; both orientations were worked out step by step before either was written,
 * and on that one the step of right distributivity comes out as `(m * p + p) + n * p` against
 * `m * p + (n * p + p)`, which differ by a commutation, so the sums have to be sorted before they
 * meet. Recursing on the second argument makes distributivity, the associativity of both
 * operations and the unit laws close by rewriting alone, and pushes the one step that needs sorting
 * down to a single lemma, [[Peano.SuccessorTimes]]. That the sorting is load-bearing there and
 * nowhere else is checked by `PeanoSpec` rather than claimed here: the same induction refuses
 * without it, and the refusal prints the two forms that did not meet.
 *
 * `NUM_LE` is the existential a reader would write, and `NUM_LT` is one successor along it:
 *
 * {{{
 *   NUM_LE m n  =  ?d. NUM_ADD m d = n
 *   NUM_LT m n  =  NUM_LE (SUC m) n
 * }}}
 *
 * Defining `<` through `<=` rather than as `m <= n /\ ~(m = n)` is what makes `m < SUC m`
 * reflexivity rather than a second induction, and it is what lets one function decide a bound
 * either way: a gap of `ZERO` is an equation and a gap of `SUC j` is the strict order, which is
 * what `splitOnGap` below does and where trichotomy comes from.
 *
 * `real_of_num` is the last definition and the reason the rest is worth having: an index over `num`
 * meets the arithmetic `Ring` and `Linarith` decide only through it. It is a homomorphism for both
 * operations, and both halves are proved rather than assumed.
 *
 * **And for the order, since 2026-09-11**, which is the half that makes the embedding usable rather
 * than merely present. Until then a development could carry an index into the reals and know
 * nothing about it there: `real_of_num i` is an atom to `LINARITH`, and an atom with no fact
 * attached is an unknown real. A claim about an index nearly always carries a bound on it, and the
 * bound was a fact about `num` that nothing over the reals could read. [[Peano.EmbedsNonNegative]],
 * [[Peano.EmbedsOrder]] and [[Peano.EmbedsStrictOrder]] are the three that carry it across, and the
 * last of them carries the **integrality** with it: `i < k` over the naturals becomes
 * `real_of_num i + 1 <= real_of_num k` and not merely `<`, because there is nothing between a
 * natural and its successor and that is the one place the fact is worth anything.
 *
 * == The subtraction here is truncated, and a reader who forgets that will write a false lemma ==
 *
 * `PRE` and `NUM_SUB` are the last two definitions, by the same recursion as the rest:
 *
 * {{{
 *   |- PRE ZERO = ZERO                  |- !m. NUM_SUB m ZERO = m
 *   |- !n. PRE (SUC n) = n              |- !m n. NUM_SUB m (SUC n) = PRE (NUM_SUB m n)
 * }}}
 *
 * `num` is closed under neither, and the two equations above are how a **total** function on it is
 * made to look like one that is not. `PRE ZERO` is `ZERO` because a recursion has to say what it
 * does at zero and there is no number below it, and `NUM_SUB` inherits that one step at a time:
 * subtracting past the bottom stops there rather than going anywhere. So `NUM_SUB m n` is `ZERO`
 * whenever `m <= n`, which [[Peano.SubIsZero]] states as a theorem rather than as a warning here,
 * and `NUM_SUB (NUM_ADD m n) n = m` ([[Peano.SumMinus]]) holds with no hypothesis while its
 * converse [[Peano.MinusThenPlus]] needs one.
 *
 * **That hypothesis is the thing to carry away.** `NUM_ADD (NUM_SUB m n) n = m` is false at
 * `m = ZERO, n = SUC ZERO`, and so is `real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n`:
 * the left side is `0` and the right is `-1`. Both are stated under `NUM_LE n m` and are false
 * without it, which is why neither is written the way a reader expecting the integers would write
 * it. `SubtractionSpec` puts the two counterexamples to the kernel rather than leaving them here.
 *
 * [[Peano.EmbedsDifference]] is the one that pays for the rest, for the reason the order lemmas
 * above pay for themselves: a difference of two indices is an index, and until it can be written as
 * a difference of two reals it is an atom that `RING` and `LINARITH` know nothing about.
 *
 * == What it does not cover ==
 *
 * **Division with a remainder and the numerals were both missing, and neither is now.** The
 * remainder went to `Modular`, where divisibility on `num` lives. The numerals are declared below,
 * since 2026-09-12: `NUM_ONE`, `NUM_BIT0` and `NUM_BIT1`, all defined, no axiom. What a consumer
 * meets instead is the seam between the two spellings, and it is worth knowing before writing a
 * statement: `2` is `NUM_BIT0 NUM_ONE` and every recurrence in this file is stated at `SUC n`, so
 * a number written as a numeral hooks none of them until `Successor` opens it.
 *
 * **No definition by well-founded recursion.** The least-number principle is here since
 * 2026-09-11, [[Peano.LeastNumber]], and it is what an argument by descent needs; what is still not
 * here is a definition that recurses on it, which needs more than the principle: a recursion
 * theorem for a well-founded relation, in the shape `Recursion.theorem` has for the successor.
 *
 * **Four of the operations are written infix, and three deliberately are not.** [[Peano.Addition]],
 * [[Peano.Multiplication]], [[Peano.StrictOrder]] and [[Peano.NonStrictOrder]] are read and printed
 * `+`, `*`, `<` and `<=`, the reals' own marks at the reals' own precedences, which `docs/adr/0018`
 * decided and this file declares in its numerals stage: a symbol stands for more than one constant
 * and the elaborator picks by the type unification settles. [[Peano.Subtraction]] and `NUM_DIV`
 * keep spellings of their own because they are not the operations `-` and `/` name over a field,
 * which is the section below this one; `NUM_POW` keeps its own because it does not share a shape
 * with `Power`, whose base is a real.
 *
 * **The numerals were the exception, and the exception turned out to be the rule.** Since
 * 2026-09-12 this development declares a second numeral encoding and a digit string reads at
 * either type, and what stood here was a reason that could not extend to the operators: `+` would
 * have to be resolved by the types of its arguments **before** those types are known, since they
 * are what the operator is being applied to. That sentence described resolving eagerly, which is
 * not what the numerals do either. A numeral takes a metavariable, unification runs, and the
 * encoding is read back afterwards; an operator whose candidates share a shape, `t -> t -> t` for
 * `+` and `t -> t -> bool` for `<=`, is deferred the same way. `docs/adr/0018` carries the
 * measurement, and [[Peano.NumeralOne]] carries the rest.
 *
 * **Nothing here is a decision procedure.** Every fact below is a theorem, and a goal that is an
 * instance of one is closed by the rewriter or by hand. `Ring` decides the reals and there is no
 * counterpart for `num`; what there is instead is `real_of_num`, which carries a goal over to the
 * side that has one.
 */
final class Peano private (
  val naturals: Natural,
  val ring: Ring,
  val theory: Theory,
  val notation: Notation,
  /**
   * The connectives, read against **this** signature rather than a narrower one.
   *
   * Held rather than rebuilt because a rule that has to construct a quantifier asks a theory for
   * the quantifier at that type, and the logic a consumer is likeliest to have to hand is the one
   * over the reals, which has never heard of `num`. `Chain` exposes its own for the same reason.
   */
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The reals this development embeds the naturals into. */
  val reals: RealTheory = ring.reals

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /**
   * The three lemmas that carry a numeral of `num` across `real_of_num`, as one named set.
   *
   * A rewrite with these takes `real_of_num` through every bit of a numeral and lands on the real
   * numeral with the same digits: [[Peano.EmbedsNumeralBit0]] and [[Peano.EmbedsNumeralBit1]] step
   * through the chain and [[Peano.EmbedsNumeralOne]] closes it. `ZERO` needs no entry, since
   * [[Peano.EmbedsZero]] already carries it and is not specific to the encoding.
   *
   * **It is a named set rather than three lemmas a caller collects, and that is the point of the
   * method.** The consumer that asked for numerals on `num` was offered the tactic and declined it,
   * correctly, for having no consumer yet; what it asked for instead was this, so that the first
   * caller does not assemble a rule set of its own and the second does not assemble a different
   * one. `Series.EmbeddingStatements` is the same argument one floor up.
   *
   * What it does not do: it is a rule set and not a tactic. Nothing applies it for you, and a goal
   * mixing a numeral with arithmetic still needs the rewrite driven and then closed.
   */
  def numeralsCrossing: Either[LogicError, Vector[Kernel.Thm]] =
    Vector(
      Peano.EmbedsNumeralBit0,
      Peano.EmbedsNumeralBit1,
      Peano.EmbedsNumeralOne
    ).foldLeft(Right(Vector.empty): Either[LogicError, Vector[Kernel.Thm]]) { (acc, name) =>
      for {
        collected <- acc
        theorem <- fact(name)
      } yield collected :+ theorem
    }

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

}

object Peano {

  /* ------------------------------------------------------------------- names */

  /** `NUM_ADD m n` is `m + n`, recursing on `n`. */
  val Addition: String = "NUM_ADD"

  /** `NUM_MUL m n` is `m * n`, recursing on `n`. */
  val Multiplication: String = "NUM_MUL"

  /** `NUM_LE m n` is `?d. NUM_ADD m d = n`. */
  val NonStrictOrder: String = "NUM_LE"

  /** `NUM_LT m n` is `NUM_LE (SUC m) n`. */
  val StrictOrder: String = "NUM_LT"

  /** The embedding into the reals, by which an index meets the arithmetic the tactics decide. */
  val EmbeddingName: String = "real_of_num"

  /**
   * `PRE n` is the number below `n`, and `PRE ZERO` is `ZERO`.
   *
   * Named `PRE` and not `NUM_PRE`, which is the question `docs/naming.md` leaves open for a new
   * constant and answers by pointing at its neighbours: the naturals prefix the operations they
   * share a name with over the reals, `NUM_ADD` against `+` and `NUM_LE` against `<=`, and leave
   * unprefixed the ones nothing else has. `SUC` is unprefixed for that reason and this is its
   * partner. The **facts** about it carry `NUM_` like every other fact here, exactly as `SUC`'s do.
   */
  val Predecessor: String = "PRE"

  /**
   * `NUM_SUB m n` is `m - n` truncated at zero, recursing on `n`.
   *
   * Prefixed where `PRE` is not, by the same reading: the reals own a `sub` and this is not it.
   */
  val Subtraction: String = "NUM_SUB"

  /** `|- !m. NUM_ADD m ZERO = m`, the first of addition's two recurrences. */
  val AddAtZero: String = "NUM_ADD_ZERO"

  /** `|- !m n. NUM_ADD m (SUC n) = SUC (NUM_ADD m n)`, the second. */
  val AddAtSuccessor: String = "NUM_ADD_SUC"

  /** `|- !n. NUM_ADD ZERO n = n`, which is the first recurrence read from the other side. */
  val ZeroPlus: String = "NUM_ZERO_ADD"

  /** `|- !m n. NUM_ADD (SUC m) n = SUC (NUM_ADD m n)`, the lemma commutativity needs. */
  val SuccessorPlus: String = "NUM_SUC_ADD"

  /** `|- !m n p. NUM_ADD (NUM_ADD m n) p = NUM_ADD m (NUM_ADD n p)` */
  val AddAssociative: String = "NUM_ADD_ASSOC"

  /** `|- !m n. NUM_ADD m n = NUM_ADD n m` */
  val AddCommutative: String = "NUM_ADD_SYM"

  /** `|- !m n p. NUM_ADD m (NUM_ADD n p) = NUM_ADD n (NUM_ADD m p)`, which sorts a sum. */
  val AddExchange: String = "NUM_ADD_EXCHANGE"

  /**
   * `|- !m n. NUM_ADD m (SUC n) = NUM_ADD (SUC m) n`, which moves a successor across a sum.
   *
   * The lemma the order is decided by, and the only place it is used: a difference of `SUC j`
   * between two numbers is a difference of `j` between the successor of the first and the second,
   * which is exactly the step from `m <= n` to `m < n`.
   */
  val Shift: String = "NUM_ADD_SHIFT"

  /** `|- !m. NUM_MUL m ZERO = ZERO`, the first of multiplication's two recurrences. */
  val MulAtZero: String = "NUM_MUL_ZERO"

  /** `|- !m n. NUM_MUL m (SUC n) = NUM_ADD (NUM_MUL m n) m`, the second. */
  val MulAtSuccessor: String = "NUM_MUL_SUC"

  /** `|- !n. NUM_MUL ZERO n = ZERO` */
  val ZeroTimes: String = "NUM_ZERO_MUL"

  /**
   * `|- !n. NUM_MUL n (SUC ZERO) = n`, the unit in the spelling the recurrences produce.
   *
   * Not `NUM_ONE`, which is a different term with the same value: a lemma stated at the numeral
   * would hook nothing the recurrences build. [[NumeralOneIsSuccessorOfZero]] is the bridge and
   * `Successor` is what walks it for a caller holding the other spelling.
   */
  val TimesOne: String = "NUM_MUL_ONE"

  /** `|- !m n p. NUM_MUL m (NUM_ADD n p) = NUM_ADD (NUM_MUL m n) (NUM_MUL m p)` */
  val Distributive: String = "NUM_MUL_DISTRIBUTE"

  /** `|- !m n p. NUM_MUL (NUM_MUL m n) p = NUM_MUL m (NUM_MUL n p)` */
  val MulAssociative: String = "NUM_MUL_ASSOC"

  /** `|- !m n. NUM_MUL (SUC m) n = NUM_ADD (NUM_MUL m n) n`, the one step that needs sorting. */
  val SuccessorTimes: String = "NUM_SUC_MUL"

  /** `|- !m n. NUM_MUL m n = NUM_MUL n m` */
  val MulCommutative: String = "NUM_MUL_SYM"

  /** `NUM_POW m n` is `m^n`, recursing on `n` exactly as [[Multiplication]] does. */
  val Exponentiation: String = "NUM_POW"

  /** `|- !m. NUM_POW m ZERO = SUC ZERO`, the first of exponentiation's two recurrences. */
  val PowAtZero: String = "NUM_POW_ZERO"

  /** `|- !m n. NUM_POW m (SUC n) = NUM_MUL (NUM_POW m n) m`, the second. */
  val PowAtSuccessor: String = "NUM_POW_SUC"

  /**
   * `|- !m n p. NUM_POW m (NUM_ADD n p) = NUM_MUL (NUM_POW m n) (NUM_POW m p)`
   *
   * The law every consumer of a power actually reaches for, and the reason this development
   * exists at all rather than callers writing `NUM_MUL` chains: an exponent that is a sum is
   * what an induction produces, and without this it cannot be taken apart.
   */
  val PowAddsExponents: String = "NUM_POW_ADD"

  /** `|- !n. NUM_POW (SUC ZERO) n = SUC ZERO`, the unit base. */
  val OneToAnyPower: String = "NUM_POW_ONE"

  /**
   * `|- !m n. NUM_LT ZERO m ==> NUM_LT ZERO (NUM_POW m n)`
   *
   * A positive base stays positive at every exponent, which every other operation here has had
   * since the order landed and exponentiation has not: `NUM_MUL_POSITIVE` is beside it and
   * `NUM_POW` had nothing. The side condition cannot go, since `NUM_POW ZERO (SUC n)` is zero,
   * and it is not needed at the exponent zero, where the value is one whatever the base.
   *
   * **It is derived after the order and not with the other three**, which is the only thing
   * about it worth a sentence. [[exponentiation]] runs before [[order]], deliberately, because
   * nothing in the order knows about powers; so this cannot be proved there, and the order block
   * is not given the power recurrences. One induction with the two of them in one place is what
   * it costs, and the place is the assembly.
   *
   * Its first consumer is [[Modular.PrimePowCancel]], whose step cancels a power of the prime
   * off an equation and needs it non-zero to do so.
   */
  val PowPositive: String = "NUM_POW_POSITIVE"

  /**
   * `|- !m. NUM_MUL m (SUC (SUC ZERO)) = NUM_ADD m m`
   *
   * Doubling, written once. A two is `SUC (SUC ZERO)` here rather than `2`, because that is the
   * spelling multiplication's own recurrence produces and a statement written at the numeral would
   * hook nothing; a caller who wants `2n = n + n` either writes this out or unfolds multiplication
   * twice at the site.
   * With [[PowAtSuccessor]] it is also what says `2^(n+1) = 2^n + 2^n`, which is the shape any
   * argument that splits a range in half needs.
   */
  val TimesTwo: String = "NUM_MUL_TWO"

  /** `|- !n m. NUM_ADD m n = m ==> n = ZERO`, cancellation, and the order rests on it. */
  val AddCancels: String = "NUM_ADD_CANCEL"

  /**
   * `|- !x y a. NUM_ADD a x = NUM_ADD a y ==> x = y`
   *
   * Cancellation proper, where [[AddCancels]] is the special case at `y = ZERO`. It was not here
   * until 2026-09-11 and the gap showed where such gaps always show: `Modular.DivisionUnique`
   * cannot take a step without it, and neither can anything else that reads two decompositions of
   * one number against each other.
   *
   * Quantified `!x y a.` rather than `!a x y.`, which a reader would not choose, for the reason
   * [[AddCancels]] gives in the same words: the induction is on `a` and the driver inducts on the
   * **last** quantifier of the statement it is given.
   */
  val AddCancelsLeft: String = "NUM_ADD_CANCEL_LEFT"

  /** `|- !m n. NUM_ADD m n = ZERO ==> m = ZERO` */
  val SumIsZero: String = "NUM_ADD_EQ_ZERO"

  /** `|- !n. NUM_LE n n` */
  val Reflexive: String = "NUM_LE_REFL"

  /** `|- !n. NUM_LE ZERO n` */
  val ZeroIsLeast: String = "NUM_ZERO_LE"

  /** `|- !n. NUM_LE n (SUC n)` */
  val AtMostSuccessor: String = "NUM_LE_SUC"

  /** `|- !m n p. NUM_LE m n /\ NUM_LE n p ==> NUM_LE m p` */
  val Transitive: String = "NUM_LE_TRANS"

  /**
   * `|- !m n. NUM_LE m n /\ NUM_LE n m ==> m = n`
   *
   * The step that makes a bounded quantification usable: a claim proved for every `i <= n` and for
   * every `n <= i` is a claim about `i = n`, and without this it is two claims that never meet.
   */
  val AntiSymmetric: String = "NUM_LE_ANTISYM"

  /** `|- !n. NUM_LT n (SUC n)` */
  val BelowSuccessor: String = "NUM_LT_SUC"

  /** `|- !m n. NUM_LE m n \/ NUM_LE n m`, the order is total. */
  val Total: String = "NUM_LE_TOTAL"

  /**
   * `|- !m n. NUM_LT m n \/ m = n \/ NUM_LT n m`
   *
   * Trichotomy, which is what makes a case analysis on two numbers exhaustive. The reals have it
   * as an axiom (`LT_TOTAL`); here it is a theorem, and it is the deepest one in the file: the
   * order is shown total by an induction, and then each half is split on whether its witness is
   * zero.
   */
  val Trichotomy: String = "NUM_LT_TOTAL"

  /**
   * `|- !n. ~(SUC n = n)`
   *
   * Not one of Peano's axioms and not a corollary of the successor's injectivity.
   * `NUM_SUC_NOT_ZERO` is about zero and this is about every number, and the step from one to the
   * other goes through [[AddCancels]]: `n + SUC ZERO = SUC n`, so a number equal to its own
   * successor is a number to which `SUC ZERO` may be added without changing it.
   */
  val SuccessorNotSelf: String = "NUM_SUC_NOT_SELF"

  /** `|- !n. ~(NUM_LT n n)`, from [[AntiSymmetric]] and [[SuccessorNotSelf]]. */
  val StrictIrreflexive: String = "NUM_LT_IRREFL"

  /**
   * `|- !m n p. NUM_LT m n /\ NUM_LT n p ==> NUM_LT m p`
   *
   * Transitivity of the STRICT order, which the non-strict one had and this did not. It is two
   * steps of [[Transitive]] once `NUM_LT m n` is read as what it is defined to be,
   * `NUM_LE (SUC m) n`: from `SUC m <= n`, `n <= SUC n` and `SUC n <= p`, transitivity twice.
   *
   * It was missing until 2026-09-12 and the consumer that found it wanted the one-step
   * corollary `m < n ==> m < SUC n`, which is this with [[BelowSuccessor]]: a bounded induction
   * whose hypothesis quantifies over the indices below `n` has to re-derive that hypothesis at
   * `n` from the one at `SUC n`, and there was no lemma that did it.
   */
  val StrictTransitive: String = "NUM_LT_TRANS"

  /**
   * `|- !n. NUM_LT ZERO (SUC n)`
   *
   * The strict counterpart of [[ZeroIsLeast]], and the fact a consumer needs to discharge a
   * hypothesis of the form `NUM_LT ZERO n`. A concrete modulus or bound is written as a successor
   * here, since that is the spelling the order's lemmas are stated in, and until this lemma existed
   * nothing outside a development could
   * produce that hypothesis at all: a lemma whose guard nobody can discharge is a lemma nobody can
   * use. `ModularSpec` checks it by using it rather than by saying so.
   */
  val SuccessorPositive: String = "NUM_ZERO_LT_SUC"

  /**
   * `|- !m n. NUM_LT ZERO m ==> NUM_LT ZERO n ==> NUM_LT ZERO (NUM_MUL m n)`
   *
   * A product of positives is positive, which this file did not hold until 2026-09-14 and which is
   * the ordinary shape of a gap here: the multiplication facts are about multiplication and the
   * order facts are about the order, and nothing had needed a statement that is about both.
   *
   * It is proved by making the product a **successor** rather than by any argument about order.
   * Both factors are successors, because a positive number is, and then `NUM_MUL_SUC` and
   * `NUM_ADD_SUC` between them put the successor on the outside; [[SuccessorPositive]] does the
   * rest. There is no cancellation and no case on the order anywhere in it.
   */
  val MulPositive: String = "NUM_MUL_POSITIVE"

  /**
   * `|- !m n. NUM_LE m n ==> NUM_LT m n \/ m = n`
   *
   * [[splitOnGap]] as a disjunction, which is the same argument and is derived from it rather than
   * beside it: a gap of `ZERO` is an equation and a gap of `SUC j` is the strict order. The private
   * function stays because both its callers build something of their own out of each half and would
   * otherwise take the disjunction apart again; this is what a caller that is **not** building both
   * halves wants.
   */
  val BelowOrEqual: String = "NUM_LE_CASES"

  /** `|- !i. ~(NUM_LT i ZERO)`, nothing is below zero. */
  val NotBelowZero: String = "NUM_NOT_LT_ZERO"

  /**
   * `|- !m n. NUM_LT m n ==> NUM_LE m n`
   *
   * One step of transitivity through [[AtMostSuccessor]], and the `_OF_X` name `docs/naming.md`
   * gives as its own example of the convention. It is the lemma every case analysis that ends in a
   * non-strict bound needs, and there was none until 2026-09-11: the two orders were related only
   * by the definition, which turns `NUM_LT m n` into `NUM_LE (SUC m) n` and moves the successor to
   * the wrong side.
   */
  val AtMostFromBelow: String = "NUM_LE_OF_LT"

  /**
   * `|- !m n p. NUM_LE m n /\ NUM_LT n p ==> NUM_LT m p`
   *
   * The transitivity that mixes the two orders, which neither [[Transitive]] nor
   * [[StrictTransitive]] covers and which a reader assumes is there. It was not until 2026-09-14,
   * and what found that is a consumer reaching for it twice in one derivation and having to build
   * the argument inline both times.
   *
   * Two lines and no induction: [[BelowOrEqual]] splits the non-strict half into a strict one and
   * an equation, the first goes through [[StrictTransitive]] and the second is a congruence.
   *
   * **The other mixing was recorded here as deliberately absent, and the sentence lasted an hour.**
   * It said `NUM_LT m n /\ NUM_LE n p ==> NUM_LT m p` was equally true and that nothing had wanted
   * it, so adding it would be a lemma no call site names. `Numbering`'s injectivity wanted it the
   * same morning, which is why [[BelowThenAtMost]] is beside this one. The claim was true when it
   * was written and it was a claim about the **future**, which is the kind this file should not
   * make: "nothing wants it yet" is a measurement and "nothing will" is not.
   */
  val AtMostThenBelow: String = "NUM_LE_LT_TRANS"

  /**
   * `|- !m n p. NUM_LT m n /\ NUM_LE n p ==> NUM_LT m p`
   *
   * The other mixing, and it is not [[AtMostThenBelow]] turned round: that one splits the
   * non-strict half into two cases, and this one needs no split at all. [[StrictOrder]] is defined
   * as `NUM_LE (SUC m) n`, so the premise **is** `SUC m <= n`, and [[Transitive]] against `n <= p`
   * gives `SUC m <= p`, which is the conclusion with the constant folded back.
   */
  val BelowThenAtMost: String = "NUM_LT_LE_TRANS"

  /**
   * `|- !P. (!n. (!m. NUM_LT m n ==> P m) ==> P n) ==> (!n. P n)`
   *
   * Course-of-values induction: to prove a claim at `n` you may assume it at every smaller number.
   * What [[Natural.Induction]] is to a recursion on the predecessor, this is to a recursion on
   * anything smaller, which is what `Descent` builds and what every function over coded syntax uses.
   * Its consumers are one level up: a claim about a term's code is proved from the same claim about
   * the codes inside it, and those are smaller numbers rather than predecessors.
   *
   * **It is derived without the least number principle and without any classical step**, which is
   * not the usual route and is worth the sentence. The usual one supposes the claim fails
   * somewhere, takes a least counterexample by [[LeastNumber]], and contradicts the hypothesis;
   * that needs "not everywhere" to give "somewhere not", which is classical. Instead the ordinary
   * induction is run over `!m. NUM_LT m n ==> P m`, whose base is that nothing is below zero and
   * whose step is [[BelowSuccessorCases]], and the conclusion is read off at `SUC n`.
   */
  val StrongInduction: String = "NUM_STRONG_INDUCTION"

  /**
   * `|- !p m n. NUM_LE m n ==> NUM_LE (NUM_ADD p m) (NUM_ADD p n)`
   *
   * Addition preserves the order, which is the second thing a reader assumes is here and was not.
   * `MONOTONE` rather than a new spelling, because `POWER_MONOTONE` and `SUM_MONOTONE` already use
   * it and `docs/naming.md` allows one spelling per concept.
   *
   * It is three lines, and the reason is what [[NonStrictOrder]] is defined as: `NUM_LE m n` is
   * `?d. m + d = n`, so the witness that makes the premise true is the witness that makes the
   * conclusion true, and what happens in between is one associativity.
   */
  val AddMonotone: String = "NUM_ADD_MONOTONE"

  /**
   * `|- !p m n. NUM_LT m n ==> NUM_LT (NUM_ADD p m) (NUM_ADD p n)`
   *
   * [[AddMonotone]] for the strict order, and a consequence of it rather than a second induction:
   * shifting keeps `NUM_LE`, and the two sides cannot become equal because addition cancels on the
   * left. The first consumer is `Provability`, where a derivation's steps are moved along a
   * sequence and every bound on an earlier step has to move with them.
   */
  val AddStrictlyMonotone: String = "NUM_ADD_LT_MONOTONE"

  /**
   * `|- !m n. NUM_LT m n ==> ~(NUM_LE n m)`
   *
   * The two orders disagreeing, which is the thing a case split on `NUM_LE m n \/ NUM_LE n m`
   * needs in order to be a case split rather than two overlapping cases. Derived: `n <= m` with
   * `m < n` gives `n < n` through [[AtMostThenBelow]], and nothing is below itself.
   */
  val BelowExcludesAtMost: String = "NUM_LT_NOT_LE"

  /**
   * `|- !m n. NUM_LE m (NUM_ADD m n)`
   *
   * A summand is at most the sum, which on `num` holds with no side condition because there are no
   * negative numbers. It is [[AddMonotone]] at zero, and the only reason it is a lemma is that
   * placing an index inside a concatenated sequence asks for it four times.
   */
  val AtMostSum: String = "NUM_LE_ADD"

  /**
   * `|- !a b c d. NUM_LE a b /\ NUM_LE c d ==> NUM_LE (NUM_ADD a c) (NUM_ADD b d)`
   *
   * [[AddMonotone]] on both summands at once, which is what a sum of two blocks needs and what a
   * caller could assemble only by commuting twice. Derived rather than induced: the one-sided
   * lemma twice with [[AddCommutative]] between them and [[Transitive]] at the end.
   *
   * What asked for it is a tally over a word split into blocks, where a bound on each block's own
   * sum has to become a bound on the sum of the two.
   */
  val AddMonotoneBoth: String = "NUM_ADD_LE_BOTH"

  /**
   * `|- !p m n. NUM_LE (NUM_ADD p m) (NUM_ADD p n) ==> NUM_LE m n`
   *
   * [[AddMonotone]] read backwards, and the only one of the pair a consumer could not assemble
   * from what was here: `NUM_ADD_CANCEL_LEFT` cancels a summand out of an **equation** and there
   * was nothing that cancelled one out of a comparison.
   *
   * It is the same three lines as [[AddMonotone]] and for the same reason, which is what
   * [[NonStrictOrder]] is: `NUM_LE m n` is `?d. m + d = n`, so the witness the premise carries is
   * the witness the conclusion wants and the summand comes off by the equational cancellation in
   * between. The route through [[Trichotomy]] and [[BelowExcludesAtMost]] reaches the same place
   * and is longer, and it makes a classical case split out of a statement about a difference.
   *
   * The first consumer is `Provability`, where two derivations are concatenated: an index `j`
   * inside the second block is `c + (j - c)`, and what says the part after the shift is within
   * that block's own bound is this lemma against the bound on `j`.
   */
  val AddCancelsOrder: String = "NUM_ADD_LE_CANCEL"

  /**
   * `|- !p m n. NUM_LT (NUM_ADD p m) (NUM_ADD p n) ==> NUM_LT m n`
   *
   * [[AddCancelsOrder]] for the strict order, and it is three lines rather than a second induction
   * because of what [[StrictOrder]] is: `NUM_LT m n` is `NUM_LE (SUC m) n`, and `SUC (p + m)` is
   * `p + SUC m` by [[AddAtSuccessor]] read backwards. So the premise is the non-strict comparison
   * at `SUC m`, the summand comes off by [[AddCancelsOrder]], and what is left is the definition
   * folded again.
   *
   * It was missing on 2026-09-16 and the pair was not: [[AddStrictlyMonotone]] had been proved the
   * day the order was written and nothing had ever needed to read it backwards. What needed it is
   * placing an index inside a concatenated word, where `k + j < k + m` is what says the index is
   * inside the second block.
   */
  val AddCancelsStrictOrder: String = "NUM_ADD_LT_CANCEL"

  /**
   * `|- !m n. ~(NUM_LT m n) ==> NUM_LE n m`
   *
   * The negation of one order turned into the other, which on a total order costs nothing
   * classical at all: [[Trichotomy]] puts the three cases on the table before anything is negated,
   * and the derivation is one disjunction elimination over them. `Order.LE_OF_NOT_LT` is the same
   * fact about the reals and says the same thing about its own cost.
   *
   * What it is for is every case split written as `i < k` against `~(i < k)`: the negative branch
   * has a negated strict comparison and every lemma about a difference wants a non-strict one.
   * Nothing had it until 2026-09-16, and until then such a branch either restated its own
   * trichotomy or was written the other way round to avoid needing one, which is what
   * [[Archimedean]] records doing.
   */
  val AtMostFromNotBelow: String = "NUM_LE_OF_NOT_LT"

  /**
   * `|- !p m n. NUM_LE m n ==> NUM_LE (NUM_MUL p m) (NUM_MUL p n)`
   *
   * [[AddMonotone]] for the other operation, and it costs the same three lines for the same reason:
   * `NUM_LE m n` is `?d. m + d = n`, so `p * n` is `p * m + p * d` by one distribution and the
   * difference the conclusion wants is `p * d`. **No side condition**, because `p` may be zero and
   * the conclusion is then `0 <= 0`.
   */
  val MulMonotone: String = "NUM_MUL_MONOTONE"

  /**
   * `|- !p m n. NUM_LT ZERO p ==> NUM_LT m n ==> NUM_LT (NUM_MUL p m) (NUM_MUL p n)`
   *
   * The same for the strict order, and here the side condition is real: at `p = ZERO` both sides
   * are zero and nothing is below itself.
   *
   * It is longer than its non-strict sibling and not by much. `NUM_LT m n` is `NUM_LE (SUC m) n`,
   * so the witness gives `p * n = p * SUC m + p * d`, and `NUM_MUL_SUC` turns the first summand
   * into `p * m + p`. What remains is to see `p` as `SUC c`, which the witness of `ZERO < p`
   * supplies, and then `p * m + SUC c` is `SUC (p * m) + c` by the two recurrences of addition.
   */
  val MulStrictlyMonotone: String = "NUM_MUL_LT_MONOTONE"

  /**
   * `|- !p m n. NUM_LT ZERO p ==> NUM_MUL p m = NUM_MUL p n ==> m = n`
   *
   * A positive factor cancels, which [[AddCancelsLeft]] does for addition with no side condition at
   * all. The condition cannot be dropped: `ZERO * m = ZERO * n` says nothing about `m` and `n`.
   *
   * Derived from [[MulStrictlyMonotone]] under trichotomy rather than by an induction of its own:
   * if the two differ then one is strictly below the other, the products are then strictly ordered,
   * and the assumed equation makes one of them strictly below itself.
   *
   * The first consumer is the irrationality of the square root of two, where the descent turns
   * `NUM_MUL 2 (NUM_MUL k k) = NUM_MUL 2 (NUM_MUL q q)` into the equation between the squares.
   */
  val MulCancelsLeft: String = "NUM_MUL_CANCEL_LEFT"

  /**
   * `|- !n. NUM_LE n ZERO ==> n = ZERO`
   *
   * The converse of [[ZeroIsLeast]] at the bottom of the order, and it is not the same statement:
   * that one says zero is below everything, this one says nothing but zero is below zero. One use
   * of [[SumIsZero]] under the existential the order unfolds to.
   */
  val AtMostZero: String = "NUM_LE_ZERO"

  /**
   * `|- !n i. NUM_LT i (SUC n) ==> NUM_LT i n \/ i = n`
   *
   * Peeling the top index off a range, which is a different question from the one trichotomy
   * answers: that compares two numbers and says which way they go. `Bounded` walks a bounded
   * universal one step at a time with this and nothing else, and it is the induction step of
   * [[LeastNumber]].
   *
   * Quantified `!n i.` rather than `!i n.`: the bound is what a caller holds fixed while the index
   * moves, so it is the argument that is specialised first.
   */
  val BelowSuccessorCases: String = "NUM_LT_SUC_CASES"

  /**
   * `|- !n i. NUM_LT i (SUC n) ==> NUM_LE i n`
   *
   * An index strictly inside a range of length `SUC n` is at most `n`, which is what an argument
   * under `Series.SUM_CONGRUENCE_BELOW` at that bound needs and what nothing here could reach
   * without a case split. [[BelowSuccessorCases]] gets to the same place through a disjunction
   * with an equation in one branch, which the caller then has to eliminate.
   *
   * Additively it has no branch at all: `NUM_LT i (SUC n)` **is** `?d. NUM_ADD (SUC i) d = SUC n`
   * and `NUM_LE i n` **is** `?d. NUM_ADD i d = n`, so the two existentials have the same witness
   * and what happens in between is [[SuccessorPlus]] and the injectivity of the successor.
   */
  val AtMostBelowSuccessor: String = "NUM_LE_OF_LT_SUC"

  /**
   * `|- !n i. NUM_LE i n ==> NUM_LE n (NUM_SUB (NUM_ADD n n) i)`
   *
   * Taking at most `n` away from `n + n` leaves at least `n`. It is what says the square of side
   * `n` sits inside the triangle of side `n + n`, which is the half of the Cauchy product's
   * sandwich that looked as though it needed a division: `2n - i >= n` for `i <= n` is the same
   * statement, and written with `NUM_ADD n n` it needs no `NUM_DIV` and no halving.
   *
   * Additively it has no case split. `NUM_LE i n` **is** `?d. NUM_ADD i d = n`, so `n + n` is
   * `i + (d + n)`; commuting once puts the `i` where [[SumMinus]] takes it off with nothing owed,
   * and what is left is `d + n`, which is at least `n` by [[AtMostSum]] and one more commutation.
   */
  val AtMostDoubleMinus: String = "NUM_LE_DOUBLE_SUB"

  /**
   * `|- !P:num->bool. (?n. P n) ==> (?m. P m /\ (!k. NUM_LT k m ==> ~(P k)))`
   *
   * The least-number principle: a property that holds somewhere holds first somewhere. The only
   * statement in this file that quantifies over a **predicate**, which this logic can say because
   * it is higher order by construction, and it is here rather than in `Natural` for the reason the
   * order lemmas above are: it is about `NUM_LT`, which `Natural` has never heard of.
   *
   * It is what turns an ordinary induction into a descent. `Natural` derives `NUM_INDUCTION` and
   * nothing that lets a proof say "take the smallest such", so every argument wanting a minimal
   * counterexample had to be rewritten as an induction on a bound first. `Modular`'s docstring
   * named it as the missing piece under both the uniqueness of division with remainder and a
   * greatest common divisor.
   */
  val LeastNumber: String = "NUM_LEAST"

  /**
   * `|- !P:num->bool. (?n. P n) /\ (?b. !k. P k ==> NUM_LE k b) ==>
   * (?m. P m /\ (!k. P k ==> NUM_LE k m))`
   *
   * The dual of [[LeastNumber]], and it is not symmetric with it: a non-empty set of naturals
   * always has a least element and has a greatest **only if it is bounded**, which is the second
   * hypothesis and the whole difference between the two.
   *
   * It is derived from [[LeastNumber]] rather than by a second induction, applied to "n is an upper
   * bound of `P`". The least upper bound is the greatest element, and the step that says so is a
   * proof by contradiction: an upper bound at which `P` fails is either `ZERO`, and then `P` fails
   * everywhere against the non-emptiness, or a successor, and then its predecessor is a smaller
   * upper bound, which the minimality forbids.
   *
   * What it is for: a greatest common divisor. `Modular.DividesBound` says a divisor of a non-zero
   * number is no larger than it, which is the bound this asks for, and the common divisors of a
   * pair are non-empty because one divides everything.
   */
  val GreatestBounded: String = "NUM_GREATEST"

  /** `|- real_of_num ZERO = 0` */
  val EmbedsZero: String = "NUM_REAL_ZERO"

  /** `|- !n. real_of_num (SUC n) = real_of_num n + 1` */
  val EmbedsSuccessor: String = "NUM_REAL_SUC"

  /** `|- !m n. real_of_num (NUM_ADD m n) = real_of_num m + real_of_num n` */
  val EmbedsSum: String = "NUM_REAL_ADD"

  /** `|- !m n. real_of_num (NUM_MUL m n) = real_of_num m * real_of_num n` */
  val EmbedsProduct: String = "NUM_REAL_MUL"

  /**
   * `|- !n. 0 <= real_of_num n`
   *
   * The first of the three that say the embedding respects the **order** and not only the two
   * operations, which it did not until 2026-09-11. Until then a development could carry an index
   * into the reals and then know nothing about it: `LINARITH` reads `real_of_num n` as an atom, and
   * an atom with no fact attached is an unknown real that may be anything.
   */
  val EmbedsNonNegative: String = "NUM_REAL_NONNEG"

  /**
   * `|- !m n. NUM_LE m n ==> real_of_num m <= real_of_num n`
   *
   * The order half of the homomorphism, and the one a consumer reaches for. A claim about an index
   * nearly always carries a bound on it, `i < k` or `m <= n`, and before this the bound was a fact
   * about `num` that no procedure over the reals could use. Now it crosses, and the arithmetic on
   * the other side is decided rather than assumed.
   *
   * Proved from the definition rather than by induction: `NUM_LE m n` **is** `?d. m + d = n`, so
   * embedding the witness equation with [[EmbedsSum]] gives `real_of_num m + real_of_num d` for
   * `real_of_num n`, and [[EmbedsNonNegative]] at the witness is the rest.
   */
  val EmbedsOrder: String = "NUM_REAL_LE"

  /**
   * `|- !m n. NUM_LT m n ==> real_of_num m + 1 <= real_of_num n`
   *
   * The strict order, and the shape it comes out in is the useful one rather than the pretty one.
   * `real_of_num m < real_of_num n` would be the obvious statement and is weaker: the naturals have
   * no room between `m` and `m + 1`, so a strict bound on them is a **gap of one** on the reals, and
   * that is what a procedure needs to close `i < k ==> real_of_num i + 1 <= real_of_num k`. Saying
   * only `<` would throw the integrality away at the border, which is the one place it is worth
   * anything.
   *
   * One line from [[EmbedsOrder]]: `NUM_LT m n` is `NUM_LE (SUC m) n` by definition, and
   * [[EmbedsSuccessor]] rewrites the left-hand side.
   */
  val EmbedsStrictOrder: String = "NUM_REAL_LT"

  /**
   * `|- !m n. real_of_num m <= real_of_num n ==> NUM_LE m n`
   *
   * [[EmbedsOrder]] read backwards, and what makes the embedding an order **map** rather than a
   * monotone function: together the two say a bound on the reals is a bound on the naturals, so a
   * fact reaching the reals can come home. Until 2026-09-18 only the outward half existed, which
   * is why `Inclusion.EmbedsOrder` one type up could not be stated: a biconditional at `int` wants
   * both directions at `num`, and the library held one.
   *
   * It is in the `NUM_REAL_` family and not spelled `NUM_LE_OF_REAL_LE`, which the `_OF_X` row of
   * `docs/naming.md` would also license. Counted on 2026-09-18 over `docs/lemmas.md`: of the
   * thirteen facts naming both `real_of_num` and a natural, thirteen carry the family prefix and
   * none is named for its conclusion's type, [[EmbedsInjectively]] and [[EmbedsDifference]]
   * included, and those two are the ones whose conclusion is at `num`. Thirteen to nothing.
   *
   * **The route is [[Trichotomy]] and not a contraposition**, which is the one the obvious reading
   * reaches for: from `~(NUM_LE m n)` to `NUM_LT n m` is [[AtMostFromNotBelow]] turned around, and
   * turning an implication around is a classical step this derivation would then owe. Trichotomy
   * puts the three cases on the table before anything is negated, which is the sentence
   * [[AtMostFromNotBelow]] already carries about itself. Two of the three cases are one line:
   * [[AtMostFromBelow]] and [[Reflexive]] under a congruence. The third is where the work is, and
   * it is [[EmbedsStrictOrder]] carrying the **integrality**, exactly as [[EmbedsInjectively]]
   * does: `NUM_LT n m` puts a whole unit between the two images, which the assumed bound forbids.
   */
  val EmbedsOrderBack: String = "NUM_REAL_LE_BACK"

  /**
   * `|- !m n. real_of_num m = real_of_num n ==> m = n`
   *
   * The embedding in the other direction, and the lemma that makes it usable as more than a
   * one-way trip: without it a fact proved about `real_of_num l` and `real_of_num r` stays a fact
   * about the reals. It rests on [[EmbedsStrictOrder]] carrying the **integrality**: two distinct
   * naturals are a whole unit apart on the reals, so their images cannot coincide, which is what
   * makes this provable rather than merely plausible.
   *
   * `Modular.identity` is what it was wanted for: an equation between naturals is decided by
   * embedding both sides, letting `RING` close it over the reals, and coming back across this. That
   * is the arrangement `docs/adr/0003` describes one level down, and it stands in for the `RING`
   * this side does not have.
   */
  val EmbedsInjectively: String = "NUM_REAL_INJECTIVE"

  /**
   * `|- !x:real. ?y:num. x < real_of_num y`: no real is above every natural.
   *
   * **The first thing in this repository that uses `COMPLETENESS`.** The sixteen axioms of the
   * reals have been in `Real.scala` since the beginning and fifteen of them have been worked; the
   * sixteenth had never been read by anything, which is a fact about the development rather than
   * about the axiom, and it is the one that separates an ordered field from the reals.
   *
   * == Why it has to be proved rather than assumed, and why it is not obvious ==
   *
   * An ordered field need not be Archimedean: the rational functions ordered by behaviour at
   * infinity are a counterexample, and there `x` is above every natural. So this is not a fact
   * about order and arithmetic that was waiting to be written down; it is where the completeness
   * of the reals is spent, and no amount of `LINARITH` reaches it.
   *
   * The argument is the standard one and its shape is worth keeping in view, because the step a
   * reader expects is the one that is not here. Suppose some `y` is above every natural. Then the
   * image of `num` is non-empty and bounded, so `COMPLETENESS` gives it a least upper bound `s`.
   * Now `s - 1` is an upper bound **as well**: every natural `n` has a successor in the image, so
   * `real_of_num n + 1 <= s` by [[EmbedsSuccessor]], so `real_of_num n <= s - 1`. Leastness then
   * gives `s <= s - 1`, which `LINARITH` turns into falsity.
   *
   * **No negated universal is pushed through a quantifier anywhere in it**, and until 2026-09-15
   * that was what made it writable at all: this logic had De Morgan for the connectives and
   * nothing for the quantifiers, and the textbook phrasing, "`s - 1` is not an upper bound, so
   * take a natural above it", needs exactly that. [[garden.xeno.symbolum.logic.Classical.NotForall]]
   * exists now, so the obstacle is gone and the route is kept anyway: showing that `s - 1` *is* an
   * upper bound is the same argument with one fewer lemma in it, and nothing has measured the
   * alternative.
   *
   * What is classical about it is one thing and it is named: the conclusion is reached by
   * `Classical.contradiction` from the assumption that no natural passes `y`. That is the choice
   * axiom's bill, through the excluded middle, and it is the same bill `Natural` already pays.
   */
  val Archimedean: String = "NUM_ARCHIMEDES"

  /** The greatest natural not above a real, named by choice. */
  val Floor: String = "NUM_FLOOR"

  /** The least natural not below a real, named the same way. */
  val Ceiling: String = "NUM_CEIL"

  /**
   * `|- !x:real. 0 <= x ==> real_of_num (NUM_FLOOR x) <= x`
   *
   * == Why the hypothesis is there, and why it is written rather than worked around ==
   *
   * `NUM_FLOOR` lands in `num`, and `num` has no negative numbers: the floor of `-1/2` is `-1` and
   * there is nothing here for it to be. So the characterisation holds where the argument is
   * non-negative and says so. **The alternative was not a better constant, it was a worse claim.**
   * A `NUM_FLOOR` that quietly returned something at a negative argument would be right above zero
   * and silently wrong below it, which is exactly the failure a reader cannot see.
   *
   * The honest version of this constant wants the integers, which `docs/adr/0007` puts after this
   * point: `floor : real -> int` characterised for every real, with no hypothesis at all. Until
   * they exist, what a caller gets is this, with the condition on the left of the arrow where it
   * can be read. `select` says nothing about what `NUM_FLOOR x` is when the predicate holds of
   * nothing, so at a negative argument the term denotes and these lemmas decline to say what.
   */
  val FloorAtMost: String = "NUM_FLOOR_LE"

  /** `|- !x:real. 0 <= x ==> x < real_of_num (NUM_FLOOR x) + 1`, the other half of the floor. */
  val FloorAbove: String = "NUM_FLOOR_LT"

  /** `|- !x:real. 0 <= x ==> x <= real_of_num (NUM_CEIL x)`, and [[FloorAtMost]]'s note applies. */
  val CeilingAtLeast: String = "NUM_CEIL_LE"

  /** `|- !x:real. 0 <= x ==> real_of_num (NUM_CEIL x) < x + 1`, the other half of the ceiling. */
  val CeilingBelow: String = "NUM_CEIL_LT"

  /** `|- PRE ZERO = ZERO`, the first of the predecessor's two recurrences. */
  val PreAtZero: String = "NUM_PRE_ZERO"

  /** `|- !n. PRE (SUC n) = n`, the second. */
  val PreAtSuccessor: String = "NUM_PRE_SUC"

  /** `|- !m. NUM_SUB m ZERO = m`, the first of subtraction's two recurrences. */
  val SubAtZero: String = "NUM_SUB_ZERO"

  /** `|- !m n. NUM_SUB m (SUC n) = PRE (NUM_SUB m n)`, the second. */
  val SubAtSuccessor: String = "NUM_SUB_SUC"

  /** `|- !n. NUM_SUB ZERO n = ZERO`, the first recurrence read from the other side. */
  val ZeroMinus: String = "NUM_ZERO_SUB"

  /** `|- !m n. NUM_SUB (SUC m) (SUC n) = NUM_SUB m n`, which is what cancels a step off both. */
  val SubSuccessors: String = "NUM_SUB_SUC_SUC"

  /** `|- !n. NUM_SUB n n = ZERO` */
  val SubSelf: String = "NUM_SUB_REFL"

  /** `|- !m n. NUM_SUB (NUM_ADD m n) n = m`, and it needs no hypothesis: nothing was truncated. */
  val SumMinus: String = "NUM_ADD_SUB"

  /**
   * `|- !m n p. NUM_SUB (NUM_SUB m n) p = NUM_SUB m (NUM_ADD n p)`
   *
   * Taking two amounts away one after the other is taking their sum away, and on `num` it holds
   * with **no** side condition precisely because the subtraction is truncated: where the first
   * difference has already bottomed out at `ZERO` so has the second, and `ZERO - p` is `ZERO`.
   * The same statement over the integers would be the same statement; the reason to say the two
   * agree here is that almost nothing else about `NUM_SUB` does.
   *
   * It is an induction on `p` that the rewriter settles, and [[SubAtSuccessor]] is in its rule set
   * where the three inductions above it leave it out: nothing here has to fire the hypothesis at a
   * node that recurrence would have taken apart first, because the hypothesis is at `p` and that
   * recurrence only matches a successor.
   */
  val SubTwice: String = "NUM_SUB_SUB"

  /**
   * `|- !m n. NUM_SUB m (NUM_ADD m n) = ZERO`, which is the truncation itself.
   *
   * Written with the sum on the right rather than as a bound, because that is the form an
   * induction can be run on: `NUM_LE` is an existential and there is nothing in it to recurse on.
   * [[SubIsZero]] is this with the witness put back inside the quantifier.
   */
  val Truncates: String = "NUM_SUB_TRUNCATES"

  /** `|- !m n. NUM_LE m n ==> NUM_SUB m n = ZERO` */
  val SubIsZero: String = "NUM_SUB_EQ_ZERO"

  /** `|- !n. NUM_LE (PRE n) n`, which holds at `ZERO` only because `PRE ZERO` is `ZERO`. */
  val PredecessorBelow: String = "NUM_PRE_LE"

  /** `|- !m n. NUM_LE (NUM_SUB m n) m` */
  val SubBelow: String = "NUM_SUB_LE"

  /**
   * `|- !m n. NUM_LE n m ==> NUM_ADD (NUM_SUB m n) n = m`
   *
   * The converse of [[SumMinus]], and the hypothesis is not decoration: at `m = ZERO` and
   * `n = SUC ZERO` the left side is `SUC ZERO` and the right is `ZERO`.
   */
  val MinusThenPlus: String = "NUM_SUB_ADD"

  /**
   * `|- !m n. NUM_LE n m ==> NUM_SUB (SUC m) n = SUC (NUM_SUB m n)`
   *
   * A step on the left of a truncated difference comes out of it, and the hypothesis is what makes
   * that true rather than decoration: at `m = ZERO` and `n = SUC ZERO` the left side is
   * `SUC ZERO - SUC ZERO`, which is `ZERO`, and the right side is `SUC (ZERO - SUC ZERO)`, which is
   * `SUC ZERO`. Truncation is what separates them, exactly as it separates [[SumMinus]] from
   * [[MinusThenPlus]].
   *
   * **It is not [[SubAtSuccessor]] read from the other side.** That one moves a step on the
   * **right**, `m - SUC n = PRE (m - n)`, and it is a recurrence of the definition: it holds
   * everywhere and mentions `PRE`. This one moves a step on the left, holds only under the bound,
   * and mentions no predecessor. The pair is the same asymmetry the file's opening draws between
   * the two cancellation laws.
   *
   * Derived rather than induced, from the two that already exist: `n <= m` gives
   * `(m - n) + n = m` by [[MinusThenPlus]], a step on both sides and [[SuccessorPlus]] give
   * `(SUC (m - n)) + n = SUC m`, and [[SumMinus]] takes the `n` back off with nothing owed,
   * because after the first move nothing has been truncated.
   */
  val SuccessorMinus: String = "NUM_SUC_SUB"

  /**
   * `|- !n. NUM_SUB (SUC n) n = SUC ZERO`
   *
   * [[SuccessorMinus]] at `m := n` with [[SubSelf]] under it, and it carries **no** hypothesis for
   * that reason: the bound `n <= n` is [[Reflexive]] and is discharged where the lemma is derived
   * rather than left for a caller. It is published because a conditional fact cannot be a rewrite
   * rule and this one can, which is what a caller peeling the last row off a triangle of indices
   * actually reaches for.
   */
  val SuccessorMinusSelf: String = "NUM_SUC_SUB_SELF"

  /**
   * `|- !m n. NUM_LE n m ==> real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n`
   *
   * The lemma the rest of the subtraction is for. `real_of_num (NUM_SUB m n)` is an atom to every
   * procedure over the reals, and an atom with no fact attached is an unknown real; this says which
   * real it is, and then an index written as a difference meets the arithmetic the tactics decide.
   *
   * Stated under the same hypothesis as [[MinusThenPlus]] and false without it, which is the one
   * mistake a reader who expects the integers' subtraction will make: at `m = ZERO, n = SUC ZERO`
   * the left side is `0` and the right is `-1`.
   */
  val EmbedsDifference: String = "NUM_REAL_SUB"

  /* ------------------------------------------------------------ partial sums */

  /**
   * `NUM_SUM f n` is `f ZERO + ... + f (n - 1)` at the naturals, recursing on `n`.
   *
   * The same operator `Series.Sum` is, one type down, and the duplication is not avoidable by
   * making either polymorphic: `Sum` adds with `+` and this one adds with `NUM_ADD`, which are two
   * constants. It is here rather than beside `Sum` for the reason `Chain.peano` gives: a constant
   * declared after a definition cannot appear inside it, and the successor equation below names
   * `NUM_ADD`, so the definition has to be made over a theory that already holds it.
   *
   * == What it is for, which is an exponent ==
   *
   * A partial sum that is an INDEX rather than a quantity. `Sum` cannot be it: `Power b n` takes a
   * `num` exponent, so a development writing 2^{a_1 + ... + a_j} has no term for the exponent and
   * must declare the partial sums as opaque constants and assume their recurrences instead. That is
   * what documents/02 of the collatz repository does for the run-length decomposition, and the five
   * assumed equations there are what this removes.
   */
  val PartialSum: String = "NUM_SUM"

  /** `|- !f. NUM_SUM f ZERO = ZERO` */
  val PartialSumAtZero: String = "NUM_SUM_ZERO"

  /** `|- !f n. NUM_SUM f (SUC n) = NUM_ADD (NUM_SUM f n) (f n)` */
  val PartialSumAtSuccessor: String = "NUM_SUM_SUC"

  /**
   * `|- !f g n. (!i. NUM_LT i n ==> f i = g i) ==> NUM_SUM f n = NUM_SUM g n`
   *
   * Congruence ON A RANGE, and stated that way the FIRST time rather than after a consumer meets
   * the wall. `Series.CongruenceBelow` is the same lemma at the reals and carries the count of how
   * this goes wrong: four lemmas in this library quantify a hypothesis over the whole type under a
   * conclusion whose object has a bound, none of them has a consumer, and the prediction recorded
   * there is that the first real consumer of any of the four meets the same wall and gets a bounded
   * twin rather than a correction. An unconditional `NUM_SUM_CONGRUENCE` would have been the fifth,
   * and a summand that agrees only where the sum looks -- which is what every argument about a
   * family indexed below a bound produces -- could not use it.
   */
  /**
   * `|- !f m n. NUM_SUM f (m + n) = NUM_SUM f m + NUM_SUM (\i. f (m + i)) n`
   *
   * A sum over a range split at a point, which the real-valued `Sum` has had as `SUM_REINDEX`
   * since it existed and this one had not. What wanted it is a sum over the positions of a word:
   * a word is a concatenation, so every fact about a tally over `WORD_CONCAT x y` is this lemma
   * with `m` the length of `x`, and without it such a tally can be defined and nothing said about
   * it.
   *
   * The shifted summand is `\i. f (m + i)` rather than a reindexed bound, which is the form that
   * composes with `WORD_CONCAT_NTH_RIGHT`: that fact reads the right half at `WORD_LENGTH x + z`,
   * which is this lemma's `f (m + i)` exactly.
   */
  val PartialSumSplit: String = "NUM_SUM_SPLIT"

  val PartialSumCongruenceBelow: String = "NUM_SUM_CONGRUENCE_BELOW"

  /**
   * `|- !f g n. (!i. NUM_LT i n ==> NUM_LE (f i) (g i)) ==> NUM_LE (NUM_SUM f n) (NUM_SUM g n)`
   *
   * [[PartialSumCongruenceBelow]] with the comparison weakened from an equation to the order, and
   * bounded for the same reason that one is: a summand that agrees only where the sum looks is what
   * every argument about a family indexed below a bound produces.
   *
   * What asked for it is a measure over the positions of a word, where a rule that makes the word
   * one letter longer moves every letter after it one place along and each of those letters weighs
   * at least what it weighed before. Nothing pointwise about that is an equation.
   */
  val PartialSumMonotoneBelow: String = "NUM_SUM_MONOTONE_BELOW"

  /* -------------------------------------------------------- binomial coefficients */

  /**
   * `NUM_CHOOSE n k`, the number of ways of choosing `k` things out of `n`.
   *
   * **The recursion is on `n` and its value is a FUNCTION of `k`**, which is the one shape Pascal's
   * rule has: `C(n+1, k+1)` is built from `C(n, k)` and `C(n, k+1)`, two entries of the same row at
   * two different columns, so nothing that recurses on one index while holding the other fixed can
   * state it. `Recursion.theorem` takes the value type as a parameter, so `num -> num` costs
   * nothing new here; it is the first constant in this repository defined that way, and the only
   * thing it costs a reader is that the two equations the recursion hands back are equations
   * between **functions** and not between numbers.
   *
   * Those two are **not published**, and that is a decision rather than an omission. What a reader
   * checks a binomial coefficient against is Pascal's triangle, which is [[ChooseNone]],
   * [[ChooseEmpty]] and [[ChoosePascal]]; the function equations are how the recursion happened to
   * be set up, carry a `COND` and a `PRE` that no consumer should meet, and determine nothing the
   * three do not. The three between them fix **every** value: the first column is one, the first
   * row past it is zero, and everything else is the sum of the two above it.
   *
   * `COND` is what the `k = 0` case needs and there is no way around it: at `k = 0` the step has to
   * answer `1` and at every other `k` it has to add two earlier entries, and `PRE` alone cannot
   * tell the two apart, since `PRE ZERO` is `ZERO` and the step would answer `2 * C(n, 0)`.
   */
  val Choose: String = "NUM_CHOOSE"

  /**
   * `|- !n. NUM_CHOOSE n ZERO = SUC ZERO`
   *
   * There is one way to choose nothing, whatever there is to choose from. It is the left edge of
   * Pascal's triangle, and it is an induction only because the `ZERO` and the `SUC` cases reach the
   * answer through two different equations: both open a `COND` at a condition that holds, and
   * neither needs the induction hypothesis.
   */
  val ChooseNone: String = "NUM_CHOOSE_ZERO"

  /**
   * `|- !k. NUM_CHOOSE ZERO (SUC k) = ZERO`
   *
   * There is no way to choose anything at all out of nothing, which is the top row of the triangle
   * past its first entry. Stated at `SUC k` rather than at `k` with a hypothesis, because the entry
   * it excludes is `NUM_CHOOSE ZERO ZERO`, which is [[ChooseNone]] and is **one**: a reader who met
   * `NUM_LT ZERO k ==> ...` would have to discharge a bound to use the fact, where this form is a
   * rewrite rule.
   */
  val ChooseEmpty: String = "NUM_CHOOSE_EMPTY"

  /**
   * `|- !n k. NUM_CHOOSE (SUC n) (SUC k) = NUM_ADD (NUM_CHOOSE n k) (NUM_CHOOSE n (SUC k))`
   *
   * Pascal's rule, and with the two above it every entry of the triangle is determined. It is
   * stated at `SUC k` on both sides for the reason [[ChooseEmpty]] is stated at `SUC k`: the rule
   * is false at `k = ZERO`, where the left side is `SUC ZERO` and the right side would be
   * `NUM_ADD (NUM_CHOOSE n (PRE ZERO)) (NUM_CHOOSE n ZERO)`, which is `SUC ZERO` doubled. Writing
   * it with `PRE` would make it true at every `k` and unusable at all of them, since a consumer
   * holding a column `SUC k` would have to push a predecessor through it first.
   */
  val ChoosePascal: String = "NUM_CHOOSE_SUC"

  /**
   * `|- !n k. NUM_LT n k ==> NUM_CHOOSE n k = ZERO`
   *
   * The triangle is zero above its own diagonal, which is the one fact about it that is not a
   * recurrence and the one a shifted sum needs: extending a sum over columns `0..n` to one over
   * `0..n+1` costs nothing exactly because the entry it adds is this.
   *
   * [[ChooseEmpty]] is the case `n = ZERO` and does **not** give this: that one is the top row,
   * and a single induction on the row cannot reach the rest, because the step at `SUC n` asks for
   * the row `n` at **two** columns and an induction on one variable offers it at one.
   */
  val ChooseAbove: String = "NUM_CHOOSE_ABOVE"

  /**
   * `|- !m. NUM_CHOOSE m m = SUC ZERO`, the triangle's diagonal.
   *
   * Pascal's recurrence with [[ChooseAbove]] under it: the entry one past the diagonal is zero,
   * so the two summands the recurrence produces are the hypothesis and nothing.
   *
   * It exists for `Coding.NUM_CHOOSE_FACTORIAL` and for the one case of that identity a strong
   * induction on `i + j` cannot reach from below, which is `j = 0`.
   */
  val ChooseDiagonal: String = "NUM_CHOOSE_ALL"

  /* ----------------------------------------------------------------- numerals */

  /**
   * `NUM_ONE`, `NUM_BIT0` and `NUM_BIT1`: the binary encoding of a numeral at `num`.
   *
   * The reals have had one since they were written, and until 2026-09-12 it was the only one, so
   * `Parser` decided a numeral's type from the declared type of `1` and its docstring said why:
   * *"numerals here belong to one theory and one type, and a polymorphic numeral would need the
   * elaborator to decide which."* What that cost a consumer is one line: `Power 2 3` could not be
   * written, because `Power : real -> num -> real` wants a real base and a natural exponent, and
   * one digit string cannot be both. The exponent had to be spelled `SUC (SUC (SUC ZERO))`, and an
   * index written as an expression -- which is most of them -- had to be spelled that way
   * throughout.
   *
   * So there are two encodings now, and the elaborator decides: a numeral takes a metavariable and
   * is expanded once unification has said what type its context forced it to. **`ZERO` is the
   * numeral zero of this encoding rather than a fourth constant beside it**, which is what keeps
   * `0:num` and `ZERO` the same term; a separate `NUM_ZERO` would print more tidily and would put
   * every lemma about `ZERO` out of reach of every statement written with `0`.
   *
   * `NUM_ONE` is the one thing the encoding needs that `num` did not have. A numeral's chain of
   * bits ends at a **constant**, because that is what [[garden.xeno.symbolum.logic.NumeralNotation]] matches
   * on, and `SUC ZERO` is an application. It is defined, not declared, so it costs no axiom;
   * [[NumeralOneIsSuccessorOfZero]] is the equation that says so and is what a rewrite uses to get
   * back to the successor form the rest of this file is written in.
   */
  val NumeralOne: String = "NUM_ONE"

  /** `NUM_BIT0 n` is `NUM_ADD n n`; [[NumeralOne]] carries the whole decision. */
  val NumeralBit0: String = "NUM_BIT0"

  /** `NUM_BIT1 n` is `SUC (NUM_ADD n n)`; [[NumeralOne]] carries the whole decision. */
  val NumeralBit1: String = "NUM_BIT1"

  /** `|- NUM_ONE = SUC ZERO`, the definition, which is how a numeral re-enters the successor form. */
  val NumeralOneIsSuccessorOfZero: String = "NUM_ONE_SUC"

  /** `|- !n. NUM_BIT0 n = NUM_ADD n n`, the even digit as the doubling it is. */
  val NumeralBit0Doubles: String = "NUM_BIT0_ADD"

  /** `|- !n. NUM_BIT1 n = SUC (NUM_ADD n n)`, the odd digit. */
  val NumeralBit1Doubles: String = "NUM_BIT1_SUC"

  /**
   * `|- real_of_num NUM_ONE = 1`, and the two below it: the encodings agree across the embedding.
   *
   * These three are the payload rather than the definitions. A `num` numeral that could not be
   * carried to the real of the same value would be a second spelling and nothing more; with them, a
   * rewrite takes `real_of_num` through any numeral's bits and lands on the real numeral with the
   * same digits, which is what every statement mixing an index with an arithmetic fact needs.
   */
  val EmbedsNumeralOne: String = "NUM_REAL_ONE"

  /** `|- !n. real_of_num (NUM_BIT0 n) = BIT0 (real_of_num n)`. */
  val EmbedsNumeralBit0: String = "NUM_REAL_BIT0"

  /** `|- !n. real_of_num (NUM_BIT1 n) = BIT1 (real_of_num n)`. */
  val EmbedsNumeralBit1: String = "NUM_REAL_BIT1"

  /* -------------------------------------------------------------- statements */

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * The same discipline `Real.Axioms` follows for the axioms and for the same reason: a statement
   * is checked by reading it, and builder calls are not read. Every theorem below is compared
   * against its entry here before it is recorded, so a derivation that reaches something else is a
   * refusal rather than a fact under the wrong name.
   *
   * Two of them are quantified in an order a reader would not choose. [[AddCancels]] is stated
   * `!n m.` because the induction is on `m`, and the driver inducts on the **last** quantifier of
   * the statement it is given.
   */
  val Statements: Vector[(String, String)] = Vector(
    AddAtZero -> "!m:num. NUM_ADD m ZERO = m",
    AddAtSuccessor -> "!m:num n:num. NUM_ADD m (SUC n) = SUC (NUM_ADD m n)",
    ZeroPlus -> "!n:num. NUM_ADD ZERO n = n",
    SuccessorPlus -> "!m:num n:num. NUM_ADD (SUC m) n = SUC (NUM_ADD m n)",
    AddAssociative -> "!m:num n:num p:num. NUM_ADD (NUM_ADD m n) p = NUM_ADD m (NUM_ADD n p)",
    AddCommutative -> "!m:num n:num. NUM_ADD m n = NUM_ADD n m",
    AddExchange -> "!m:num n:num p:num. NUM_ADD m (NUM_ADD n p) = NUM_ADD n (NUM_ADD m p)",
    Shift -> "!m:num n:num. NUM_ADD m (SUC n) = NUM_ADD (SUC m) n",
    MulAtZero -> "!m:num. NUM_MUL m ZERO = ZERO",
    MulAtSuccessor -> "!m:num n:num. NUM_MUL m (SUC n) = NUM_ADD (NUM_MUL m n) m",
    ZeroTimes -> "!n:num. NUM_MUL ZERO n = ZERO",
    TimesOne -> "!n:num. NUM_MUL n (SUC ZERO) = n",
    Distributive ->
      "!m:num n:num p:num. NUM_MUL m (NUM_ADD n p) = NUM_ADD (NUM_MUL m n) (NUM_MUL m p)",
    MulAssociative -> "!m:num n:num p:num. NUM_MUL (NUM_MUL m n) p = NUM_MUL m (NUM_MUL n p)",
    SuccessorTimes -> "!m:num n:num. NUM_MUL (SUC m) n = NUM_ADD (NUM_MUL m n) n",
    MulCommutative -> "!m:num n:num. NUM_MUL m n = NUM_MUL n m",
    PowAtZero -> "!m:num. NUM_POW m ZERO = SUC ZERO",
    PowAtSuccessor -> "!m:num n:num. NUM_POW m (SUC n) = NUM_MUL (NUM_POW m n) m",
    PowAddsExponents ->
      "!m:num n:num p:num. NUM_POW m (NUM_ADD n p) = NUM_MUL (NUM_POW m n) (NUM_POW m p)",
    OneToAnyPower -> "!n:num. NUM_POW (SUC ZERO) n = SUC ZERO",
    PowPositive -> "!m:num n:num. NUM_LT ZERO m ==> NUM_LT ZERO (NUM_POW m n)",
    TimesTwo -> "!m:num. NUM_MUL m (SUC (SUC ZERO)) = NUM_ADD m m",
    AddCancels -> "!n:num m:num. NUM_ADD m n = m ==> n = ZERO",
    AddCancelsLeft -> "!x:num y:num a:num. NUM_ADD a x = NUM_ADD a y ==> x = y",
    SumIsZero -> "!m:num n:num. NUM_ADD m n = ZERO ==> m = ZERO",
    Reflexive -> "!n:num. NUM_LE n n",
    ZeroIsLeast -> "!n:num. NUM_LE ZERO n",
    AtMostSuccessor -> "!n:num. NUM_LE n (SUC n)",
    Transitive -> "!m:num n:num p:num. NUM_LE m n /\\ NUM_LE n p ==> NUM_LE m p",
    StrictTransitive -> "!m:num n:num p:num. NUM_LT m n /\\ NUM_LT n p ==> NUM_LT m p",
    AntiSymmetric -> "!m:num n:num. NUM_LE m n /\\ NUM_LE n m ==> m = n",
    BelowSuccessor -> "!n:num. NUM_LT n (SUC n)",
    Total -> "!m:num n:num. NUM_LE m n \\/ NUM_LE n m",
    Trichotomy -> "!m:num n:num. NUM_LT m n \\/ m = n \\/ NUM_LT n m",
    SuccessorNotSelf -> "!n:num. ~(SUC n = n)",
    StrictIrreflexive -> "!n:num. ~(NUM_LT n n)",
    SuccessorPositive -> "!n:num. NUM_LT ZERO (SUC n)",
    MulPositive ->
      "!m:num n:num. NUM_LT ZERO m ==> NUM_LT ZERO n ==> NUM_LT ZERO (NUM_MUL m n)",
    BelowOrEqual -> "!m:num n:num. NUM_LE m n ==> NUM_LT m n \\/ m = n",
    NotBelowZero -> "!i:num. ~(NUM_LT i ZERO)",
    AtMostFromBelow -> "!m:num n:num. NUM_LT m n ==> NUM_LE m n",
    AtMostThenBelow ->
      "!m:num n:num p:num. NUM_LE m n /\\ NUM_LT n p ==> NUM_LT m p",
    AddMonotone ->
      "!p:num m:num n:num. NUM_LE m n ==> NUM_LE (NUM_ADD p m) (NUM_ADD p n)",
    AddStrictlyMonotone ->
      "!p:num m:num n:num. NUM_LT m n ==> NUM_LT (NUM_ADD p m) (NUM_ADD p n)",
    AddCancelsOrder ->
      "!p:num m:num n:num. NUM_LE (NUM_ADD p m) (NUM_ADD p n) ==> NUM_LE m n",
    AddCancelsStrictOrder ->
      "!p:num m:num n:num. NUM_LT (NUM_ADD p m) (NUM_ADD p n) ==> NUM_LT m n",
    AtMostFromNotBelow -> "!m:num n:num. (~(NUM_LT m n)) ==> NUM_LE n m",
    MulMonotone ->
      "!p:num m:num n:num. NUM_LE m n ==> NUM_LE (NUM_MUL p m) (NUM_MUL p n)",
    MulStrictlyMonotone ->
      ("!p:num m:num n:num. NUM_LT ZERO p ==> NUM_LT m n ==> " +
        "NUM_LT (NUM_MUL p m) (NUM_MUL p n)"),
    MulCancelsLeft ->
      "!p:num m:num n:num. NUM_LT ZERO p ==> NUM_MUL p m = NUM_MUL p n ==> m = n",
    BelowExcludesAtMost -> "!m:num n:num. NUM_LT m n ==> ~(NUM_LE n m)",
    AtMostSum -> "!m:num n:num. NUM_LE m (NUM_ADD m n)",
    AddMonotoneBoth ->
      ("!a:num b:num c:num d:num. NUM_LE a b /\\ NUM_LE c d ==> " +
        "NUM_LE (NUM_ADD a c) (NUM_ADD b d)"),
    BelowThenAtMost ->
      "!m:num n:num p:num. NUM_LT m n /\\ NUM_LE n p ==> NUM_LT m p",
    StrongInduction ->
      ("!P:num->bool. (!n:num. (!m:num. NUM_LT m n ==> P m) ==> P n) ==> " +
        "(!n:num. P n)"),
    AtMostZero -> "!n:num. NUM_LE n ZERO ==> n = ZERO",
    AtMostBelowSuccessor -> "!n:num i:num. NUM_LT i (SUC n) ==> NUM_LE i n",
    AtMostDoubleMinus ->
      "!n:num i:num. NUM_LE i n ==> NUM_LE n (NUM_SUB (NUM_ADD n n) i)",
    BelowSuccessorCases -> "!n:num i:num. NUM_LT i (SUC n) ==> NUM_LT i n \\/ i = n",
    LeastNumber ->
      ("!P:num->bool. (?n:num. P n) ==> " +
        "(?m:num. P m /\\ (!k:num. NUM_LT k m ==> ~(P k)))"),
    GreatestBounded ->
      ("!P:num->bool. (?n:num. P n) /\\ (?b:num. !k:num. P k ==> NUM_LE k b) ==> " +
        "(?m:num. P m /\\ (!k:num. P k ==> NUM_LE k m))"),
    EmbedsZero -> "real_of_num ZERO = 0",
    EmbedsSuccessor -> "!n:num. real_of_num (SUC n) = real_of_num n + 1",
    EmbedsSum -> "!m:num n:num. real_of_num (NUM_ADD m n) = real_of_num m + real_of_num n",
    EmbedsProduct -> "!m:num n:num. real_of_num (NUM_MUL m n) = real_of_num m * real_of_num n",
    EmbedsNonNegative -> "!n:num. 0 <= real_of_num n",
    EmbedsOrder -> "!m:num n:num. NUM_LE m n ==> real_of_num m <= real_of_num n",
    EmbedsStrictOrder -> "!m:num n:num. NUM_LT m n ==> real_of_num m + 1 <= real_of_num n",
    EmbedsOrderBack -> "!m:num n:num. real_of_num m <= real_of_num n ==> NUM_LE m n",
    EmbedsInjectively -> "!m:num n:num. real_of_num m = real_of_num n ==> m = n",
    Archimedean -> "!x:real. ?n:num. x < real_of_num n",
    FloorAtMost -> "!x:real. 0 <= x ==> real_of_num (NUM_FLOOR x) <= x",
    FloorAbove -> "!x:real. 0 <= x ==> x < real_of_num (NUM_FLOOR x) + 1",
    CeilingAtLeast -> "!x:real. 0 <= x ==> x <= real_of_num (NUM_CEIL x)",
    CeilingBelow -> "!x:real. 0 <= x ==> real_of_num (NUM_CEIL x) < x + 1",
    PreAtZero -> "PRE ZERO = ZERO",
    PreAtSuccessor -> "!n:num. PRE (SUC n) = n",
    SubAtZero -> "!m:num. NUM_SUB m ZERO = m",
    SubAtSuccessor -> "!m:num n:num. NUM_SUB m (SUC n) = PRE (NUM_SUB m n)",
    ZeroMinus -> "!n:num. NUM_SUB ZERO n = ZERO",
    SubSuccessors -> "!m:num n:num. NUM_SUB (SUC m) (SUC n) = NUM_SUB m n",
    SubSelf -> "!n:num. NUM_SUB n n = ZERO",
    SumMinus -> "!m:num n:num. NUM_SUB (NUM_ADD m n) n = m",
    SubTwice -> "!m:num n:num p:num. NUM_SUB (NUM_SUB m n) p = NUM_SUB m (NUM_ADD n p)",
    Truncates -> "!m:num n:num. NUM_SUB m (NUM_ADD m n) = ZERO",
    SubIsZero -> "!m:num n:num. NUM_LE m n ==> NUM_SUB m n = ZERO",
    PredecessorBelow -> "!n:num. NUM_LE (PRE n) n",
    SubBelow -> "!m:num n:num. NUM_LE (NUM_SUB m n) m",
    MinusThenPlus -> "!m:num n:num. NUM_LE n m ==> NUM_ADD (NUM_SUB m n) n = m",
    SuccessorMinus -> "!m:num n:num. NUM_LE n m ==> NUM_SUB (SUC m) n = SUC (NUM_SUB m n)",
    SuccessorMinusSelf -> "!n:num. NUM_SUB (SUC n) n = SUC ZERO",
    ChooseNone -> "!n:num. NUM_CHOOSE n ZERO = SUC ZERO",
    ChooseEmpty -> "!k:num. NUM_CHOOSE ZERO (SUC k) = ZERO",
    ChoosePascal ->
      ("!n:num k:num. NUM_CHOOSE (SUC n) (SUC k) = " +
        "NUM_ADD (NUM_CHOOSE n k) (NUM_CHOOSE n (SUC k))"),
    ChooseAbove -> "!n:num k:num. NUM_LT n k ==> NUM_CHOOSE n k = ZERO",
    ChooseDiagonal -> "!m:num. NUM_CHOOSE m m = SUC ZERO",
    EmbedsDifference ->
      "!m:num n:num. NUM_LE n m ==> real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n",
    PartialSumAtZero -> "!f:num -> num. NUM_SUM f ZERO = ZERO",
    PartialSumAtSuccessor ->
      "!f:num -> num. !n:num. NUM_SUM f (SUC n) = NUM_ADD (NUM_SUM f n) (f n)",
    PartialSumSplit ->
      ("!f:num -> num. !m:num. !n:num. " +
        "NUM_SUM f (NUM_ADD m n) = " +
        "NUM_ADD (NUM_SUM f m) (NUM_SUM (\\i:num. f (NUM_ADD m i)) n)"),
    PartialSumCongruenceBelow ->
      ("!f:num -> num. !g:num -> num. !n:num. " +
        "(!i:num. NUM_LT i n ==> f i = g i) ==> NUM_SUM f n = NUM_SUM g n"),
    PartialSumMonotoneBelow ->
      ("!f:num -> num. !g:num -> num. !n:num. " +
        "(!i:num. NUM_LT i n ==> NUM_LE (f i) (g i)) ==> " +
        "NUM_LE (NUM_SUM f n) (NUM_SUM g n)"),
    NumeralOneIsSuccessorOfZero -> "NUM_ONE = SUC ZERO",
    NumeralBit0Doubles -> "!n:num. NUM_BIT0 n = NUM_ADD n n",
    NumeralBit1Doubles -> "!n:num. NUM_BIT1 n = SUC (NUM_ADD n n)",
    EmbedsNumeralOne -> "real_of_num NUM_ONE = 1",
    EmbedsNumeralBit0 -> "!n:num. real_of_num (NUM_BIT0 n) = BIT0 (real_of_num n)",
    EmbedsNumeralBit1 -> "!n:num. real_of_num (NUM_BIT1 n) = BIT1 (real_of_num n)"
  )

  private val statements: Map[String, String] = Statements.toMap

  /* ------------------------------------------------------------ construction */

  /** The standard development, over the chain that has both types in one signature. */
  lazy val standard: Peano =
    construct(Chain.standard.naturals, Chain.standard.ring).fold(
      error => throw new IllegalStateException(s"the arithmetic of the naturals does not build: ${error.message}"),
      identity
    )

  /**
   * The development over the naturals and the reals of a chain of one's own.
   *
   * Both are needed and the second is not decoration: `real_of_num` cannot be stated without a
   * signature holding both types, and the two homomorphism lemmas are proved by an induction whose
   * step is a ring identity, so the tactic that decides those has to be to hand. `Chain` is what
   * builds the pair in the order that works.
   */
  /**
   * The arithmetic of `num` alone, over a theory that has never heard of `real`.
   *
   * `docs/adr/0016`'s phase 0, as something a test can point at. What comes back is the seven
   * stages that name no real, built over `naturals.theory`, which declares `num` and the logic and
   * nothing else: no type `real`, no `+`, no `<`, no `real_of_num`.
   *
   * It is not what the chain builds. The chain still puts this development over the reals, because
   * nothing below them needs it there yet and moving it is churn until the construction wants it.
   * What this is for is the assertion `PeanoSpec` makes with it: that the 74 facts are **buildable**
   * below the reals rather than merely free of them, which is the difference between a measurement
   * of the derivations as they stand and a fact about what they depend on.
   *
   * The two notations differ and the difference is not cosmetic. Over the reals the numerals are
   * read at `real` until [[numerals]] widens the table to read them at `num` as well; here there is
   * no `real` to read them at, so a digit string is a natural from the first stage. Nothing in
   * these seven statements is ambiguous either way, which is itself part of what is being asserted.
   */
  def arithmetic(
    naturals: Natural
  ): Either[LogicError, (Theory, Notation, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] =
    arithmeticStages(naturals, naturals.theory, naturals.notation)
      .map(stages => (stages.theory, stages.notation, stages.definitions, stages.facts))

  def construct(naturals: Natural, ring: Ring): Either[LogicError, Peano] =
    construct(naturals, ring, ring.reals.theory)

  /**
   * The same, for a caller that has already built the order facts.
   *
   * `Chain` builds an `Order` before this line and would otherwise pay for a second one. The order
   * is here at all because of the three lemmas that carry a bound on an index into the reals: they
   * are closed by `LINARITH`, which is built over an order, and there is no counterpart to it over
   * `num` to close them with instead.
   */
  def construct(naturals: Natural, ring: Ring, order: Order): Either[LogicError, Peano] =
    construct(naturals, ring, ring.reals.theory, order)

  /**
   * The same, extending a theory that already holds something else.
   *
   * `Chain` does not use it any more and it is not dead: it is what a caller with a development of
   * its own over the reals reaches for, and the parameter is the reason the chain could be built
   * either way round while the question of which was open. `Series` is now built over **this**
   * rather than the other way about, because a constant declared after a definition cannot appear
   * inside it: see `Chain.peano` for the whole of that argument.
   */
  def construct(naturals: Natural, ring: Ring, base: Theory): Either[LogicError, Peano] =
    Order.construct(ring).flatMap(construct(naturals, ring, base, _))

  /** The same again, over a theory and an order the caller holds. */
  def construct(
    naturals: Natural,
    ring: Ring,
    base: Theory,
    bounds: Order
  ): Either[LogicError, Peano] = {
    val notation = ring.reals.notation

    for {
      linarith <- Linarith.construct(bounds)
      stages <- arithmeticStages(naturals, base, notation)
      logic = stages.logic
      recursion = stages.recursion

      // A driver of its own, and the reason is the whole point of the split. The stages above ran
      // on `stages.driver`, which has no closer because nothing about `num` needs one; the stages
      // below are about the reals and their steps end in ring identities, so they need `Ring`.
      // Handing them the closerless one refuses with the goal named, which is how this line came
      // to be written: `real_of_num x = real_of_num x + 0` is a step of the embedding.
      induction <- naturals.fact(Natural.Induction)
      driver = Induct(logic, ring, induction)
      addFacts = stages.addFacts
      mulFacts = stages.mulFacts
      orderDefinitions = stages.orderDefinitions
      orderFacts = stages.orderFacts
      subtractionFacts = stages.subtractionFacts
      numeralFacts = stages.numeralFacts
      withNumerals = stages.theory
      spelled = stages.notation

      // ---- and from here the reals are needed, and were not above ----

      // `notation` and NOT `spelled`, which is the one thing the reorder is not free in. `spelled`
      // reads a digit string at `num` as well as at `real`, and these statements are about the
      // reals and carry bare numerals: `real_of_num ZERO = 0` with both readings available is the
      // refusal `docs/adr/0012` promises, "the type of the numeral 0 is not determined". The
      // statements are right and the reader was wrong, so the reader narrows rather than the text
      // gaining annotations, which is what that record asks for.
      embedded <- Embedding.embedding(
        logic,
        driver,
        linarith,
        naturals,
        withNumerals,
        notation,
        recursion,
        addFacts ++ mulFacts,
        orderDefinitions,
        orderFacts(Trichotomy),
        orderFacts(Reflexive),
        orderFacts(AtMostFromBelow)
      )
      (withEmbedding, embeddingDefinition, embeddingFacts) = embedded

      // The two facts that were inside a pure stage until the split: a difference carried across
      // the embedding, and the three numerals carried across it.
      minusThenPlusFact <- subtractionFacts
        .get(MinusThenPlus)
        .toRight(MissingDefinition(MinusThenPlus))
      embedsDifference <- Embedding.subtractionEmbedded(
        logic, ring, withEmbedding, spelled, embeddingFacts(EmbedsSum), minusThenPlusFact)

      oneIsSuccessorFact <- numeralFacts
        .get(NumeralOneIsSuccessorOfZero)
        .toRight(MissingDefinition(NumeralOneIsSuccessorOfZero))
      bit0DoublesFact <- numeralFacts
        .get(NumeralBit0Doubles)
        .toRight(MissingDefinition(NumeralBit0Doubles))
      bit1DoublesFact <- numeralFacts
        .get(NumeralBit1Doubles)
        .toRight(MissingDefinition(NumeralBit1Doubles))
      numeralEmbeddingFacts <- Embedding.numeralsEmbedded(
        logic,
        ring,
        withEmbedding,
        spelled,
        embeddingFacts,
        oneIsSuccessorFact,
        bit0DoublesFact,
        bit1DoublesFact
      )

      overNumerals <- naturals.classical.logic.over(withEmbedding)

      // Last, and over the finished signature, because these two are the only derivations in this
      // file that reason classically: `Classical.contradiction` and `Classical.cases` want the
      // connectives, and the steps above were checked against a narrower theory.
      realTrichotomy <- ring.reals.axiom("LT_TOTAL")
      realCompleteness <- ring.reals.axiom("COMPLETENESS")
      embedsSuccessorFact <- embeddingFacts
        .get(EmbedsSuccessor)
        .toRight(MissingDefinition(EmbedsSuccessor))
      embedsZeroFact <- embeddingFacts.get(EmbedsZero).toRight(MissingDefinition(EmbedsZero))
      archimedes <- Embedding.archimedean(
        overNumerals,
        naturals.classical,
        linarith,
        withEmbedding,
        spelled,
        realTrichotomy,
        realCompleteness,
        embedsSuccessorFact
      ).flatMap(checked(withEmbedding, spelled, Archimedean, _))

      // And the floor, which is what the Archimedean property was wanted for: it is the only thing
      // that says the search for a natural past a real terminates at all.
      leastFact <- orderFacts.get(LeastNumber).toRight(MissingDefinition(LeastNumber))
      belowSuccessorFact <- orderFacts.get(BelowSuccessor).toRight(MissingDefinition(BelowSuccessor))
      zeroOrSuccessor <- naturals.fact(Natural.ZeroOrSuccessor)
      leCases <- bounds.fact(Order.LeCases)
      bounded <- Embedding.floors(
        overNumerals,
        naturals.classical,
        linarith,
        withEmbedding,
        spelled,
        archimedes,
        leastFact,
        zeroOrSuccessor,
        belowSuccessorFact,
        embedsZeroFact,
        embedsSuccessorFact,
        realTrichotomy,
        leCases
      )
      (withFloors, floorDefinitions, floorFacts) = bounded

      // The connectives against the finished signature, which is wider than the one the derivations
      // above were run against: `Logic.over` checks the extension rather than assuming it, so this
      // is also the assertion that nothing was defined into a side branch.
      widest <- naturals.classical.logic.over(withFloors)
    } yield new Peano(
      naturals,
      ring,
      withFloors,
      spelled,
      widest,
      stages.definitions ++ Map(EmbeddingName -> embeddingDefinition) ++ floorDefinitions,
      stages.facts ++ embeddingFacts ++ numeralEmbeddingFacts ++ floorFacts ++
        Map(Archimedean -> archimedes, EmbedsDifference -> embedsDifference)
    )
  }

  /**
   * What every stage that names no real produces, held together rather than returned as a tuple.
   *
   * Seventeen values was past the point where a tuple is readable, and the fields are what
   * [[Peano.construct]] threads into the stages that do name a real.
   */
  private final case class Arithmetic(
    theory: Theory,
    notation: Notation,
    logic: Logic,
    driver: Induct,
    recursion: Kernel.Thm,
    addFacts: Map[String, Kernel.Thm],
    mulFacts: Map[String, Kernel.Thm],
    orderDefinitions: Map[String, Kernel.Thm],
    orderFacts: Map[String, Kernel.Thm],
    subtractionFacts: Map[String, Kernel.Thm],
    numeralFacts: Map[String, Kernel.Thm],
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  )

  /**
   * Every stage that names no real, over whatever theory the caller has.
   *
   * `docs/adr/0016`'s phase 0 in one signature. These seven stages were measured on 2026-09-15:
   * not one node of any of the 74 facts they produce mentions a real, in a conclusion or in a
   * hypothesis. So they take a `base` and a `notation` and ask for nothing else, and in particular
   * for **no `Ring`**. The driver is [[Induct.overNaturals]], whose closer refuses by name, because
   * `Ring.prove` refuses a goal of type `num` by type and so never closed one of these.
   *
   * [[Peano.arithmetic]] calls it over a theory that has never heard of `real`, which is what makes
   * the split a fact about the theory rather than a reading of the statements. [[Peano.construct]]
   * calls it over the reals' theory, which is what the chain still does, and runs the stages that
   * do name a real on top of it.
   */
  private def arithmeticStages(
    naturals: Natural,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Arithmetic] =
    for {
      logic <- naturals.classical.logic.over(base)
      recursion <- naturals.recursion
      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      sums <- addition(logic, driver, naturals, base, notation, recursion)
      (withAddition, additionDefinition, addFacts) = sums

      products <- multiplication(logic, driver, naturals, withAddition, notation, recursion, addFacts)
      (withMultiplication, multiplicationDefinition, mulFacts) = products

      // After multiplication, because its step multiplies by the base, and before the order,
      // because nothing in the order knows about it.
      powers <- exponentiation(
        logic, driver, naturals, withMultiplication, notation, recursion, mulFacts ++ addFacts)
      (withPowers, exponentiationDefinition, powFacts) = powers

      ordered <- order(logic, withPowers, notation, addFacts ++ mulFacts, naturals, driver)
      (withOrder, orderDefinitions, orderFacts) = ordered

      // HERE AND NOT IN EITHER BLOCK, for the reason [[PowPositive]] gives: the powers are built
      // before the order and the order is not given them, so the one induction that needs both
      // recurrences and both sign lemmas has to happen where both are in hand.
      powPositive <- powerIsPositive(driver, withOrder, notation, powFacts, orderFacts)

      // The four pure stages are finished and the theory under them names no real. Everything
      // from here down does, and the order is `docs/adr/0016`'s phase 0: the stages that can be
      // stated below the reals run first, and the split of this file follows the split of this
      // comprehension rather than the other way round.
      subtracted <- subtraction(
        logic,
        driver,
        naturals,
        withOrder,
        notation,
        recursion,
        addFacts,
        orderDefinitions,
        orderFacts
      )
      (withSubtraction, subtractionDefinitions, subtractionFacts) = subtracted

      // Its step adds and its congruence compares: `NUM_ADD` for the recursion and `NUM_LT` with
      // the two lemmas that lift an index to below a successor.
      summed <- partialSums(
        logic, driver, naturals, withSubtraction, notation, recursion, orderFacts, addFacts)
      (withPartialSums, partialSumDefinition, partialSumFacts) = summed

      // The binomial coefficients, whose recursion is the one in this file whose VALUE is a
      // function. It needs `COND` from the classical extension and `PRE` from the subtraction
      // stage, which is why it comes after both.
      chosen <- binomials(
        logic, driver, naturals, withPartialSums, notation, recursion, subtractionFacts,
        orderDefinitions, addFacts, induction)
      (withChoose, chooseDefinition, chooseFacts) = chosen

      // The last of the pure stages: three definitions and three doubling lemmas, no real.
      spelt <- numerals(logic, withChoose, notation, addFacts)
      (withNumerals, spelled, numeralDefinitions, numeralFacts) = spelt
    } yield Arithmetic(
      withNumerals,
      spelled,
      logic,
      driver,
      recursion,
      addFacts,
      mulFacts,
      orderDefinitions,
      orderFacts,
      subtractionFacts,
      numeralFacts,
      Map(
        Addition -> additionDefinition,
        Multiplication -> multiplicationDefinition,
        Exponentiation -> exponentiationDefinition,
        PartialSum -> partialSumDefinition,
        Choose -> chooseDefinition
      ) ++ orderDefinitions ++ subtractionDefinitions ++ numeralDefinitions,
      addFacts ++ mulFacts ++ powFacts ++ orderFacts ++ subtractionFacts ++ partialSumFacts ++
        chooseFacts ++ numeralFacts ++ Map(PowPositive -> powPositive)
    )

  /* --------------------------------------------------------------- addition */

  /**
   * Addition, its two recurrences, and the facts a consumer of a sum asks for.
   *
   * All but one of them close by rewriting: the recurrences go in as rules, the induction
   * hypothesis joins them inside the step, and both sides of the goal reach the same term. Which
   * lemma each step needs is the interesting part:
   *
   *  - [[ZeroPlus]] and [[SuccessorPlus]] need only the two recurrences. They are the mirror image
   *    of the recursion, and they exist because the recursion happens on one argument and half the
   *    uses are on the other.
   *  - [[AddAssociative]] needs the two recurrences.
   *  - [[AddCommutative]] needs both of the first two, one for its base and one for its step, and
   *    that is why they come first. The step is `m + SUC n = SUC (m + n) = SUC (n + m) = SUC n + m`,
   *    where the first equality is a recurrence, the second is the hypothesis, and the third is
   *    [[SuccessorPlus]] read backwards, which the rewriter does by bringing both sides to the
   *    same form rather than by reversing anything.
   *  - [[AddExchange]] is derived by hand instead: it is a rewrite that holds in both directions,
   *    so it cannot be reached by rewriting to a normal form, and it is three named steps.
   *  - [[Shift]] needs no induction at all: both sides reach `SUC (m + n)`, one by a recurrence
   *    and the other by [[SuccessorPlus]].
   */
  private def addition(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Addition,
        numbers,
        "m:num",
        "\\v:num. \\i:num. SUC v",
        Some(m)
      )
      (theory, definition, atZero, atSuccessor) = defined

      addAtZero <- checked(theory, notation, AddAtZero, atZero)
      addAtSuccessor <- checked(theory, notation, AddAtSuccessor, atSuccessor)
      recurrences = Vector(addAtZero, addAtSuccessor)

      zeroPlus <- byInduction(driver, theory, notation, ZeroPlus, recurrences)
      successorPlus <- byInduction(driver, theory, notation, SuccessorPlus, recurrences)
      associative <- byInduction(driver, theory, notation, AddAssociative, recurrences)
      commutative <- byInduction(
        driver,
        theory,
        notation,
        AddCommutative,
        recurrences ++ Vector(zeroPlus, successorPlus)
      )
      exchange <- exchanged(logic, theory, notation, associative, commutative)
      shift <- byRewriting(logic, theory, notation, Shift, recurrences :+ successorPlus)
    } yield (
      theory,
      definition,
      Map(
        AddAtZero -> addAtZero,
        AddAtSuccessor -> addAtSuccessor,
        ZeroPlus -> zeroPlus,
        SuccessorPlus -> successorPlus,
        AddAssociative -> associative,
        AddCommutative -> commutative,
        AddExchange -> exchange,
        Shift -> shift
      )
    )
  }

  /**
   * `|- !m n p. NUM_ADD m (NUM_ADD n p) = NUM_ADD n (NUM_ADD m p)`, by hand and not by rewriting.
   *
   * `m + (n + p) = (m + n) + p = (n + m) + p = n + (m + p)`: associativity backwards, commutativity
   * under the outer sum, associativity forwards. It is the rule that sorts a sum, so it cannot be
   * proved by sorting one; a rewriter given commutativity rewrites its own output for ever.
   */
  private def exchanged(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    associative: Kernel.Thm,
    commutative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val p = Term.variable("p", numbers)

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      grouped <- rules.specAll(associative, List(m, n, p))
      ungrouped <- Conv.sym(grouped)
      swapped <- rules.specAll(commutative, List(m, n))
      underneath <- Conv.apTerm(plus, swapped).flatMap(Conv.apThm(_, p))
      regrouped <- rules.specAll(associative, List(n, m, p))

      whole <- Conv
        .trans(ungrouped, underneath)
        .flatMap(Conv.trans(_, regrouped))
        .flatMap(rules.genAll(_, List(m, n, p)))
      result <- checked(theory, notation, AddExchange, whole)
    } yield result
  }

  /* --------------------------------------------------------- multiplication */

  /**
   * Multiplication, its two recurrences, and what follows from them.
   *
   * All but one of them close by rewriting with the recurrences of both operations and the
   * associativity of addition. [[SuccessorTimes]] is the exception and it is where the sorting
   * comes in: its step reaches `SUC (m * k + (k + m))` on one side and `SUC (m * k + (m + k))` on
   * the other, which differ by one commutation. Commutativity and [[AddExchange]] are handed to
   * the same conversion as **ordered** rules, firing only where they make the term smaller in
   * `Term.ordering`, so a sum sorts instead of oscillating. That is `Arithmetic`'s arrangement for
   * the ring, one operation smaller.
   *
   * [[MulCommutative]] then needs [[SuccessorTimes]] for its step and [[ZeroTimes]] for its base,
   * which is the whole reason those two come before it.
   */
  private def multiplication(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    addFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val recurrences = Vector(addFacts(AddAtZero), addFacts(AddAtSuccessor))
    val sorting = Vector(addFacts(AddCommutative), addFacts(AddExchange))

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Multiplication,
        numbers,
        "ZERO",
        "\\v:num. \\i:num. NUM_ADD v (m:num)",
        Some(m)
      )
      (theory, definition, atZero, atSuccessor) = defined

      mulAtZero <- checked(theory, notation, MulAtZero, atZero)
      mulAtSuccessor <- checked(theory, notation, MulAtSuccessor, atSuccessor)

      arithmetic = recurrences ++ Vector(mulAtZero, mulAtSuccessor, addFacts(AddAssociative))

      zeroTimes <- byInduction(driver, theory, notation, ZeroTimes, arithmetic)
      timesOne <- byRewriting(logic, theory, notation, TimesOne, arithmetic :+ addFacts(ZeroPlus))
      distributive <- byInduction(driver, theory, notation, Distributive, arithmetic)
      associative <- byInduction(
        driver,
        theory,
        notation,
        MulAssociative,
        arithmetic :+ distributive
      )
      successorTimes <- byInduction(
        driver,
        theory,
        notation,
        SuccessorTimes,
        arithmetic,
        sorting
      )
      commutative <- byInduction(
        driver,
        theory,
        notation,
        MulCommutative,
        arithmetic ++ Vector(zeroTimes, successorTimes)
      )
    } yield (
      theory,
      definition,
      Map(
        MulAtZero -> mulAtZero,
        MulAtSuccessor -> mulAtSuccessor,
        ZeroTimes -> zeroTimes,
        TimesOne -> timesOne,
        Distributive -> distributive,
        MulAssociative -> associative,
        SuccessorTimes -> successorTimes,
        MulCommutative -> commutative
      )
    )
  }

  /**
   * Exponentiation, and the one law that is the reason for having it.
   *
   * The same shape as [[multiplication]] one level up: recursion on the exponent, with the step
   * multiplying by the base rather than adding it, and the base case `SUC ZERO` rather than
   * `ZERO` because the unit is one, written in the spelling the recursion produces.
   *
   * [[PowAddsExponents]] is what a consumer wants, and it is the only one here that costs an
   * induction of its own. It is an induction on `p` whose step needs associativity of
   * multiplication, and it is the natural-number twin of `Series.POWER_ADD`: a development that
   * has the real one and not this one can take apart an exponent it has embedded and not one it
   * is still counting with, which is the position this was added from. The bridge between the
   * two, `real_of_num (NUM_POW m n) = Power (real_of_num m) n`, is NOT here: `Power` belongs to
   * `Series`, which is above this file, so the bridge belongs there with it.
   */
  private def exponentiation(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    mulFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Exponentiation,
        numbers,
        "SUC ZERO",
        "\\v:num. \\i:num. NUM_MUL v (m:num)",
        Some(m)
      )
      (theory, definition, atZero, atSuccessor) = defined

      powAtZero <- checked(theory, notation, PowAtZero, atZero)
      powAtSuccessor <- checked(theory, notation, PowAtSuccessor, atSuccessor)

      // The ADDITION recurrences are in here and not only multiplication's, because the
      // exponent on the left of [[PowAddsExponents]] is a SUM and the induction has to open it.
      // Without `NUM_ADD m ZERO = m` and `NUM_ADD ZERO n = n` the base case leaves
      // `NUM_POW m (NUM_ADD n ZERO)` against `NUM_ADD ZERO (NUM_POW m n)`, which is how the
      // omission announced itself.
      arithmetic = Vector(
        powAtZero,
        powAtSuccessor,
        mulFacts(MulAtZero),
        mulFacts(MulAtSuccessor),
        mulFacts(TimesOne),
        mulFacts(MulAssociative),
        mulFacts(AddAtZero),
        mulFacts(ZeroPlus),
        mulFacts(AddAtSuccessor))

      // `m^(n+p) = m^n * m^p` by induction on `p`: the step unfolds both sides to a product and
      // associativity is what brings the two together. The addition recurrence has to be in the
      // rules as well, since the exponent on the left is a sum that the step has to open.
      addsExponents <- byInduction(
        driver,
        theory,
        notation,
        PowAddsExponents,
        arithmetic)
      oneToAnyPower <- byInduction(driver, theory, notation, OneToAnyPower, arithmetic)
      // Not an induction: two unfoldings of multiplication and the unit, then reflexivity.
      timesTwo <- byRewriting(logic, theory, notation, TimesTwo, arithmetic)
    } yield (
      theory,
      definition,
      Map(
        PowAtZero -> powAtZero,
        PowAtSuccessor -> powAtSuccessor,
        PowAddsExponents -> addsExponents,
        OneToAnyPower -> oneToAnyPower,
        TimesTwo -> timesTwo
      )
    )
  }

  /* ------------------------------------------------------------------ order */

  /**
   * The order, defined as the existential a reader would write, and the six facts it carries.
   *
   * `m <= n` is `?d. m + d = n`, so every fact about it is a witness: reflexivity is `ZERO`,
   * `0 <= n` is `n`, `m <= SUC m` is `SUC ZERO`, and transitivity is the sum of the two witnesses
   * it was given. That is the whole of why this definition was chosen over `~(n < m)`: the
   * existential is what a proof about it opens, and each of these is one line of arithmetic under
   * that opening.
   *
   * Antisymmetry is the one that costs something, and what it costs is two lemmas about addition
   * that nothing else here needed: `m + n = m` forces `n = ZERO`, by induction on `m` through the
   * injectivity of the successor, and `m + n = ZERO` forces `m = ZERO`, by an induction whose step
   * is the successor never being zero. Those two are where the axiom of infinity finally reaches
   * the order.
   *
   * Totality and trichotomy are the deep pair and they come last, in that order: the order is
   * shown total by an induction, and then trichotomy is that with each half split on whether its
   * witness is zero. `Natural`'s case analysis on a number is what both splits are, and
   * `splitOnGap` is the step they share.
   */
  private def order(
    logic: Logic,
    base: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural,
    driver: Induct
  ): Either[LogicError, (Theory, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      nonStrictBody <- Parser.term(base, notation, "\\m:num. \\n:num. ?d:num. NUM_ADD m d = n")
      nonStrict <- LogicError.lift(Kernel.defineConstant(base, NonStrictOrder, nonStrictBody))
      (withNonStrict, nonStrictDefinition) = nonStrict

      strictBody <- Parser.term(withNonStrict, notation, "\\m:num. \\n:num. NUM_LE (SUC m) n")
      strict <- LogicError.lift(Kernel.defineConstant(withNonStrict, StrictOrder, strictBody))
      (theory, strictDefinition) = strict

      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      successorOfN <- LogicError.lift(Term.app(successor, n))
      one <- LogicError.lift(Term.app(successor, zero))

      // Reflexivity: nothing has to be added to reach yourself.
      atZeroOfN <- rules.spec(n, arithmetic(AddAtZero))
      reflexiveAt <- atMost(logic, nonStrictDefinition, n, n, zero, atZeroOfN)
      reflexive <- rules.gen(n, reflexiveAt).flatMap(checked(theory, notation, Reflexive, _))

      // Zero is least: what has to be added is the number itself.
      zeroPlusN <- rules.spec(n, arithmetic(ZeroPlus))
      leastAt <- atMost(logic, nonStrictDefinition, zero, n, n, zeroPlusN)
      least <- rules.gen(n, leastAt).flatMap(checked(theory, notation, ZeroIsLeast, _))

      // One step up: `n + SUC ZERO = SUC n`, which is the second recurrence and then the first.
      throughSuccessor <- rules.specAll(arithmetic(AddAtSuccessor), List(n, zero))
      insideSuccessor <- Conv.apTerm(successor, atZeroOfN)
      plusOne <- Conv.trans(throughSuccessor, insideSuccessor)
      belowAt <- atMost(logic, nonStrictDefinition, n, successorOfN, one, plusOne)
      below <- rules.gen(n, belowAt).flatMap(checked(theory, notation, AtMostSuccessor, _))

      transitive <- transitivity(logic, theory, notation, nonStrictDefinition, arithmetic)
      strictTransitive <- strictTransitivity(
        logic, theory, notation, strictDefinition, transitive, below)

      cancels <- cancellation(driver, theory, notation, arithmetic, naturals)
      cancelsLeft <- leftCancellation(driver, theory, notation, arithmetic, naturals)
      sumIsZero <- sumVanishes(driver, theory, notation, arithmetic, naturals)
      antiSymmetric <- antisymmetry(
        logic,
        theory,
        notation,
        nonStrictDefinition,
        arithmetic,
        (cancels, sumIsZero)
      )

      // `n < SUC n` is `SUC n <= SUC n`, which is reflexivity. That is what defining the strict
      // order through the non-strict one buys, and the reason it is defined that way round.
      strictAt <- Conv.unfold(strictDefinition, List(n, successorOfN))
      reflexiveAtSuccessor <- rules.spec(successorOfN, reflexive)
      strictly <- Conv
        .sym(strictAt)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, reflexiveAtSuccessor)))
      belowSuccessor <- rules.gen(n, strictly).flatMap(checked(theory, notation, BelowSuccessor, _))

      reached = Map(ZeroIsLeast -> least, AtMostSuccessor -> below, Transitive -> transitive)
      total <- totality(
        driver,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic,
        reached,
        naturals
      )
      trichotomy <- trichotomous(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic,
        naturals,
        total
      )

      // The strict order's own facts, which until 2026-09-11 were derived by two consumers instead:
      // `Modular` held four of them and `Bounded` two, both because this file was being changed
      // elsewhere the hour they were written. None of the six mentions anything either of those
      // defines, and a fact held outside the chain's developments is a fact `docs/lemmas.md` does
      // not list, `Library.of` collecting the chain and neither of them being in it.
      successorNotSelf <- successorIsNotItself(
        logic,
        theory,
        notation,
        arithmetic,
        cancels,
        naturals
      )
      strictIrreflexive <- strictlyIrreflexive(
        logic,
        theory,
        notation,
        strictDefinition,
        antiSymmetric,
        below,
        successorNotSelf
      )
      belowOrEqual <- belowOrEqualTo(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic,
        naturals
      )
      successorPositive <- successorIsPositive(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic
      )
      mulPositive <- productIsPositive(
        logic,
        theory,
        notation,
        naturals,
        arithmetic,
        successorPositive,
        strictIrreflexive
      )
      notBelowZero <- nothingIsBelowZero(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        sumIsZero,
        naturals
      )
      belowSuccessorCases <- belowSuccessorSplits(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic,
        naturals
      )
      atMostBelowSuc <- atMostBelowSuccessor(
        logic,
        theory,
        notation,
        (nonStrictDefinition, strictDefinition),
        arithmetic,
        naturals
      )

      atMostFromBelow <- atMostFromStrictlyBelow(
        logic,
        theory,
        notation,
        strictDefinition,
        transitive,
        below
      )
      atMostZero <- atMostZeroIsZero(
        logic,
        theory,
        notation,
        nonStrictDefinition,
        sumIsZero
      )
      atMostThenBelow <- atMostThenStrictlyBelow(
        logic,
        theory,
        notation,
        belowOrEqual,
        strictTransitive
      )
      belowThenAtMost <- strictlyBelowThenAtMost(
        logic,
        theory,
        notation,
        strictDefinition,
        transitive
      )
      strongInduction <- courseOfValues(
        logic,
        theory,
        notation,
        naturals,
        notBelowZero,
        belowSuccessorCases,
        belowSuccessor
      )
      addMonotone <- additionIsMonotone(
        logic,
        theory,
        notation,
        nonStrictDefinition,
        arithmetic(AddAssociative)
      )
      mulMonotone <- multiplicationIsMonotone(
        logic, theory, notation, nonStrictDefinition, arithmetic(Distributive))
      mulStrictlyMonotone <- multiplicationIsStrictlyMonotone(
        logic, theory, notation, nonStrictDefinition, strictDefinition, arithmetic)
      mulCancelsLeft <- multiplicationCancels(
        logic, theory, notation, mulStrictlyMonotone, trichotomy, strictIrreflexive)
      addCancelsOrder <- additionCancelsTheOrder(
        logic,
        theory,
        notation,
        nonStrictDefinition,
        arithmetic(AddAssociative),
        cancelsLeft
      )
      belowExcludesAtMost <- strictExcludesNonStrict(
        logic, theory, notation, atMostThenBelow, strictIrreflexive)
      atMostFromNotBelow <- atMostFromNotStrictlyBelow(
        logic, theory, notation, trichotomy, reflexive, atMostFromBelow)
      addCancelsStrictOrder <- additionCancelsTheStrictOrder(
        logic,
        theory,
        notation,
        strictDefinition,
        arithmetic(AddAtSuccessor),
        addCancelsOrder
      )
      atMostSum <- summandIsAtMostTheSum(
        logic, theory, notation, addMonotone, least, arithmetic(AddAtZero))
      addMonotoneBoth <- additionIsMonotoneInBoth(
        logic, theory, notation, addMonotone, transitive, arithmetic(AddCommutative))
      addStrictlyMonotone <- additionIsStrictlyMonotone(
        logic,
        theory,
        notation,
        addMonotone,
        atMostFromBelow,
        belowOrEqual,
        cancelsLeft,
        strictIrreflexive
      )

      // Last of the order, because they are the only two over a predicate the caller supplies
      // rather than facts about two numbers.
      leastPrinciple <- leastNumber(
        logic,
        driver,
        theory,
        notation,
        naturals,
        belowSuccessor,
        notBelowZero,
        belowSuccessorCases
      )
      greatestPrinciple <- greatestBounded(
        logic,
        theory,
        notation,
        naturals,
        leastPrinciple,
        belowSuccessor,
        reflexive,
        belowOrEqual,
        belowSuccessorCases,
        atMostFromBelow,
        atMostZero
      )
    } yield (
      theory,
      Map(NonStrictOrder -> nonStrictDefinition, StrictOrder -> strictDefinition),
      Map(
        Reflexive -> reflexive,
        ZeroIsLeast -> least,
        AtMostSuccessor -> below,
        Transitive -> transitive,
        StrictTransitive -> strictTransitive,
        AddCancels -> cancels,
        AddCancelsLeft -> cancelsLeft,
        SumIsZero -> sumIsZero,
        AntiSymmetric -> antiSymmetric,
        BelowSuccessor -> belowSuccessor,
        Total -> total,
        Trichotomy -> trichotomy,
        SuccessorNotSelf -> successorNotSelf,
        StrictIrreflexive -> strictIrreflexive,
        BelowOrEqual -> belowOrEqual,
        SuccessorPositive -> successorPositive,
        MulPositive -> mulPositive,
        NotBelowZero -> notBelowZero,
        BelowSuccessorCases -> belowSuccessorCases,
        AtMostBelowSuccessor -> atMostBelowSuc,
        AtMostFromBelow -> atMostFromBelow,
        AtMostThenBelow -> atMostThenBelow,
        AddMonotone -> addMonotone,
        AddStrictlyMonotone -> addStrictlyMonotone,
        AddCancelsOrder -> addCancelsOrder,
        MulMonotone -> mulMonotone,
        MulStrictlyMonotone -> mulStrictlyMonotone,
        MulCancelsLeft -> mulCancelsLeft,
        BelowExcludesAtMost -> belowExcludesAtMost,
        AtMostFromNotBelow -> atMostFromNotBelow,
        AddCancelsStrictOrder -> addCancelsStrictOrder,
        AtMostSum -> atMostSum,
        AddMonotoneBoth -> addMonotoneBoth,
        BelowThenAtMost -> belowThenAtMost,
        StrongInduction -> strongInduction,
        AtMostZero -> atMostZero,
        LeastNumber -> leastPrinciple,
        GreatestBounded -> greatestPrinciple
      )
    )
  }

  /**
   * `|- !m n. NUM_LE m n \/ NUM_LE n m`, by induction on the second.
   *
   * The base is `0 <= m`. The step has the two cases the hypothesis gives: if `m <= k` then
   * `m <= SUC k` by transitivity through `k <= SUC k`, and if `k <= m` then the witness of that
   * decides which way the new pair goes, which is what `splitOnGap` is for. Zero witness means
   * `k` is `m`, and then `m <= SUC k` is `k <= SUC k` with one name rewritten; a witness of
   * `SUC j` means `SUC k <= m`, with `j` as the new witness.
   *
   * This is the induction trichotomy rests on, and it is the only place in the file where the case
   * split on a number is used twice over: once on the hypothesis and once on a witness.
   */
  private def totality(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm],
    reached: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val (nonStrict, strict) = definitions

    for {
      statement <- stated(theory, notation, Total)
      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      relation <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      result <- driver.proveBy(
        statement,
        goal =>
          for {
            sides <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
            number <- sides._1 match {
              case App(App(_, left), _) => Right(left)
              case other => Left(NotOfForm("a bound on a number", other))
            }
            least <- rules.spec(number, reached(ZeroIsLeast))
            injected <- rules.disjIntro2(sides._1, least)
          } yield injected,
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          for {
            sides <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
            (left, right) = sides
            pieces <- left match {
              case App(App(_, subject), App(_, step)) => Right((subject, step))
              case other => Left(NotOfForm("a bound below a successor", other))
            }
            (subject, step) = pieces
            successorOfStep <- LogicError.lift(Term.app(successor, step))

            halves <- logic
              .destDisj(hypothesis.conclusion)
              .toRight(NotOfForm("a disjunction", hypothesis.conclusion))
            (below, above) = halves

            // `subject <= step`, so `subject <= SUC step` through `step <= SUC step`.
            assumedBelow <- LogicError.lift(Kernel.assume(below))
            upward <- rules.spec(step, reached(AtMostSuccessor))
            pair <- rules.conjIntro(assumedBelow, upward)
            chained <- rules
              .specAll(reached(Transitive), List(subject, step, successorOfStep))
              .flatMap(rules.mp(_, pair))
            firstCase <- rules.disjIntro1(right, chained)

            // `step <= subject`, and then it depends on the witness.
            assumedAbove <- LogicError.lift(Kernel.assume(above))
            secondCase <- splitOnGap(
              logic,
              theory,
              nonStrict,
              strict,
              arithmetic(Shift),
              arithmetic(AddAtZero),
              cases,
              step,
              subject,
              assumedAbove,
              equal =>
                for {
                  atStep <- rules.spec(step, reached(AtMostSuccessor))
                  carried <- Conv.apTerm(relation, equal).flatMap(Conv.apThm(_, successorOfStep))
                  moved <- LogicError.lift(Kernel.eqMp(carried, atStep))
                  injected <- rules.disjIntro1(right, moved)
                } yield injected,
              strictly =>
                for {
                  unfolded <- Conv.unfold(strict, List(step, subject))
                  plain <- LogicError.lift(Kernel.eqMp(unfolded, strictly))
                  injected <- rules.disjIntro2(left, plain)
                } yield injected
            )

            decided <- rules.disjElim(hypothesis, firstCase, secondCase)
          } yield decided
      )
    } yield result
  }

  /**
   * `|- !m n. NUM_LT m n \/ m = n \/ NUM_LT n m`.
   *
   * Totality gives one of the two bounds, and `splitOnGap` turns whichever it gives into the
   * strict bound or the equation, according to whether its witness is zero. The two branches are
   * the same argument with the roles swapped, which is why they are two calls of one function and
   * differ only in which disjunct they inject into.
   */
  private def trichotomous(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural,
    total: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions

    for {
      statement <- stated(theory, notation, Trichotomy)
      cases <- naturals.fact(Natural.ZeroOrSuccessor)

      // The variables the statement quantifies over, so that what is generalised at the end is
      // what was written rather than something equal to it.
      stripped <- Logic.stripForall(statement)
      subject <- stripped._1.headOption.toRight(NotOfForm("a claim about two numbers", statement))
      other <- stripped._1.lift(1).toRight(NotOfForm("a claim about two numbers", statement))
      goal = stripped._2

      sides <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
      (strictlyBelow, rest) = sides
      tail <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equalPart, strictlyAbove) = tail

      bounded <- rules.specAll(total, List(subject, other))
      halves <- logic
        .destDisj(bounded.conclusion)
        .toRight(NotOfForm("a disjunction", bounded.conclusion))
      (below, above) = halves

      assumedBelow <- LogicError.lift(Kernel.assume(below))
      firstCase <- splitOnGap(
        logic,
        theory,
        nonStrict,
        strict,
        arithmetic(Shift),
        arithmetic(AddAtZero),
        cases,
        subject,
        other,
        assumedBelow,
        equal =>
          for {
            middle <- rules.disjIntro1(strictlyAbove, equal)
            injected <- rules.disjIntro2(strictlyBelow, middle)
          } yield injected,
        strictly => rules.disjIntro1(rest, strictly)
      )

      assumedAbove <- LogicError.lift(Kernel.assume(above))
      secondCase <- splitOnGap(
        logic,
        theory,
        nonStrict,
        strict,
        arithmetic(Shift),
        arithmetic(AddAtZero),
        cases,
        other,
        subject,
        assumedAbove,
        equal =>
          for {
            flipped <- Conv.sym(equal)
            middle <- rules.disjIntro1(strictlyAbove, flipped)
            injected <- rules.disjIntro2(strictlyBelow, middle)
          } yield injected,
        strictly =>
          for {
            middle <- rules.disjIntro2(equalPart, strictly)
            injected <- rules.disjIntro2(strictlyBelow, middle)
          } yield injected
      )

      decided <- rules.disjElim(bounded, firstCase, secondCase)
      result <- rules
        .genAll(decided, List(subject, other))
        .flatMap(checked(theory, notation, Trichotomy, _))
    } yield result
  }

  /**
   * Decide a non-strict bound by its witness, and hand the caller whichever half it turned out to
   * be.
   *
   * `left <= right` says some `d` closes the gap. The case split on a number says `d` is `ZERO` or
   * a successor, and those are the two halves of `<=`: a zero gap means `left = right`, and a gap
   * of `SUC j` means `SUC left + j = right`, which is `left < right` with `j` as the witness. That
   * second step is the whole use of [[Shift]].
   *
   * The two continuations rather than a disjunction, because both callers want to build something
   * of their own out of each half and a disjunction would have to be taken apart again by each of
   * them. Both have to return the same proposition, which the case analysis checks: a caller whose
   * two branches prove different things is refused rather than given the first.
   */
  private def splitOnGap(
    logic: Logic,
    theory: Theory,
    nonStrict: Kernel.Thm,
    strict: Kernel.Thm,
    shift: Kernel.Thm,
    addAtZero: Kernel.Thm,
    cases: Kernel.Thm,
    left: Term,
    right: Term,
    evidence: Kernel.Thm,
    fromEqual: Kernel.Thm => Either[LogicError, Kernel.Thm],
    fromBelow: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    // Fresh with respect to the hypotheses as well as the conclusion: a witness that collided with
    // a variable of an assumption would narrow the case to where the two are equal, and would not
    // be refused anywhere.
    val avoid = evidence.hypotheses.foldLeft(
      Term.freeVariables(evidence.conclusion) ++ Term.freeVariables(left) ++ Term.freeVariables(right)
    )((found, hypothesis) => found ++ Term.freeVariables(hypothesis))
    val difference = Conv.freshVariable("d", numbers, avoid)
    val step = Conv.freshVariable("j", numbers, avoid + difference)

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      from <- LogicError.lift(Term.app(plus, left))

      opened <- gap(logic, nonStrict, left, right, evidence)
      reaching <- LogicError.lift(Term.app(from, difference).flatMap(Term.eq(_, right)))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      split <- rules.spec(difference, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = branches

      // A gap of zero: `left + d = left`, so `left` is `right`.
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      carried <- Conv.apTerm(from, assumedZero)
      unit <- rules.spec(left, addAtZero)
      toLeft <- Conv.trans(carried, unit)
      equal <- Conv.sym(toLeft).flatMap(Conv.trans(_, reaches))
      zeroBranch <- fromEqual(equal)

      // A gap of `SUC j`: `SUC left + j = right`, so `left` is strictly below `right`.
      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      successorOfStep <- LogicError.lift(Term.app(successor, step))
      isStep <- LogicError.lift(Term.eq(difference, successorOfStep))
      assumedStep <- LogicError.lift(Kernel.assume(isStep))
      carriedStep <- Conv.apTerm(from, assumedStep)
      shifted <- rules.specAll(shift, List(left, step))
      toShift <- Conv.trans(carriedStep, shifted)
      reachesRight <- Conv.sym(toShift).flatMap(Conv.trans(_, reaches))
      successorOfLeft <- LogicError.lift(Term.app(successor, left))
      bounded <- atMost(logic, nonStrict, successorOfLeft, right, step, reachesRight)
      unfolded <- Conv.unfold(strict, List(left, right))
      strictly <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, bounded)))
      reached <- fromBelow(strictly)
      successorBranch <- rules.existsElim(assumedSuccessor, step, reached)

      decided <- rules.disjElim(split, zeroBranch, successorBranch)
      result <- rules.existsElim(opened, difference, decided)
    } yield result
  }

  /* ------------------------------------------ the strict order's own six facts */

  /**
   * `|- !n. ~(SUC n = n)`.
   *
   * `n + SUC ZERO = SUC n` is the second recurrence and then the first, so a number equal to its
   * own successor is a number to which `SUC ZERO` may be added without changing it, and
   * [[AddCancels]] says such an addend is `ZERO`. `NUM_SUC_NOT_ZERO` at `ZERO` closes it.
   *
   * It goes through cancellation rather than through the successor's injectivity, which is the
   * thing a reader expects and which does not work: injectivity takes `SUC m = SUC n` down to
   * `m = n` and says nothing about a number and its own successor.
   */
  private def successorIsNotItself(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm],
    cancels: Kernel.Thm,
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      one <- LogicError.lift(Term.app(successor, zero))
      successorOfN <- LogicError.lift(Term.app(successor, n))

      target <- LogicError.lift(Term.eq(successorOfN, n))
      assumed <- LogicError.lift(Kernel.assume(target))

      atSuccessor <- rules.specAll(arithmetic(AddAtSuccessor), List(n, zero))
      atZero <- rules.spec(n, arithmetic(AddAtZero))
      inside <- Conv.apTerm(successor, atZero)
      plusOne <- Conv.trans(atSuccessor, inside)

      reached <- Conv.trans(plusOne, assumed)
      vanishes <- rules.specAll(cancels, List(one, n)).flatMap(rules.mp(_, reached))
      never <- rules.spec(zero, notZero)
      absurd <- rules.notElim(never, vanishes)
      denied <- rules.notIntro(target, absurd)
      general <- rules.gen(n, denied)
      result <- checked(theory, notation, SuccessorNotSelf, general)
    } yield result
  }

  /**
   * `|- !n. ~(NUM_LT n n)`.
   *
   * `NUM_LT n n` **is** `NUM_LE (SUC n) n` by definition, and `NUM_LE n (SUC n)` is already a fact,
   * so antisymmetry gives `SUC n = n` and [[successorIsNotItself]] denies it.
   */
  private def strictlyIrreflexive(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strict: Kernel.Thm,
    antiSymmetric: Kernel.Thm,
    atMostSuccessor: Kernel.Thm,
    successorNotSelf: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      successorOfN <- LogicError.lift(Term.app(successor, n))

      unfolded <- Conv.unfold(strict, List(n, n))
      target <- leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(target))
      bounded <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      other <- rules.spec(n, atMostSuccessor)
      pair <- rules.conjIntro(bounded, other)
      equal <- rules.specAll(antiSymmetric, List(successorOfN, n)).flatMap(rules.mp(_, pair))

      never <- rules.spec(n, successorNotSelf)
      absurd <- rules.notElim(never, equal)
      denied <- rules.notIntro(target, absurd)
      general <- rules.gen(n, denied)
      result <- checked(theory, notation, StrictIrreflexive, general)
    } yield result
  }

  /**
   * `|- !m n. NUM_LE m n ==> NUM_LT m n \/ m = n`.
   *
   * [[splitOnGap]] with the two continuations being the two injections, which is all it is: the
   * private function decides a non-strict bound by its witness and hands each half over, and this
   * puts the halves back into a disjunction.
   *
   * That it is [[splitOnGap]] and not a second argument was worth measuring, because `Modular`
   * proved the same statement a different way while this file was being changed elsewhere: from
   * trichotomy, with the third case refuted by [[strictlyIrreflexive]]. Both are correct and both
   * reach the identical term, which is how the two were compared. Counted on 2026-09-11 with
   * `Derivation.size`: 8379 inferences through the gap and 13385 through trichotomy. The difference
   * is [[Trichotomy]] itself, 11044 on its own and the deepest theorem in the file, which a question
   * about one pair does not need.
   */
  private def belowOrEqualTo(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))

      premise <- LogicError.lift(Term.appAll(atMostConstant, List(m, n)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      strictly <- LogicError.lift(Term.appAll(lessThan, List(m, n)))
      equal <- LogicError.lift(Term.eq(m, n))

      decided <- splitOnGap(
        logic,
        theory,
        nonStrict,
        strict,
        arithmetic(Shift),
        arithmetic(AddAtZero),
        cases,
        m,
        n,
        assumed,
        proved => rules.disjIntro2(strictly, proved),
        proved => rules.disjIntro1(equal, proved)
      )

      discharged <- rules.disch(premise, decided)
      general <- rules.genAll(discharged, List(m, n))
      result <- checked(theory, notation, BelowOrEqual, general)
    } yield result
  }


  /**
   * [[MulPositive]]: a product of positives is a successor, and a successor is positive.
   *
   * Neither factor can be zero, so `Natural.ZeroOrSuccessor` makes each one a successor; then
   * `m * SUC n'` is `m * n' + m` by [[MulAtSuccessor]] and `m` is itself `SUC m'`, so
   * [[AddAtSuccessor]] pulls the successor outside and [[SuccessorPositive]] closes it.
   *
   * The route through successors rather than through the order is what keeps it short. Arguing it
   * as an order fact would want cancellation or a case split on which factor is larger, and neither
   * is needed: what is being shown is that the product is not zero, and "is a successor" is the
   * strongest way to say that here.
   */
  private def productIsPositive(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    arithmetic: Map[String, Kernel.Thm],
    successorPositive: Kernel.Thm,
    strictIrreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      times <- LogicError.lift(
        theory.constant(Multiplication, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      strict <- LogicError.lift(theory.constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool))))

      positiveM <- LogicError.lift(Term.appAll(strict, List(zero, m)))
      positiveN <- LogicError.lift(Term.appAll(strict, List(zero, n)))
      product <- LogicError.lift(Term.appAll(times, List(m, n)))
      goal <- LogicError.lift(Term.appAll(strict, List(zero, product)))
      assumedM <- LogicError.lift(Kernel.assume(positiveM))
      assumedN <- LogicError.lift(Kernel.assume(positiveN))

      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      atSuccessor <- arithmetic.get(MulAtSuccessor).toRight(MissingDefinition(MulAtSuccessor))
      addAtSuccessor <- arithmetic.get(AddAtSuccessor).toRight(MissingDefinition(AddAtSuccessor))

      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      belowZero <- LogicError.lift(Term.app(strict, zero))

      reached <- asSuccessor(
        logic, cases, strictIrreflexive, assumedM, m, zero, belowZero, goal, Set(m, n)
      ) { (leftInner, leftIs) =>
          asSuccessor(
            logic, cases, strictIrreflexive, assumedN, n, zero, belowZero, goal, Set(m, n, leftInner)
          ) { (rightInner, rightIs) =>
              for {
                // `m * n = m * SUC n' = m * n' + m`
                timesM <- LogicError.lift(Term.app(times, m))
                opened <- Conv.apTerm(timesM, rightIs)
                stepped <- rules.specAll(atSuccessor, List(m, rightInner))
                asProduct <- Conv.trans(opened, stepped)

                // `m * n' + m = m * n' + SUC m' = SUC (m * n' + m')`
                scaled <- LogicError.lift(Term.appAll(times, List(m, rightInner)))
                plusScaled <- LogicError.lift(Term.app(plus, scaled))
                tail <- Conv.apTerm(plusScaled, leftIs)
                asSum <- rules.specAll(addAtSuccessor, List(scaled, leftInner))
                whole <- Conv.trans(asProduct, tail).flatMap(Conv.trans(_, asSum))

                inside <- Term
                  .destEq(whole.conclusion)
                  .map(_._2)
                  .toRight(NotOfForm("an equation", whole.conclusion))
                argument <- inside match {
                  case App(_, value) => Right(value)
                  case other => Left(NotOfForm("a successor", other))
                }
                positive <- rules.spec(argument, successorPositive)
                back <- Conv.sym(whole)
                carried <- Conv.apTerm(belowZero, back)
                result <- LogicError.lift(Kernel.eqMp(carried, positive))
              } yield result
          }
      }

      dischargedN <- rules.disch(positiveN, reached)
      dischargedM <- rules.disch(positiveM, dischargedN)
      general <- rules.genAll(dischargedM, List(m, n))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", general.conclusion))
    } yield general
  }

  /**
   * A positive number is a successor, and the caller gets the predecessor and the equation.
   *
   * `Natural.ZeroOrSuccessor` offers zero or a successor; the zero arm is refuted by the positivity
   * the caller holds, since it would make `ZERO` below itself.
   */
  private def asSuccessor(
    logic: Logic,
    cases: Kernel.Thm,
    strictIrreflexive: Kernel.Thm,
    positive: Kernel.Thm,
    subject: Term,
    zero: Term,
    belowZero: Term,
    goal: Term,
    avoid: Set[FVar]
  )(
    reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      split <- rules.spec(subject, cases)
      arms <- logic.destDisj(split.conclusion).toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = arms

      refuted <- for {
        assumed <- LogicError.lift(Kernel.assume(isZero))
        carried <- Conv.apTerm(belowZero, assumed)
        absurd <- LogicError.lift(Kernel.eqMp(carried, positive))
        never <- rules.spec(zero, strictIrreflexive)
        contradiction <- rules.notElim(never, absurd)
        anything <- rules.falsityElim(goal, contradiction)
      } yield anything

      taken <- withPredecessor(logic, isSuccessor, avoid)(reach)
      result <- rules.disjElim(split, refuted, taken)
    } yield result
  }

  /** Open `?y. subject = SUC y` and hand the predecessor and the equation over. */
  private def withPredecessor(
    logic: Logic,
    existential: Term,
    avoid: Set[FVar]
  )(
    reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      assumedExists <- LogicError.lift(Kernel.assume(existential))
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      // Avoiding the caller's variables and not only this existential's: the two factors are
      // opened one inside the other, so a name chosen against the inner statement alone collides
      // with the outer predecessor and the elimination refuses with "k occurs free".
      variable = Conv.freshVariable("k", numbers, avoid ++ Term.freeVariables(existential))
      applied <- LogicError.lift(Term.app(predicate, variable))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumed <- LogicError.lift(Kernel.assume(instance))
      reached <- reach(variable, assumed)
      result <- rules.existsElim(assumedExists, variable, reached)
    } yield result
  }

  /**
   * `|- !n. NUM_LT ZERO (SUC n)`.
   *
   * `NUM_LT ZERO (SUC n)` is `NUM_LE (SUC ZERO) (SUC n)` by definition, and `n` closes that gap:
   * `SUC ZERO + n = SUC n` is [[SuccessorPlus]] and then [[ZeroPlus]] under a successor. One
   * witness and nothing else, which is what defining the strict order through the non-strict one
   * buys everywhere else in this file too.
   */
  private def successorIsPositive(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      one <- LogicError.lift(Term.app(successor, zero))
      successorOfN <- LogicError.lift(Term.app(successor, n))

      fromSuccessor <- rules.specAll(arithmetic(SuccessorPlus), List(zero, n))
      fromZero <- rules.spec(n, arithmetic(ZeroPlus))
      inside <- Conv.apTerm(successor, fromZero)
      reaches <- Conv.trans(fromSuccessor, inside)

      bounded <- atMost(logic, nonStrict, one, successorOfN, n, reaches)
      unfolded <- Conv.unfold(strict, List(zero, successorOfN))
      strictly <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, bounded)))
      general <- rules.gen(n, strictly)
      result <- checked(theory, notation, SuccessorPositive, general)
    } yield result
  }

  /**
   * `|- !i. ~(NUM_LT i ZERO)`.
   *
   * `NUM_LT i ZERO` unfolds twice to `?d. NUM_ADD (SUC i) d = ZERO`, and [[SumIsZero]] turns any
   * witness of that into `SUC i = ZERO`, which `NUM_SUC_NOT_ZERO` refuses. Open the existential,
   * contradict, close.
   */
  private def nothingIsBelowZero(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    sumIsZero: Kernel.Thm,
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions
    val numbers = TyApp(Natural.TypeName, Nil)
    val i = Term.variable("i", numbers)

    for {
      successorNotZero <- naturals.fact(Natural.SuccessorNotZero)
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      successorOfI <- LogicError.lift(Term.app(successor, i))
      from <- LogicError.lift(Term.app(plus, successorOfI))

      unfolded <- Conv.unfold(strict, List(i, zero))
      guard <- leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(guard))
      bounded <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      existential <- gap(logic, nonStrict, successorOfI, zero, bounded)

      difference = Conv.freshVariable("d", numbers, Term.freeVariables(guard))
      sum <- LogicError.lift(Term.app(from, difference))
      reaching <- LogicError.lift(Term.eq(sum, zero))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      isZero <- rules
        .specAll(sumIsZero, List(successorOfI, difference))
        .flatMap(rules.mp(_, reaches))
      never <- rules.spec(i, successorNotZero)
      absurd <- rules.notElim(never, isZero)
      closed <- rules.existsElim(existential, difference, absurd)

      negated <- rules.notIntro(guard, closed)
      general <- rules.gen(i, negated)
      result <- checked(theory, notation, NotBelowZero, general)
    } yield result
  }

  /**
   * `|- !n i. NUM_LT i (SUC n) ==> NUM_LT i n \/ i = n`.
   *
   * `NUM_LT i (SUC n)` is `?d. NUM_ADD (SUC i) d = SUC n`, and the case split on `d` is the whole
   * argument. A gap of `ZERO` gives `SUC i = SUC n`, so `i = n` by injectivity. A gap of `SUC j`
   * gives `SUC (NUM_ADD (SUC i) j) = SUC n` through [[AddAtSuccessor]], so
   * `NUM_ADD (SUC i) j = n` by the same injectivity, and that is `NUM_LE (SUC i) n` with `j` as its
   * witness, which is `NUM_LT i n`.
   *
   * [[Shift]] does not appear, which is worth a line because [[splitOnGap]] is the same shape and
   * needs it. There the gap is opened on `NUM_LE left right` and a successor has to be moved across
   * the sum to reach a strict bound; here the sum already carries the successor on the left, and
   * what moves is the one on the right, which is what the recurrence says directly.
   */
  /**
   * `|- !n i. NUM_LT i (SUC n) ==> NUM_LE i n`, and the witness never moves.
   *
   * `NUM_LT i (SUC n)` **is** `?d. NUM_ADD (SUC i) d = SUC n`, and `NUM_LE i n` **is**
   * `?d. NUM_ADD i d = n`. So the whole of the proof is that the two existentials have the same
   * witness: [[SuccessorPlus]] moves the step out of the sum on the left, and the injectivity of
   * the successor takes it off both sides.
   *
   * [[BelowSuccessorCases]] reaches the same fact through a disjunction with an equation in one
   * branch, which a caller then has to eliminate. This one has no case split, and a consumer
   * under `SUM_CONGRUENCE_BELOW` at a bound of `SUC n` wants exactly this shape.
   */
  /**
   * `|- !n i. NUM_LE i n ==> NUM_LE n (NUM_SUB (NUM_ADD n n) i)`, and the witness does the work.
   *
   * `i + d = n` gives `n + n = i + (d + n)` by associativity; [[AddCommutative]] moves the `i` to
   * where [[SumMinus]] takes it off with nothing owed, since nothing was truncated; and `d + n`
   * is at least `n` by [[AtMostSum]] commuted. No case split and no order fact beyond the two the
   * definition unfolds to.
   */
  private def atMostDoubleMinus(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrict: Kernel.Thm,
    arithmetic: Map[String, Kernel.Thm],
    sumMinus: Kernel.Thm,
    atMostSum: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    /** Rewrite the last argument of an application, which is all the congruence here needs. */
    def inLastArgument(
      equation: Kernel.Thm,
      theorem: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      theorem.conclusion match {
        case App(partial, _) =>
          Conv
            .apTerm(partial, equation)
            .flatMap(congruence => LogicError.lift(Kernel.eqMp(congruence, theorem)))
        case other => Left(NotOfForm("an application", other))
      }

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      minus <- LogicError.lift(
        theory.constant(Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (i:num) (n:num)")
      assumed <- LogicError.lift(Kernel.assume(below))
      existential <- gap(logic, nonStrict, i, n, assumed)

      difference = Conv.freshVariable("d", numbers, Term.freeVariables(below))
      reaching <- LogicError.lift(
        Term.appAll(plus, List(i, difference)).flatMap(Term.eq(_, n)))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      // `n + n = (i + d) + n = i + (d + n)`, and then the `i` goes to the other side of the sum.
      doubled <- Conv
        .sym(reaches)
        .flatMap(equation => Conv.apThm(Conv.apTerm(plus, equation).getOrElse(equation), n))
      associated <- rules.specAll(arithmetic(AddAssociative), List(i, difference, n))
      shaped <- Conv.trans(doubled, associated)
      rest <- LogicError.lift(Term.appAll(plus, List(difference, n)))
      swapped <- rules.specAll(arithmetic(AddCommutative), List(i, rest))
      moved <- Conv.trans(shaped, swapped)

      cancelled <- rules.specAll(sumMinus, List(rest, i))
      carried <- Conv.apTerm(minus, moved).flatMap(Conv.apThm(_, i))
      difference0 <- Conv.trans(carried, cancelled)

      reached <- rules
        .specAll(atMostSum, List(n, difference))
        .flatMap(atMost =>
          rules
            .specAll(arithmetic(AddCommutative), List(n, difference))
            .flatMap(commuted => inLastArgument(commuted, atMost)))
      result <- Conv
        .sym(difference0)
        .flatMap(equation => inLastArgument(equation, reached))
        .flatMap(rules.existsElim(existential, difference, _))
        .flatMap(rules.disch(below, _))
        .flatMap(rules.genAll(_, List(n, i)))
        .flatMap(checked(theory, notation, AtMostDoubleMinus, _))
    } yield result
  }

  private def atMostBelowSuccessor(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    for {
      injective <- naturals.fact(Natural.SuccessorInjective)
      successorPlus <- arithmetic.get(SuccessorPlus).toRight(MissingDefinition(SuccessorPlus))

      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      successorOfN <- LogicError.lift(Term.app(successor, n))
      successorOfI <- LogicError.lift(Term.app(successor, i))

      unfolded <- Conv.unfold(strict, List(i, successorOfN))
      guard <- leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(guard))
      bounded <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      existential <- gap(logic, nonStrict, successorOfI, successorOfN, bounded)

      difference = Conv.freshVariable("d", numbers, Term.freeVariables(guard))
      sum <- LogicError.lift(Term.appAll(plus, List(successorOfI, difference)))
      reaching <- LogicError.lift(Term.eq(sum, successorOfN))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      pushed <- rules.specAll(successorPlus, List(i, difference))
      stepped <- Conv.sym(pushed).flatMap(Conv.trans(_, reaches))
      inside <- LogicError.lift(Term.appAll(plus, List(i, difference)))
      cancelled <- rules.specAll(injective, List(inside, n)).flatMap(rules.mp(_, stepped))

      atMost <- Conv.unfold(nonStrict, List(i, n))
      body <- rightOf(atMost)
      predicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))
      witnessed <- rules.existsIntro(predicate, difference, cancelled)
      folded <- Conv
        .sym(atMost)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))

      withoutWitness <- rules.existsElim(existential, difference, folded)
      result <- rules
        .disch(guard, withoutWitness)
        .flatMap(rules.genAll(_, List(n, i)))
        .flatMap(checked(theory, notation, AtMostBelowSuccessor, _))
    } yield result
  }

  private def belowSuccessorSplits(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: (Kernel.Thm, Kernel.Thm),
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (nonStrict, strict) = definitions
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    for {
      injective <- naturals.fact(Natural.SuccessorInjective)
      cases <- naturals.fact(Natural.ZeroOrSuccessor)

      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))
      successorOfN <- LogicError.lift(Term.app(successor, n))
      successorOfI <- LogicError.lift(Term.app(successor, i))
      from <- LogicError.lift(Term.app(plus, successorOfI))

      unfolded <- Conv.unfold(strict, List(i, successorOfN))
      guard <- leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(guard))
      bounded <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      existential <- gap(logic, nonStrict, successorOfI, successorOfN, bounded)

      strictlyBelow <- LogicError.lift(Term.appAll(lessThan, List(i, n)))
      equalTo <- LogicError.lift(Term.eq(i, n))

      // Fresh against the hypothesis as well as the conclusion, for the reason [[splitOnGap]]
      // gives: a witness colliding with a variable already in play would narrow the case to where
      // the two are equal, and would be refused nowhere.
      avoid = Term.freeVariables(guard) ++ Term.freeVariables(strictlyBelow)
      difference = Conv.freshVariable("d", numbers, avoid)
      step = Conv.freshVariable("j", numbers, avoid + difference)

      sum <- LogicError.lift(Term.app(from, difference))
      reaching <- LogicError.lift(Term.eq(sum, successorOfN))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      split <- rules.spec(difference, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = branches

      // A gap of zero: `SUC i + ZERO` is `SUC i`, so the two successors are equal.
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      carried <- Conv.apTerm(from, assumedZero)
      unit <- rules.spec(successorOfI, arithmetic(AddAtZero))
      toSuccessor <- Conv.trans(carried, unit)
      sameSuccessor <- Conv.sym(toSuccessor).flatMap(Conv.trans(_, reaches))
      equal <- rules.specAll(injective, List(i, n)).flatMap(rules.mp(_, sameSuccessor))
      zeroBranch <- rules.disjIntro2(strictlyBelow, equal)

      // A gap of `SUC j`: the successor comes out of the sum, and `j` is the witness one down.
      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      successorOfStep <- LogicError.lift(Term.app(successor, step))
      isStep <- LogicError.lift(Term.eq(difference, successorOfStep))
      assumedStep <- LogicError.lift(Kernel.assume(isStep))
      carriedStep <- Conv.apTerm(from, assumedStep)
      recurrence <- rules.specAll(arithmetic(AddAtSuccessor), List(successorOfI, step))
      toStep <- Conv.trans(carriedStep, recurrence)
      sameStep <- Conv.sym(toStep).flatMap(Conv.trans(_, reaches))
      shorter <- LogicError.lift(Term.app(from, step))
      reachesN <- rules.specAll(injective, List(shorter, n)).flatMap(rules.mp(_, sameStep))

      atMostN <- atMost(logic, nonStrict, successorOfI, n, step, reachesN)
      unfoldedAtN <- Conv.unfold(strict, List(i, n))
      strictly <- Conv
        .sym(unfoldedAtN)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atMostN)))
      injected <- rules.disjIntro1(equalTo, strictly)
      successorBranch <- rules.existsElim(assumedSuccessor, step, injected)

      decided <- rules.disjElim(split, zeroBranch, successorBranch)
      closed <- rules.existsElim(existential, difference, decided)
      implied <- rules.disch(guard, closed)
      general <- rules.gen(i, implied).flatMap(rules.gen(n, _))
      result <- checked(theory, notation, BelowSuccessorCases, general)
    } yield result
  }

  /**
   * `|- !m n. NUM_LT m n ==> NUM_LE m n`.
   *
   * `NUM_LT m n` **is** `NUM_LE (SUC m) n`, so the successor is on the wrong side and one step of
   * transitivity through `NUM_LE m (SUC m)` puts it back.
   */
  private def atMostFromStrictlyBelow(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strict: Kernel.Thm,
    transitive: Kernel.Thm,
    atMostSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      successorOfM <- LogicError.lift(Term.app(successor, m))

      unfolded <- Conv.unfold(strict, List(m, n))
      premise <- leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(premise))
      bounded <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      upward <- rules.spec(m, atMostSuccessor)
      pair <- rules.conjIntro(upward, bounded)
      chained <- rules
        .specAll(transitive, List(m, successorOfM, n))
        .flatMap(rules.mp(_, pair))

      discharged <- rules.disch(premise, chained)
      general <- rules.genAll(discharged, List(m, n))
      result <- checked(theory, notation, AtMostFromBelow, general)
    } yield result
  }

  /**
   * `|- !n. NUM_LE n ZERO ==> n = ZERO`.
   *
   * The bound unfolds to `?d. NUM_ADD n d = ZERO`, and [[SumIsZero]] reads the answer off any
   * witness of it.
   */
  /**
   * [[AtMostThenBelow]]: at most, then strictly below, is strictly below.
   *
   * [[BelowOrEqual]] turns `m <= n` into `m < n` or `m = n`. The first branch is
   * [[StrictTransitive]]; the second carries the equation into `n < p` under a fixed context, which
   * is a congruence rather than a rewrite because `m` and `n` both occur elsewhere in the goal.
   */
  /**
   * [[AddMonotone]], by carrying the witness of the order across one associativity.
   *
   * `NUM_LE m n` is `?d. m + d = n` and nothing else, so the derivation opens that `d`, rewrites
   * `(p + m) + d` into `p + (m + d)`, and puts the same `d` back. No induction and no case split:
   * the order on `num` is a statement about a difference, and a common summand does not touch it.
   */
  /**
   * [[BelowThenAtMost]], by unfolding the strict order and never making a case split.
   *
   * `NUM_LT m n` is `NUM_LE (SUC m) n` by definition, so the premise is already a non-strict
   * comparison and [[Transitive]] takes it the rest of the way. It is shorter than
   * [[AtMostThenBelow]] for that reason and not by luck: the definition puts the successor on the
   * side this one needs it on.
   */
  private def strictlyBelowThenAtMost(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strictDefinition: Kernel.Thm,
    transitive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val p = Term.variable("p", numbers)

    for {
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))
      successorConstant <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      strictly <- LogicError.lift(Term.appAll(lessThan, List(m, n)))
      atMost <- LogicError.lift(Term.appAll(atMostConstant, List(n, p)))
      premise <- logic.mkConj(strictly, atMost)
      assumed <- LogicError.lift(Kernel.assume(premise))
      strictHalf <- rules.conjElim1(assumed)
      atMostHalf <- rules.conjElim2(assumed)

      opened <- Conv
        .unfold(strictDefinition, List(m, n))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, strictHalf)))
      successor <- LogicError.lift(Term.app(successorConstant, m))
      chained <- rules
        .conjIntro(opened, atMostHalf)
        .flatMap(pair =>
          rules.specAll(transitive, List(successor, n, p)).flatMap(rules.mp(_, pair))
        )
      folded <- Conv
        .unfold(strictDefinition, List(m, p))
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chained)))

      discharged <- rules.disch(premise, folded)
      general <- rules.genAll(discharged, List(m, n, p))
      result <- checked(theory, notation, BelowThenAtMost, general)
    } yield result
  }

  /**
   * [[StrongInduction]], by ordinary induction over "every number below this one".
   *
   * The predicate inducted on is not the caller's: it is `\n. !m. NUM_LT m n ==> P m`, whose base
   * holds because nothing is below zero and whose step needs only that below a successor is below
   * or equal. The caller's claim comes out at the end by reading that predicate at `SUC n`, where
   * `n` itself is one of the numbers below.
   *
   * `Induct.proveBy` cannot run it, for the reason `Language`'s numerals meet: the hypothesis has
   * to be quantified over the other variable, and that driver leaves the others free.
   */
  private def courseOfValues(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    notBelowZero: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    belowSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val claim = Term.variable("P", Type.fun(numbers, Type.Bool))
    val index = Term.variable("n", numbers)

    for {
      lessThan <- LogicError.lift(
        theory.constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      successorConstant <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      /* The step the caller hands over, assumed once. */
      atIndex <- LogicError.lift(Term.app(claim, index))
      belowIndex = Conv.freshVariable("m", numbers, Set(claim, index))
      belowTerm <- LogicError.lift(Term.appAll(lessThan, List(belowIndex, index)))
      atBelow <- LogicError.lift(Term.app(claim, belowIndex))
      inner <- logic.mkImp(belowTerm, atBelow)
      everyBelow <- logic.mkForall(belowIndex, inner)
      stepBody <- logic.mkImp(everyBelow, atIndex)
      stepTerm <- logic.mkForall(index, stepBody)
      assumedStep <- LogicError.lift(Kernel.assume(stepTerm))

      /* The predicate actually inducted on, which is not the caller's. */
      carrier <- LogicError.lift(Term.abs(index, everyBelow))
      induction <- naturals.fact(Natural.Induction)
      instance <- rules.spec(carrier, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTermOfInduction) = halves

      /* Nothing is below zero. */
      base <- for {
        stripped <- Logic.stripForall(baseTerm)
        variable <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every number", baseTerm))
        body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        assumed <- LogicError.lift(Kernel.assume(body._1))
        never <- rules.spec(variable, notBelowZero)
        contradiction <- rules.notElim(never, assumed)
        anything <- rules.falsityElim(body._2, contradiction)
        result <- rules.disch(body._1, anything).flatMap(rules.gen(variable, _))
      } yield result

      /* Below a successor is below or equal, and equal is where the caller's step is spent. */
      step <- for {
        stripped <- Logic.stripForall(stepTermOfInduction)
        variable <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every number", stepTermOfInduction))
        parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        assumedBelow <- LogicError.lift(Kernel.assume(parts._1))
        innerStripped <- Logic.stripForall(parts._2)
        target <- innerStripped._1.headOption
          .toRight(NotOfForm("a claim about every number", parts._2))
        body <- logic.destImp(innerStripped._2).toRight(NotOfForm("an implication", innerStripped._2))
        assumedTarget <- LogicError.lift(Kernel.assume(body._1))

        cases <- rules
          .specAll(belowSuccessorCases, List(variable, target))
          .flatMap(rules.mp(_, assumedTarget))
        split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))

        fromBelow <- LogicError
          .lift(Kernel.assume(split._1))
          .flatMap(held => rules.spec(target, assumedBelow).flatMap(rules.mp(_, held)))

        fromEqual <- for {
          assumedEqual <- LogicError.lift(Kernel.assume(split._2))
          here <- rules.spec(variable, assumedStep).flatMap(rules.mp(_, assumedBelow))
          backwards <- Conv.sym(assumedEqual)
          carried <- Conv
            .apTerm(claim, backwards)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, here)))
        } yield carried

        settled <- rules.disjElim(cases, fromBelow, fromEqual)
        result <- rules
          .disch(body._1, settled)
          .flatMap(rules.gen(target, _))
          .flatMap(rules.disch(parts._1, _))
          .flatMap(rules.gen(variable, _))
      } yield result

      everywhere <- rules.conjIntro(base, step).flatMap(rules.mp(opened, _))

      /* The caller's claim, read off at the successor where the number itself sits below. */
      successorOfIndex <- LogicError.lift(Term.app(successorConstant, index))
      atSuccessor <- rules.spec(successorOfIndex, everywhere)
      reaches <- rules.spec(index, belowSuccessor)
      here <- rules.spec(index, atSuccessor).flatMap(rules.mp(_, reaches))
      general <- rules.gen(index, here)
      discharged <- rules.disch(stepTerm, general).flatMap(rules.gen(claim, _))
      result <- checked(theory, notation, StrongInduction, discharged)
    } yield result
  }

  private def additionIsMonotone(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrictDefinition: Kernel.Thm,
    associative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmeticType = Type.fun(numbers, Type.fun(numbers, numbers))
    val p = Term.variable("p", numbers)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      plus <- LogicError.lift(theory.constant(Addition, arithmeticType))

      premise <- LogicError.lift(Term.appAll(atMostConstant, List(m, n)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      opened <- Conv
        .unfold(nonStrictDefinition, List(m, n))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))

      shifted <- LogicError.lift(Term.appAll(plus, List(p, m)))
      target <- LogicError.lift(Term.appAll(plus, List(p, n)))
      wanted <- LogicError.lift(Term.appAll(atMostConstant, List(shifted, target)))
      unfoldedWanted <- Conv.unfold(nonStrictDefinition, List(shifted, target))
      body <- Term
        .destEq(unfoldedWanted.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", unfoldedWanted.conclusion))
      predicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))

      witnessed <- withDifference(logic, plus, associative, opened, p, m, predicate)
      back <- Conv.sym(unfoldedWanted)
      carried <- LogicError.lift(Kernel.eqMp(back, witnessed))
      _ <-
        if (carried.conclusion == wanted) Right(())
        else Left(NotOfForm("the order it was asked for", carried.conclusion))
      discharged <- rules.disch(premise, carried)
      general <- rules.genAll(discharged, List(p, m, n))
      result <- checked(theory, notation, AddMonotone, general)
    } yield result
  }

  /**
   * [[MulMonotone]], which is [[additionIsMonotone]] with the distribution in place of the
   * associativity.
   *
   * The same shape and the same length: the premise's witness `d` gives `p * n = p * m + p * d`,
   * so `p * d` is the difference the conclusion asks for.
   */
  private def multiplicationIsMonotone(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrictDefinition: Kernel.Thm,
    distributive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmeticType = Type.fun(numbers, Type.fun(numbers, numbers))
    val p = Term.variable("p", numbers)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      times <- LogicError.lift(theory.constant(Multiplication, arithmeticType))

      premise <- LogicError.lift(Term.appAll(atMostConstant, List(m, n)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      opened <- Conv
        .unfold(nonStrictDefinition, List(m, n))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))

      left <- LogicError.lift(Term.appAll(times, List(p, m)))
      right <- LogicError.lift(Term.appAll(times, List(p, n)))
      unfoldedWanted <- Conv.unfold(nonStrictDefinition, List(left, right))
      body <- rightOf(unfoldedWanted)
      predicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))

      inner <- logic
        .destExistsPredicate(opened.conclusion)
        .toRight(NotOfForm("an existential", opened.conclusion))
      difference = Conv.freshVariable("d", numbers, Set(p, m, n))
      applied <- LogicError.lift(Term.app(inner, difference))
      contraction <- Conv.betaRoot(applied)
      instance <- rightOf(contraction)
      held <- LogicError.lift(Kernel.assume(instance))

      spread <- rules.specAll(distributive, List(p, m, difference))
      partial <- LogicError.lift(Term.app(times, p))
      carried <- Conv.apTerm(partial, held)
      reached <- Conv.sym(spread).flatMap(Conv.trans(_, carried))
      product <- LogicError.lift(Term.appAll(times, List(p, difference)))
      witnessed <- rules.existsIntro(predicate, product, reached)
      closed <- rules.existsElim(opened, difference, witnessed)

      back <- Conv.sym(unfoldedWanted)
      result <- LogicError.lift(Kernel.eqMp(back, closed))
      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(p, m, n))
      checked <- checked(theory, notation, MulMonotone, general)
    } yield checked
  }

  /**
   * [[MulStrictlyMonotone]], by carrying the witness across the two recurrences of addition.
   *
   * `NUM_LT m n` unfolds twice, to `?d. SUC m + d = n`, and the same for `ZERO < p`, which gives a
   * `c` with `SUC ZERO + c = p` and so `p = SUC c`. From there the arithmetic is one chain:
   *
   * {{{
   * SUC (p * m) + (c + p * d)
   *   = (SUC (p * m) + c) + p * d     associativity
   *   = (p * SUC m) + p * d           the chain below, which is the whole lemma
   *   = p * (SUC m + d)               distribution
   *   = p * n                         the premise's witness
   * }}}
   *
   * and the middle step is `SUC (p * m) + c = SUC (p * m + c) = p * m + SUC c = p * m + p`, which
   * `NUM_MUL_SUC` turns into `p * SUC m`.
   */
  private def multiplicationIsStrictlyMonotone(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrictDefinition: Kernel.Thm,
    strictDefinition: Kernel.Thm,
    arithmetic: String => Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmeticType = Type.fun(numbers, Type.fun(numbers, numbers))
    val p = Term.variable("p", numbers)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    /** A theorem of `a < b` opened into the existential the two definitions give. */
    def opened(held: Kernel.Thm, a: Term, b: Term, successor: Term => Term)
      : Either[LogicError, Kernel.Thm] =
      for {
        strict <- Conv
          .unfold(strictDefinition, List(a, b))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, held)))
        result <- Conv
          .unfold(nonStrictDefinition, List(successor(a), b))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, strict)))
      } yield result

    for {
      belowConstant <- LogicError.lift(theory.constant(StrictOrder, relation))
      times <- LogicError.lift(theory.constant(Multiplication, arithmeticType))
      plus <- LogicError.lift(theory.constant(Addition, arithmeticType))
      successorConstant <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
      zeroTerm <- Parser.term(theory, notation, "ZERO", numbers)

      successor = (subject: Term) =>
        Term.app(successorConstant, subject).getOrElse(subject)

      positiveTerm <- LogicError.lift(Term.appAll(belowConstant, List(zeroTerm, p)))
      positive <- LogicError.lift(Kernel.assume(positiveTerm))
      premise <- LogicError.lift(Term.appAll(belowConstant, List(m, n)))
      held <- LogicError.lift(Kernel.assume(premise))

      positiveWitness <- opened(positive, zeroTerm, p, successor)
      openedPremise <- opened(held, m, n, successor)

      product <- LogicError.lift(Term.appAll(times, List(p, m)))
      target <- LogicError.lift(Term.appAll(times, List(p, n)))
      wantedStrict <- Conv.unfold(strictDefinition, List(product, target))
      wantedAtMost <- Conv.unfold(nonStrictDefinition, List(successor(product), target))
      body <- rightOf(wantedAtMost)
      predicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))

      witnessed <- withTwoDifferences(
        logic, theory, arithmetic, openedPremise, positiveWitness, predicate,
        times, plus, successorConstant, zeroTerm, p, m, n)

      asAtMost <- Conv
        .sym(wantedAtMost)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))
      asStrict <- Conv
        .sym(wantedStrict)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, asAtMost)))
      discharged <- rules.disch(premise, asStrict).flatMap(rules.disch(positiveTerm, _))
      general <- rules.genAll(discharged, List(p, m, n))
      result <- checked(theory, notation, MulStrictlyMonotone, general)
    } yield result
  }

  /** The chain [[multiplicationIsStrictlyMonotone]]'s docstring writes out, with both witnesses. */
  private def withTwoDifferences(
    logic: Logic,
    theory: Theory,
    arithmetic: String => Kernel.Thm,
    premise: Kernel.Thm,
    positive: Kernel.Thm,
    predicate: Term,
    times: Term,
    plus: Term,
    successorConstant: Term,
    zeroTerm: Term,
    p: FVar,
    m: FVar,
    n: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        inner <- logic
          .destExistsPredicate(existential.conclusion)
          .toRight(NotOfForm("an existential", existential.conclusion))
        fresh = Conv.freshVariable(
          name, numbers, taken ++ Term.freeVariables(existential.conclusion))
        applied <- LogicError.lift(Term.app(inner, fresh))
        contraction <- Conv.betaRoot(applied)
        body <- rightOf(contraction)
        assumed <- LogicError.lift(Kernel.assume(body))
        reached <- reach(fresh, assumed)
        result <- rules.existsElim(existential, fresh, reached)
      } yield result

    open(premise, "d", Set(p, m, n)) { (d, instance) =>
      open(positive, "c", Set(p, m, n, d)) { (c, atC) =>
        for {
          product <- LogicError.lift(Term.appAll(times, List(p, m)))
          successorOfM <- LogicError.lift(Term.app(successorConstant, m))
          successorOfProduct <- LogicError.lift(Term.app(successorConstant, product))
          productOfD <- LogicError.lift(Term.appAll(times, List(p, d)))

          // `p = SUC c`, read back off the witness of `ZERO < p`.
          stepped <- rules.specAll(arithmetic(SuccessorPlus), List(zeroTerm, c))
          leftZero <- rules
            .spec(c, arithmetic(ZeroPlus))
            .flatMap(Conv.apTerm(successorConstant, _))
          isSuccessor <- Conv
            .sym(atC)
            .flatMap(reversed => Conv.trans(stepped, leftZero).flatMap(Conv.trans(reversed, _)))

          // `SUC (p * m) + c = p * SUC m`.
          first <- rules.specAll(arithmetic(SuccessorPlus), List(product, c))
          second <- rules.specAll(arithmetic(AddAtSuccessor), List(product, c)).flatMap(Conv.sym)
          partialSum <- LogicError.lift(Term.app(plus, product))
          third <- Conv.sym(isSuccessor).flatMap(Conv.apTerm(partialSum, _))
          fourth <- rules.specAll(arithmetic(MulAtSuccessor), List(p, m)).flatMap(Conv.sym)
          middle <- Conv
            .trans(third, fourth)
            .flatMap(tail => Conv.trans(second, tail).flatMap(Conv.trans(first, _)))

          regrouped <- rules
            .specAll(arithmetic(AddAssociative), List(successorOfProduct, c, productOfD))
            .flatMap(Conv.sym)
          spread <- Conv.apTerm(plus, middle).flatMap(Conv.apThm(_, productOfD))
          distributed <- rules
            .specAll(arithmetic(Distributive), List(p, successorOfM, d))
            .flatMap(Conv.sym)
          partialProduct <- LogicError.lift(Term.app(times, p))
          carried <- Conv.apTerm(partialProduct, instance)

          reached <- Conv
            .trans(distributed, carried)
            .flatMap(tail => Conv.trans(spread, tail).flatMap(Conv.trans(regrouped, _)))
          difference <- LogicError.lift(Term.appAll(plus, List(c, productOfD)))
          result <- rules.existsIntro(predicate, difference, reached)
        } yield result
      }
    }
  }

  /** [[MulCancelsLeft]]: trichotomy, and either order makes a product strictly below itself. */
  private def multiplicationCancels(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strictlyMonotone: Kernel.Thm,
    trichotomy: Kernel.Thm,
    strictIrreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmeticType = Type.fun(numbers, Type.fun(numbers, numbers))
    val p = Term.variable("p", numbers)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      belowConstant <- LogicError.lift(theory.constant(StrictOrder, relation))
      times <- LogicError.lift(theory.constant(Multiplication, arithmeticType))
      zeroTerm <- Parser.term(theory, notation, "ZERO", numbers)

      positiveTerm <- LogicError.lift(Term.appAll(belowConstant, List(zeroTerm, p)))
      positive <- LogicError.lift(Kernel.assume(positiveTerm))
      left <- LogicError.lift(Term.appAll(times, List(p, m)))
      right <- LogicError.lift(Term.appAll(times, List(p, n)))
      premise <- LogicError.lift(Term.eq(left, right))
      held <- LogicError.lift(Kernel.assume(premise))
      target <- LogicError.lift(Term.eq(m, n))

      cases <- rules.specAll(trichotomy, List(m, n))
      first <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      rest <- logic.destDisj(first._2).toRight(NotOfForm("a disjunction", first._2))

      /* One order refuted: the products are strictly ordered and the equation identifies them. */
      refuted = (assumed: Term, lower: Term, upper: Term, fixed: Term, forwards: Boolean) =>
        for {
          order <- LogicError.lift(Kernel.assume(assumed))
          strict <- rules
            .specAll(strictlyMonotone, List(p, lower, upper))
            .flatMap(rules.mp(_, positive))
            .flatMap(rules.mp(_, order))
          equation <- if (forwards) Right(held) else Conv.sym(held)
          moved <- Conv
            .apTerm(belowConstant, equation)
            .flatMap(Conv.apThm(_, fixed))
            .flatMap(step => LogicError.lift(Kernel.eqMp(step, strict)))
          never <- rules.spec(fixed, strictIrreflexive)
          absurd <- rules.notElim(never, moved)
          reached <- rules.falsityElim(target, absurd)
        } yield reached

      fromBelow <- refuted(first._1, m, n, right, true)
      fromEqual <- LogicError.lift(Kernel.assume(rest._1))
      fromAbove <- refuted(rest._2, n, m, left, false)

      tail <- logic
        .mkDisj(rest._1, rest._2)
        .flatMap(subject => LogicError.lift(Kernel.assume(subject)))
      inner <- rules.disjElim(tail, fromEqual, fromAbove)
      settled <- rules.disjElim(cases, fromBelow, inner)

      discharged <- rules.disch(premise, settled).flatMap(rules.disch(positiveTerm, _))
      general <- rules.genAll(discharged, List(p, m, n))
      result <- checked(theory, notation, MulCancelsLeft, general)
    } yield result
  }

  /**
   * [[AddCancelsOrder]], by taking the difference back out of the shifted comparison.
   *
   * [[additionIsMonotone]] read backwards and the same length. The premise carries a `d` with
   * `(p + m) + d = p + n`; one associativity regroups that into `p + (m + d) = p + n`;
   * [[AddCancelsLeft]] takes `p` off both sides and what is left, `m + d = n`, is the conclusion's
   * own witness. No induction and no case split, for the reason the sibling gives.
   *
   * The route a reader expects is the other one, through [[Trichotomy]] and
   * [[BelowExcludesAtMost]]: suppose `n < m`, shift it, and contradict the premise. That works and
   * was rejected here for being longer and for making a classical case split out of a statement
   * about a difference, which is all this is.
   */
  private def additionCancelsTheOrder(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrictDefinition: Kernel.Thm,
    associative: Kernel.Thm,
    cancelsLeft: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmeticType = Type.fun(numbers, Type.fun(numbers, numbers))
    val p = Term.variable("p", numbers)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      plus <- LogicError.lift(theory.constant(Addition, arithmeticType))

      shifted <- LogicError.lift(Term.appAll(plus, List(p, m)))
      target <- LogicError.lift(Term.appAll(plus, List(p, n)))
      premise <- LogicError.lift(Term.appAll(atMostConstant, List(shifted, target)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      opened <- Conv
        .unfold(nonStrictDefinition, List(shifted, target))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))

      unfoldedWanted <- Conv.unfold(nonStrictDefinition, List(m, n))
      body <- rightOf(unfoldedWanted)
      predicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))

      witnessed <- withoutTheSummand(
        logic, plus, associative, cancelsLeft, opened, p, m, n, predicate)
      back <- Conv.sym(unfoldedWanted)
      carried <- LogicError.lift(Kernel.eqMp(back, witnessed))
      discharged <- rules.disch(premise, carried)
      general <- rules.genAll(discharged, List(p, m, n))
      result <- checked(theory, notation, AddCancelsOrder, general)
    } yield result
  }

  /** [[BelowExcludesAtMost]]: assume the other order and the strict one becomes reflexive. */
  private def strictExcludesNonStrict(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    atMostThenBelow: Kernel.Thm,
    strictIrreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val left = Term.variable("m", numbers)
    val right = Term.variable("n", numbers)

    for {
      below <- LogicError.lift(
        theory.constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      premise <- LogicError.lift(Term.appAll(below, List(left, right)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      other <- LogicError.lift(Term.appAll(atMost, List(right, left)))
      otherAssumed <- LogicError.lift(Kernel.assume(other))
      chained <- rules.conjIntro(otherAssumed, assumed)
      reflexive <- rules
        .specAll(atMostThenBelow, List(right, left, right))
        .flatMap(rules.mp(_, chained))
      absurd <- rules.spec(right, strictIrreflexive).flatMap(rules.notElim(_, reflexive))
      refused <- rules.notIntro(other, absurd)
      discharged <- rules.disch(premise, refused)
      general <- rules.genAll(discharged, List(left, right))
      result <- checked(theory, notation, BelowExcludesAtMost, general)
    } yield result
  }

  /**
   * `|- !m n. ~(NUM_LT m n) ==> NUM_LE n m`, by eliminating [[Trichotomy]].
   *
   * One disjunction elimination over the three cases and no classical step: the disjunction is
   * already a theorem here, so what the negated premise does is close the first branch rather than
   * open a case split. The middle branch is [[Reflexive]] with one name rewritten and the last is
   * [[AtMostFromBelow]].
   */
  private def atMostFromNotStrictlyBelow(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    trichotomy: Kernel.Thm,
    reflexive: Kernel.Thm,
    atMostFromBelow: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val left = Term.variable("m", numbers)
    val right = Term.variable("n", numbers)

    for {
      below <- LogicError.lift(
        theory.constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      goal <- LogicError.lift(Term.appAll(atMost, List(right, left)))
      strict <- LogicError.lift(Term.appAll(below, List(left, right)))
      premise <- logic.mkNot(strict)
      assumed <- LogicError.lift(Kernel.assume(premise))

      cases <- rules.specAll(trichotomy, List(left, right))
      parts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (first, rest) = parts
      inner <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equal, other) = inner

      // `m < n` is the branch the premise refuses, so it proves the goal the way anything follows
      // from a contradiction.
      assumedFirst <- LogicError.lift(Kernel.assume(first))
      absurd <- rules.notElim(assumed, assumedFirst)
      fromFirst <- rules.falsityElim(goal, absurd)

      // `m = n` carries `NUM_LE n n` to `NUM_LE n m` across the equation itself.
      assumedEqual <- LogicError.lift(Kernel.assume(equal))
      atRight <- LogicError.lift(Term.app(atMost, right))
      moved <- Conv.apTerm(atRight, assumedEqual)
      atBoth <- rules.spec(right, reflexive)
      fromEqual <- Conv.sym(moved).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atBoth)))

      assumedOther <- LogicError.lift(Kernel.assume(other))
      fromOther <- rules.specAll(atMostFromBelow, List(right, left)).flatMap(rules.mp(_, assumedOther))

      assumedRest <- LogicError.lift(Kernel.assume(rest))
      fromRest <- rules.disjElim(assumedRest, fromEqual, fromOther)
      reached <- rules.disjElim(cases, fromFirst, fromRest)

      discharged <- rules.disch(premise, reached)
      general <- rules.genAll(discharged, List(left, right))
      result <- checked(theory, notation, AtMostFromNotBelow, general)
    } yield result
  }

  /**
   * `|- !p m n. NUM_LT (NUM_ADD p m) (NUM_ADD p n) ==> NUM_LT m n`, through the definition.
   *
   * `NUM_LT a b` **is** `NUM_LE (SUC a) b`, so the premise is `NUM_LE (SUC (p + m)) (p + n)`, and
   * [[AddAtSuccessor]] read backwards says `SUC (p + m)` is `p + SUC m`. That is
   * [[AddCancelsOrder]]'s shape exactly, and what it gives back is `NUM_LE (SUC m) n`, which is the
   * conclusion with the definition folded again. No induction and no case split.
   */
  private def additionCancelsTheStrictOrder(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strictDefinition: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    addCancelsOrder: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val summand = Term.variable("p", numbers)
    val left = Term.variable("m", numbers)
    val right = Term.variable("n", numbers)

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      leftSum <- LogicError.lift(Term.appAll(plus, List(summand, left)))
      rightSum <- LogicError.lift(Term.appAll(plus, List(summand, right)))

      opened <- Conv.unfold(strictDefinition, List(leftSum, rightSum))
      premise <- Term
        .destEq(opened.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", opened.conclusion))
      assumed <- LogicError.lift(Kernel.assume(premise))
      nonStrict <- LogicError.lift(Kernel.eqMp(opened, assumed))

      // `p + SUC m = SUC (p + m)`, used from right to left so that the comparison is a sum in
      // both arguments and the cancellation applies.
      shifted <- rules.specAll(addAtSuccessor, List(summand, left))
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      restated <- Conv.apTerm(atMost, shifted).flatMap(Conv.apThm(_, rightSum))
      carried <- Conv
        .sym(restated)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, nonStrict)))

      successorOfLeft <- LogicError.lift(Term.app(successor, left))
      cancelled <- rules
        .specAll(addCancelsOrder, List(summand, successorOfLeft, right))
        .flatMap(rules.mp(_, carried))

      folded <- Conv.unfold(strictDefinition, List(left, right))
      strict <- Conv
        .sym(folded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, cancelled)))

      discharged <- rules.disch(premise, strict)
      general <- rules.genAll(discharged, List(summand, left, right))
      result <- checked(theory, notation, AddCancelsStrictOrder, general)
    } yield result
  }

  /** [[AtMostSum]]: [[AddMonotone]] at zero, with the identity rewritten away. */
  /**
   * [[AddMonotoneBoth]]: one summand's bound and the other's, put together.
   *
   * [[AddMonotone]] shifts on the left, so the second step has to be read through
   * [[AddCommutative]]: `d + a <= d + b` is the one-sided lemma at `d`, and what the conclusion
   * wants is `a + d <= b + d`. Both commutations are carried on the relation rather than proved
   * again, and [[Transitive]] joins the two steps.
   */
  private def additionIsMonotoneInBoth(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    addMonotone: Kernel.Thm,
    transitive: Kernel.Thm,
    addCommutative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val c = Term.variable("c", numbers)
    val d = Term.variable("d", numbers)

    for {
      statement <- stated(theory, notation, AddMonotoneBoth)
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )

      premiseLeft <- LogicError.lift(Term.appAll(atMost, List(a, b)))
      premiseRight <- LogicError.lift(Term.appAll(atMost, List(c, d)))
      premise <- logic.mkConj(premiseLeft, premiseRight)
      assumed <- LogicError.lift(Kernel.assume(premise))
      first <- rules.conjElim1(assumed)
      second <- rules.conjElim2(assumed)

      // `a + c <= a + d`, the right-hand summand moving under a fixed left one
      onTheRight <- rules.specAll(addMonotone, List(a, c, d)).flatMap(rules.mp(_, second))

      // `d + a <= d + b`, which is the same lemma at the other summand, read into `a + d <= b + d`
      shifted <- rules.specAll(addMonotone, List(d, a, b)).flatMap(rules.mp(_, first))
      commutedLeft <- rules.specAll(addCommutative, List(d, a))
      commutedRight <- rules.specAll(addCommutative, List(d, b))
      sumDA <- LogicError.lift(Term.appAll(plus, List(d, a)))
      sumAD <- LogicError.lift(Term.appAll(plus, List(a, d)))
      sumDB <- LogicError.lift(Term.appAll(plus, List(d, b)))
      movedLeft <- Conv
        .apTerm(atMost, commutedLeft)
        .flatMap(Conv.apThm(_, sumDB))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, shifted)))
      partial <- LogicError.lift(Term.app(atMost, sumAD))
      onTheLeft <- Conv
        .apTerm(partial, commutedRight)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, movedLeft)))

      sumAC <- LogicError.lift(Term.appAll(plus, List(a, c)))
      sumBD <- LogicError.lift(Term.appAll(plus, List(b, d)))
      chained <- rules
        .conjIntro(onTheRight, onTheLeft)
        .flatMap(pair =>
          rules.specAll(transitive, List(sumAC, sumAD, sumBD)).flatMap(rules.mp(_, pair))
        )

      discharged <- rules.disch(premise, chained)
      result <- rules.genAll(discharged, List(a, b, c, d))
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm(s"$AddMonotoneBoth as it is written", result.conclusion))
    } yield result
  }

  /**
   * [[PartialSumMonotoneBelow]] by induction on the bound, which is [[congruenceOnARange]]'s shape.
   *
   * The base does not use the hypothesis: both sums are `ZERO` by the zero recurrence, and nothing
   * is below itself in the strict order, so what closes it is reflexivity carried across the two
   * equations. The step takes the induction hypothesis apart exactly as the congruence does — the
   * agreement below the successor gives the agreement below the variable, by transitivity with
   * `v < SUC v` — and what is left is `NUM_SUM f v + f v <= NUM_SUM g v + g v`, which is
   * [[AddMonotoneBoth]] on the two bounds and not an arithmetic fact of its own.
   */
  private def monotoneOnARange(
    logic: Logic,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    strictTransitive: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    reflexive: Kernel.Thm,
    addMonotoneBoth: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    /** The head of `NUM_LT a b`, read off a statement that uses it rather than rebuilt. */
    def strictlyBelow(sample: Term): Either[LogicError, Term] = sample match {
      case App(App(head, _), _) => Right(head)
      case other => Left(NotOfForm("an order statement", other))
    }

    /**
     * `|- R x' y'` from `|- R x y` and the two equations `x = x'` and `y = y'`.
     *
     * One side at a time, because a relation is two applications and an equation moves under one
     * of them: the left equation is carried at the right side as it still stands, and the right
     * equation at the left side as it has become.
     */
    def acrossBoth(
      relation: Term,
      left: Kernel.Thm,
      right: Kernel.Thm,
      fact: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        rightStart <- Term
          .destEq(right.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an equation", right.conclusion))
        movedLeft <- Conv.apTerm(relation, left).flatMap(Conv.apThm(_, rightStart))
        onLeft <- LogicError.lift(Kernel.eqMp(movedLeft, fact))
        leftEnd <- Term
          .destEq(left.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", left.conclusion))
        partial <- LogicError.lift(Term.app(relation, leftEnd))
        movedRight <- Conv.apTerm(partial, right)
        result <- LogicError.lift(Kernel.eqMp(movedRight, onLeft))
      } yield result

    for {
      statement <- stated(theory, notation, PartialSumMonotoneBelow)
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      stripped <- Logic.stripForall(statement)
      (outer, inner) = stripped
      summands = outer.take(2).toList
      left <- outer.lift(0).toRight(NotOfForm("two summands", inner))
      right <- outer.lift(1).toRight(NotOfForm("two summands", inner))
      bound <- outer.lift(2).toRight(NotOfForm("a bound to induct on", inner))
      overEveryBound <- logic.mkForall(bound, inner)

      proved <- driver.proveBy(
        overEveryBound,
        goal =>
          for {
            parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
            unfoldLeft <- rules.spec(left, atZero).flatMap(Conv.sym)
            unfoldRight <- rules.spec(right, atZero).flatMap(Conv.sym)
            atNothing <- rules.spec(zero, reflexive)
            base <- acrossBoth(atMost, unfoldLeft, unfoldRight, atNothing)
            _ <-
              if (base.conclusion == parts._2) Right(())
              else Left(NotOfForm("the empty range as it is written", base.conclusion))
            result <- rules.disch(parts._1, base)
          } yield result,
        step =>
          for {
            goalParts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
            (agreesBelowSuccessor, orderedSums) = goalParts
            assumed <- LogicError.lift(Kernel.assume(agreesBelowSuccessor))
            atTheVariable <- rules.spec(step.variable, belowSuccessor)

            openedPremise <- Logic.stripForall(agreesBelowSuccessor)
            innerParts <- logic
              .destImp(openedPremise._2)
              .toRight(NotOfForm("a bounded agreement", openedPremise._2))
            below <- strictlyBelow(innerParts._1)
            index <- openedPremise._1.lift(0).toRight(NotOfForm("one index", openedPremise._2))
            smallerTerm <- LogicError.lift(Term.app(below, index).flatMap(Term.app(_, step.variable)))
            smaller <- LogicError.lift(Kernel.assume(smallerTerm))

            successor <- atTheVariable.conclusion match {
              case App(App(_, _), above) => Right(above)
              case other => Left(NotOfForm("an order statement", other))
            }
            liftedAt <- rules
              .spec(index, strictTransitive)
              .flatMap(rules.spec(step.variable, _))
              .flatMap(rules.spec(successor, _))
            chained <- rules.conjIntro(smaller, atTheVariable).flatMap(rules.mp(liftedAt, _))
            agreementAt <- rules.spec(index, assumed).flatMap(rules.mp(_, chained))
            agreesBelow <- rules.disch(smallerTerm, agreementAt).flatMap(rules.gen(index, _))

            sumsBelow <- rules.mp(step.hypothesis, agreesBelow)
            top <- rules.spec(step.variable, assumed).flatMap(rules.mp(_, atTheVariable))

            together <- rules.conjIntro(sumsBelow, top).flatMap { pair =>
              for {
                arguments <- sumsBelow.conclusion match {
                  case App(App(_, sumLeft), sumRight) =>
                    top.conclusion match {
                      case App(App(_, topLeft), topRight) =>
                        Right(List(sumLeft, sumRight, topLeft, topRight))
                      case other => Left(NotOfForm("an order statement", other))
                    }
                  case other => Left(NotOfForm("an order statement", other))
                }
                applied <- rules.specAll(addMonotoneBoth, arguments).flatMap(rules.mp(_, pair))
              } yield applied
            }

            unfoldLeft <- rules
              .spec(left, atSuccessor)
              .flatMap(rules.spec(step.variable, _))
              .flatMap(Conv.sym)
            unfoldRight <- rules
              .spec(right, atSuccessor)
              .flatMap(rules.spec(step.variable, _))
              .flatMap(Conv.sym)
            settled <- acrossBoth(atMost, unfoldLeft, unfoldRight, together)
            _ <-
              if (settled.conclusion == orderedSums) Right(())
              else Left(NotOfForm("the sums at the successor as they are written", settled.conclusion))
            result <- rules.disch(agreesBelowSuccessor, settled)
          } yield result
      )
      general <- rules.genAll(proved, summands)
    } yield general
  }

  private def summandIsAtMostTheSum(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    addMonotone: Kernel.Thm,
    zeroIsLeast: Kernel.Thm,
    addAtZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val left = Term.variable("m", numbers)
    val right = Term.variable("n", numbers)

    for {
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      atMost <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      atZero <- rules.spec(right, zeroIsLeast)
      shifted <- rules
        .specAll(addMonotone, List(left, zero, right))
        .flatMap(rules.mp(_, atZero))
      identity <- rules.spec(left, addAtZero)
      sum <- LogicError.lift(Term.appAll(plus, List(left, right)))
      moved <- Conv
        .apTerm(atMost, identity)
        .flatMap(Conv.apThm(_, sum))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, shifted)))
      general <- rules.genAll(moved, List(left, right))
      result <- checked(theory, notation, AtMostSum, general)
    } yield result
  }

  /**
   * [[AddStrictlyMonotone]], out of the published facts and without touching a definition.
   *
   * The shift keeps `NUM_LE`, so what is left is to rule out equality, and addition cancelling on
   * the left turns that into `m = n` against `m < n`. Derived rather than proved by induction
   * because every piece of it is already a lemma: an induction here would be a second proof of
   * things this file has proved twice already.
   */
  private def additionIsStrictlyMonotone(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    addMonotone: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    belowOrEqual: Kernel.Thm,
    addCancelsLeft: Kernel.Thm,
    strictIrreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val shift = Term.variable("p", numbers)
    val left = Term.variable("m", numbers)
    val right = Term.variable("n", numbers)

    for {
      below <- LogicError.lift(
        theory.constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      premise <- LogicError.lift(Term.appAll(below, List(left, right)))
      assumed <- LogicError.lift(Kernel.assume(premise))

      shiftedLeft <- LogicError.lift(Term.appAll(plus, List(shift, left)))
      shiftedRight <- LogicError.lift(Term.appAll(plus, List(shift, right)))
      goal <- LogicError.lift(Term.appAll(below, List(shiftedLeft, shiftedRight)))

      atMost <- rules.specAll(atMostFromBelow, List(left, right)).flatMap(rules.mp(_, assumed))
      shifted <- rules
        .specAll(addMonotone, List(shift, left, right))
        .flatMap(rules.mp(_, atMost))
      split <- rules
        .specAll(belowOrEqual, List(shiftedLeft, shiftedRight))
        .flatMap(rules.mp(_, shifted))

      parts <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (strict, equal) = parts

      // The equal case: cancelling the shift gives `m = n`, and `m < n` then reads `m < m`.
      sameAssumed <- LogicError.lift(Kernel.assume(equal))
      same <- rules
        .specAll(addCancelsLeft, List(left, right, shift))
        .flatMap(rules.mp(_, sameAssumed))
      headed <- LogicError.lift(Term.app(below, left))
      reflexive <- Conv
        .apTerm(headed, same)
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))
      absurd <- rules
        .spec(left, strictIrreflexive)
        .flatMap(rules.notElim(_, reflexive))
      anyway <- rules.falsityElim(goal, absurd)

      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      settled <- rules.disjElim(split, strictAssumed, anyway)
      discharged <- rules.disch(premise, settled)
      general <- rules.genAll(discharged, List(shift, left, right))
      result <- checked(theory, notation, AddStrictlyMonotone, general)
    } yield result
  }

  /** Open `?d. m + d = n`, shift both sides by `p`, and put the same `d` back. */
  private def withDifference(
    logic: Logic,
    plus: Term,
    associative: Kernel.Thm,
    existential: Kernel.Thm,
    shift: Term,
    lower: Term,
    predicate: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      inner <- logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("an existential", existential.conclusion))
      difference = Conv.freshVariable(
        "d",
        numbers,
        Term.freeVariables(existential.conclusion) ++ Term.freeVariables(predicate)
      )
      applied <- LogicError.lift(Term.app(inner, difference))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumed <- LogicError.lift(Kernel.assume(instance))

      // `(p + m) + d = p + (m + d) = p + n`, the second step being the witness itself.
      regrouped <- rules.specAll(associative, List(shift, lower, difference))
      shiftedRight <- LogicError
        .lift(Term.app(plus, shift))
        .flatMap(Conv.apTerm(_, assumed))
      reached <- Conv.trans(regrouped, shiftedRight)
      witnessed <- rules.existsIntro(predicate, difference, reached)
      result <- rules.existsElim(existential, difference, witnessed)
    } yield result
  }

  /**
   * The difference of a shifted comparison is the difference of the plain one.
   *
   * [[withDifference]] in the other direction: that one puts a witness under a shift, this one
   * takes the shift off the witness. Written as its own method for the same reason, which is that
   * the opening of the existential is where a free variable escapes if the conclusion is handed
   * back out instead of being reached inside.
   */
  private def withoutTheSummand(
    logic: Logic,
    plus: Term,
    associative: Kernel.Thm,
    cancelsLeft: Kernel.Thm,
    existential: Kernel.Thm,
    shift: Term,
    lower: Term,
    upper: Term,
    predicate: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      inner <- logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("an existential", existential.conclusion))
      difference = Conv.freshVariable(
        "d",
        numbers,
        Term.freeVariables(existential.conclusion) ++ Term.freeVariables(predicate)
      )
      applied <- LogicError.lift(Term.app(inner, difference))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumed <- LogicError.lift(Kernel.assume(instance))

      // `p + (m + d) = (p + m) + d = p + n`, and then `p` comes off both ends.
      regrouped <- rules.specAll(associative, List(shift, lower, difference))
      reached <- Conv.sym(regrouped).flatMap(Conv.trans(_, assumed))
      carried <- LogicError.lift(Term.appAll(plus, List(lower, difference)))
      cancelled <- rules
        .specAll(cancelsLeft, List(carried, upper, shift))
        .flatMap(rules.mp(_, reached))
      witnessed <- rules.existsIntro(predicate, difference, cancelled)
      result <- rules.existsElim(existential, difference, witnessed)
    } yield result
  }

  private def atMostThenStrictlyBelow(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    belowOrEqual: Kernel.Thm,
    strictTransitive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val p = Term.variable("p", numbers)

    for {
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))

      atMost <- LogicError.lift(Term.appAll(atMostConstant, List(m, n)))
      strictly <- LogicError.lift(Term.appAll(lessThan, List(n, p)))
      premise <- logic.mkConj(atMost, strictly)
      assumed <- LogicError.lift(Kernel.assume(premise))
      atMostHalf <- rules.conjElim1(assumed)
      strictHalf <- rules.conjElim2(assumed)

      cases <- rules.specAll(belowOrEqual, List(m, n)).flatMap(rules.mp(_, atMostHalf))
      split <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (below, equal) = split

      fromBelow <- for {
        assumedBelow <- LogicError.lift(Kernel.assume(below))
        pair <- rules.conjIntro(assumedBelow, strictHalf)
        settled <- rules.specAll(strictTransitive, List(m, n, p)).flatMap(rules.mp(_, pair))
      } yield settled

      fromEqual <- for {
        assumedEqual <- LogicError.lift(Kernel.assume(equal))
        backwards <- Conv.sym(assumedEqual)
        carried <- Conv.apTerm(lessThan, backwards).flatMap(Conv.apThm(_, p))
        settled <- LogicError.lift(Kernel.eqMp(carried, strictHalf))
      } yield settled

      reached <- rules.disjElim(cases, fromBelow, fromEqual)
      discharged <- rules.disch(premise, reached)
      general <- rules.genAll(discharged, List(m, n, p))
      result <- checked(theory, notation, AtMostThenBelow, general)
    } yield result
  }

  private def atMostZeroIsZero(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    nonStrict: Kernel.Thm,
    sumIsZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val n = Term.variable("n", numbers)

    for {
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      from <- LogicError.lift(Term.app(plus, n))

      premise <- LogicError.lift(Term.appAll(atMostConstant, List(n, zero)))
      assumed <- LogicError.lift(Kernel.assume(premise))
      existential <- gap(logic, nonStrict, n, zero, assumed)

      difference = Conv.freshVariable("d", numbers, Term.freeVariables(premise))
      sum <- LogicError.lift(Term.app(from, difference))
      reaching <- LogicError.lift(Term.eq(sum, zero))
      reaches <- LogicError.lift(Kernel.assume(reaching))
      isZero <- rules.specAll(sumIsZero, List(n, difference)).flatMap(rules.mp(_, reaches))

      closed <- rules.existsElim(existential, difference, isZero)
      discharged <- rules.disch(premise, closed)
      general <- rules.gen(n, discharged)
      result <- checked(theory, notation, AtMostZero, general)
    } yield result
  }

  /* ------------------------------------------------- the least-number principle */

  /**
   * `|- !P. (?n. P n) ==> (?m. P m /\ (!k. NUM_LT k m ==> ~(P k)))`.
   *
   * Ordinary induction proves nothing about `P` directly: the statement is not of the form `!n. Q
   * n` for any `Q` built out of `P`. What is, is the **auxiliary**
   *
   * {{{
   *   !n. (?j. NUM_LT j n /\ P j) ==> (?m. P m /\ (!k. NUM_LT k m ==> ~(P k)))
   * }}}
   *
   * which says that a witness below any bound produces a least one, and that is an induction on
   * the bound. The bound is **strict** and that is the choice worth recording: with `NUM_LE` the
   * base case has `P ZERO` still to deal with, and with `NUM_LT` it is vacuous by
   * [[nothingIsBelowZero]] and costs nothing. `Modular`'s docstring proposed the non-strict form;
   * this is the same argument with the cheaper base.
   *
   * The step is where the classical case split is, on whether anything below the **old** bound
   * satisfies `P`. If something does, the induction hypothesis answers and the new bound is not
   * looked at. If nothing does, then the witness the new bound supplies can only be the old bound
   * itself, by [[belowSuccessorSplits]], and that same absence is exactly the minimality the
   * conclusion asks for: nothing below it satisfies `P`, and the proof of that is one instance of
   * the negated existential.
   *
   * Finally `?n. P n` is turned into a bounded one by [[BelowSuccessor]]: `n < SUC n`, so the
   * auxiliary at `SUC n` applies.
   */
  private def leastNumber(
    logic: Logic,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    belowSuccessor: Kernel.Thm,
    notBelowZero: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))

    for {
      statement <- stated(theory, notation, LeastNumber)
      stripped <- Logic.stripForall(statement)
      predicate <- stripped._1.headOption
        .toRight(NotOfForm("a claim about a predicate", statement))
      halves <- logic
        .destImp(stripped._2)
        .toRight(NotOfForm("an implication", stripped._2))
      (somewhere, conclusion) = halves

      excludedMiddle <- naturals.classical.fact(Classical.ExcludedMiddle)
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      taken = Term.freeVariables(statement)
      bound = Conv.freshVariable("n", numbers, taken)
      index = Conv.freshVariable("j", numbers, taken + bound)
      belowBound <- LogicError.lift(Term.appAll(lessThan, List(index, bound)))
      holdsThere <- LogicError.lift(Term.app(predicate, index))
      together <- logic.mkConj(belowBound, holdsThere)
      someBelow <- logic.mkExists(index, together)
      auxiliaryBody <- logic.mkImp(someBelow, conclusion)
      auxiliary <- logic.mkForall(bound, auxiliaryBody)

      descent <- driver.proveBy(
        auxiliary,
        goal => nothingBelowZeroIsLeast(logic, notBelowZero, goal),
        step =>
          oneBoundHigher(logic, excludedMiddle, belowSuccessorCases, lessThan, predicate, step)
      )

      // `?n. P n` is not yet a bounded claim, and `n < SUC n` is what makes it one.
      chosen <- logic
        .destExistsPredicate(somewhere)
        .toRight(NotOfForm("an existential quantification", somewhere))
      assumed <- LogicError.lift(Kernel.assume(somewhere))
      found = Conv.freshVariable("n", numbers, taken ++ Term.freeVariables(conclusion))
      applied <- LogicError.lift(Term.app(chosen, found))
      contraction <- Conv.betaRoot(applied)
      instance <- rightOf(contraction)
      assumedInstance <- LogicError.lift(Kernel.assume(instance))

      successorOfFound <- LogicError.lift(Term.app(successor, found))
      atBound <- rules.spec(successorOfFound, descent)
      guarded <- logic
        .destImp(atBound.conclusion)
        .toRight(NotOfForm("an implication", atBound.conclusion))
      bounded <- logic
        .destExistsPredicate(guarded._1)
        .toRight(NotOfForm("an existential quantification", guarded._1))
      aboveFound <- rules.spec(found, belowSuccessor)
      pair <- rules.conjIntro(aboveFound, assumedInstance)
      introduced <- rules.existsIntro(bounded, found, pair)
      reached <- rules.mp(atBound, introduced)

      closed <- rules.existsElim(assumed, found, reached)
      discharged <- rules.disch(somewhere, closed)
      general <- rules.gen(predicate, discharged)
      result <- checked(theory, notation, LeastNumber, general)
    } yield result
  }

  /**
   * The base of [[leastNumber]]: nothing is below `ZERO`, so the antecedent cannot hold.
   *
   * The one place the choice of a strict bound pays. With `NUM_LE` in the auxiliary this case would
   * have `P ZERO` in hand and would have to build the conclusion from it.
   */
  private def nothingBelowZeroIsLeast(
    logic: Logic,
    notBelowZero: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      halves <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (antecedent, conclusion) = halves
      assumed <- LogicError.lift(Kernel.assume(antecedent))
      predicate <- logic
        .destExistsPredicate(antecedent)
        .toRight(NotOfForm("an existential quantification", antecedent))
      domain <- Type
        .destFun(Term.typeOf(predicate))
        .map(_._1)
        .toRight(NotOfForm("a predicate", predicate))

      index = Conv.freshVariable(
        "j",
        domain,
        Term.freeVariables(antecedent) ++ Term.freeVariables(conclusion)
      )
      applied <- LogicError.lift(Term.app(predicate, index))
      contraction <- Conv.betaRoot(applied)
      instance <- rightOf(contraction)
      assumedInstance <- LogicError.lift(Kernel.assume(instance))

      belowZero <- rules.conjElim1(assumedInstance)
      never <- rules.spec(index, notBelowZero)
      absurd <- rules.notElim(never, belowZero)
      anything <- rules.falsityElim(conclusion, absurd)
      closed <- rules.existsElim(assumed, index, anything)
      result <- rules.disch(antecedent, closed)
    } yield result
  }

  /**
   * The step of [[leastNumber]], and the only classical case split in this file.
   *
   * On whether anything below the **old** bound satisfies `P`. If something does, the induction
   * hypothesis is the answer outright and the new bound never has to be looked at. If nothing does,
   * the negated existential is worth more than it looks: it is simultaneously what forces the
   * witness to be the old bound and what proves that bound minimal.
   */
  private def oneBoundHigher(
    logic: Logic,
    excludedMiddle: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    lessThan: Term,
    predicate: FVar,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      halves <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (antecedent, conclusion) = halves
      assumed <- LogicError.lift(Kernel.assume(antecedent))

      prior <- logic
        .destImp(step.hypothesis.conclusion)
        .toRight(NotOfForm("an implication", step.hypothesis.conclusion))
      (below, _) = prior

      assumedBelow <- LogicError.lift(Kernel.assume(below))
      fromHypothesis <- rules.mp(step.hypothesis, assumedBelow)

      denied <- logic.mkNot(below)
      assumedDenial <- LogicError.lift(Kernel.assume(denied))
      fromDenial <- boundIsItselfLeast(
        logic,
        belowSuccessorCases,
        lessThan,
        predicate,
        step.variable,
        antecedent,
        below,
        conclusion,
        assumed,
        assumedDenial
      )

      middle <- rules.spec(below, excludedMiddle)
      decided <- rules.disjElim(middle, fromHypothesis, fromDenial)
      result <- rules.disch(antecedent, decided)
    } yield result
  }

  /**
   * The half of [[oneBoundHigher]] where nothing below the old bound satisfies `P`.
   *
   * The witness the new bound supplies is below `SUC n`, so by [[belowSuccessorSplits]] it is below
   * `n` or it **is** `n`. The first is refused by the very assumption this branch is under. The
   * second gives `P n`, and the same assumption, specialised at an arbitrary `k`, is the minimality
   * clause: if some `k` below `n` satisfied `P` then something below `n` would.
   */
  private def boundIsItselfLeast(
    logic: Logic,
    belowSuccessorCases: Kernel.Thm,
    lessThan: Term,
    predicate: FVar,
    bound: FVar,
    antecedent: Term,
    below: Term,
    conclusion: Term,
    assumed: Kernel.Thm,
    denial: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      wider <- logic
        .destExistsPredicate(antecedent)
        .toRight(NotOfForm("an existential quantification", antecedent))
      narrower <- logic
        .destExistsPredicate(below)
        .toRight(NotOfForm("an existential quantification", below))
      least <- logic
        .destExistsPredicate(conclusion)
        .toRight(NotOfForm("an existential quantification", conclusion))
      domain <- Type
        .destFun(Term.typeOf(wider))
        .map(_._1)
        .toRight(NotOfForm("a predicate", wider))

      taken = Term.freeVariables(antecedent) ++ Term.freeVariables(conclusion) + bound
      index = Conv.freshVariable("j", domain, taken)
      other = Conv.freshVariable("k", domain, taken + index)

      applied <- LogicError.lift(Term.app(wider, index))
      contraction <- Conv.betaRoot(applied)
      instance <- rightOf(contraction)
      assumedInstance <- LogicError.lift(Kernel.assume(instance))
      strictlyBelow <- rules.conjElim1(assumedInstance)
      holds <- rules.conjElim2(assumedInstance)

      split <- rules
        .specAll(belowSuccessorCases, List(bound, index))
        .flatMap(rules.mp(_, strictlyBelow))
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isBelow, isBound) = branches

      // Below the old bound: the assumption this branch is under says there is no such thing.
      assumedIsBelow <- LogicError.lift(Kernel.assume(isBelow))
      pairBelow <- rules.conjIntro(assumedIsBelow, holds)
      witnessed <- rules.existsIntro(narrower, index, pairBelow)
      contradicted <- rules.notElim(denial, witnessed)
      belowCase <- rules.falsityElim(conclusion, contradicted)

      // The old bound itself: `P` holds there, and nothing below it satisfies `P` for the same
      // reason the first branch was impossible.
      assumedIsBound <- LogicError.lift(Kernel.assume(isBound))
      carried <- Conv.apTerm(predicate, assumedIsBound)
      atBound <- LogicError.lift(Kernel.eqMp(carried, holds))

      otherBelow <- LogicError.lift(Term.appAll(lessThan, List(other, bound)))
      assumedOtherBelow <- LogicError.lift(Kernel.assume(otherBelow))
      holdsAtOther <- LogicError.lift(Term.app(predicate, other))
      assumedHoldsAtOther <- LogicError.lift(Kernel.assume(holdsAtOther))
      pairOther <- rules.conjIntro(assumedOtherBelow, assumedHoldsAtOther)
      witnessedOther <- rules.existsIntro(narrower, other, pairOther)
      contradictedOther <- rules.notElim(denial, witnessedOther)
      deniedAtOther <- rules.notIntro(holdsAtOther, contradictedOther)
      impliedAtOther <- rules.disch(otherBelow, deniedAtOther)
      minimal <- rules.gen(other, impliedAtOther)

      together <- rules.conjIntro(atBound, minimal)
      boundCase <- rules.existsIntro(least, bound, together)

      decided <- rules.disjElim(split, belowCase, boundCase)
      result <- rules.existsElim(assumed, index, decided)
    } yield result
  }

  /* --------------------------------------------- the greatest bounded element */

  /**
   * `|- !P. (?n. P n) /\ (?b. !k. P k ==> NUM_LE k b) ==> (?m. P m /\ (!k. P k ==> NUM_LE k m))`.
   *
   * From [[leastNumber]] and not from a second induction. "`n` is an upper bound of `P`" is itself
   * a predicate on numbers, the second hypothesis says something satisfies it, and the **least**
   * thing that does is the greatest element of `P`. That is the whole argument, and the only part
   * of it that is not immediate is that `P` holds at that least upper bound.
   *
   * It is proved by contradiction, and the case split is on the bound rather than on `P`. If the
   * least upper bound is `ZERO` and `P` fails there, then every witness of the first hypothesis is
   * at most `ZERO` and so **is** `ZERO` by [[atMostZeroIsZero]], which is the failure again. If it
   * is `SUC j` and `P` fails there, then `j` is an upper bound too: anything satisfying `P` is at
   * most `SUC j`, is therefore below `SUC j` or equal to it, and cannot be equal to it because `P`
   * fails there. And `j` is below `SUC j`, so the minimality forbids it being an upper bound.
   *
   * The asymmetry with [[leastNumber]] is the second hypothesis and it is the mathematics rather
   * than a limitation: a non-empty set of naturals always has a least element, and has a greatest
   * one only if it is bounded.
   */
  private def greatestBounded(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    least: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    reflexive: Kernel.Thm,
    belowOrEqual: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    atMostZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))

    for {
      statement <- stated(theory, notation, GreatestBounded)
      stripped <- Logic.stripForall(statement)
      predicate <- stripped._1.headOption
        .toRight(NotOfForm("a claim about a predicate", statement))
      halves <- logic
        .destImp(stripped._2)
        .toRight(NotOfForm("an implication", stripped._2))
      (hypotheses, conclusion) = halves
      parts <- logic.destConj(hypotheses).toRight(NotOfForm("a conjunction", hypotheses))
      (somewhere, boundedAbove) = parts

      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      doubleNegation <- naturals.classical.fact(Classical.DoubleNegation)
      atMostConstant <- LogicError.lift(theory.constant(NonStrictOrder, relation))
      lessThan <- LogicError.lift(theory.constant(StrictOrder, relation))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      assumedHypotheses <- LogicError.lift(Kernel.assume(hypotheses))
      assumedSomewhere <- rules.conjElim1(assumedHypotheses)
      assumedBounded <- rules.conjElim2(assumedHypotheses)

      // `NUM_LEAST` at "is an upper bound of `P`". The specialisation leaves the predicate applied
      // rather than substituted, which is what `Rules.spec` documents, so the conclusion is
      // normalised before anything is read off it.
      upperBound <- logic
        .destExistsPredicate(boundedAbove)
        .toRight(NotOfForm("an existential quantification", boundedAbove))
      instance <- rules.spec(upperBound, least)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      leastBound <- rules.mp(opened, assumedBounded)

      taken = Term.freeVariables(statement) ++ Term.freeVariables(conclusion)
      top = Conv.freshVariable("m", numbers, taken)
      found = Conv.freshVariable("n", numbers, taken + top)
      step = Conv.freshVariable("j", numbers, taken + top + found)
      other = Conv.freshVariable("k", numbers, taken + top + found + step)

      leastPredicate <- logic
        .destExistsPredicate(leastBound.conclusion)
        .toRight(NotOfForm("an existential quantification", leastBound.conclusion))
      appliedTop <- LogicError.lift(Term.app(leastPredicate, top))
      contractionTop <- Conv.betaRoot(appliedTop)
      instanceAtTop <- rightOf(contractionTop)
      assumedAtTop <- LogicError.lift(Kernel.assume(instanceAtTop))
      isBound <- rules.conjElim1(assumedAtTop)
      minimal <- rules.conjElim2(assumedAtTop)

      holdsAtTop <- LogicError.lift(Term.app(predicate, top))
      denialAtTop <- logic.mkNot(holdsAtTop)
      assumedDenial <- LogicError.lift(Kernel.assume(denialAtTop))

      split <- rules.spec(top, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = branches

      zeroCase <- noWitnessBelowZero(
        logic,
        atMostZero,
        atMostConstant,
        predicate,
        somewhere,
        isZero,
        top,
        found,
        isBound,
        assumedSomewhere,
        assumedDenial
      )

      successorCase <- predecessorIsAlsoAnUpperBound(
        logic,
        belowSuccessor,
        reflexive,
        belowOrEqual,
        belowSuccessorCases,
        atMostFromBelow,
        atMostConstant,
        lessThan,
        successor,
        predicate,
        isSuccessor,
        top,
        step,
        other,
        isBound,
        minimal,
        assumedDenial
      )

      absurd <- rules.disjElim(split, zeroCase, successorCase)
      doubled <- rules.notIntro(denialAtTop, absurd)
      atTop <- rules.spec(holdsAtTop, doubleNegation).flatMap(rules.mp(_, doubled))

      together <- rules.conjIntro(atTop, isBound)
      greatest <- logic
        .destExistsPredicate(conclusion)
        .toRight(NotOfForm("an existential quantification", conclusion))
      reached <- rules.existsIntro(greatest, top, together)

      closed <- rules.existsElim(leastBound, top, reached)
      discharged <- rules.disch(hypotheses, closed)
      general <- rules.gen(predicate, discharged)
      result <- checked(theory, notation, GreatestBounded, general)
    } yield result
  }

  /**
   * The first half of [[greatestBounded]]'s contradiction: the least upper bound is `ZERO`.
   *
   * Then every witness of the non-emptiness is at most `ZERO` and so is `ZERO` itself, which is the
   * bound, so `P` holds there after all.
   */
  private def noWitnessBelowZero(
    logic: Logic,
    atMostZero: Kernel.Thm,
    atMostConstant: Term,
    predicate: FVar,
    somewhere: Term,
    isZero: Term,
    top: FVar,
    found: FVar,
    isBound: Kernel.Thm,
    assumedSomewhere: Kernel.Thm,
    assumedDenial: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      chosen <- logic
        .destExistsPredicate(somewhere)
        .toRight(NotOfForm("an existential quantification", somewhere))
      applied <- LogicError.lift(Term.app(chosen, found))
      contraction <- Conv.betaRoot(applied)
      instance <- rightOf(contraction)
      assumedFound <- LogicError.lift(Kernel.assume(instance))

      bounded <- rules.spec(found, isBound).flatMap(rules.mp(_, assumedFound))
      from <- LogicError.lift(Term.app(atMostConstant, found))
      carried <- Conv.apTerm(from, assumedZero)
      atZero <- LogicError.lift(Kernel.eqMp(carried, bounded))
      foundIsZero <- rules.spec(found, atMostZero).flatMap(rules.mp(_, atZero))

      foundIsTop <- Conv.sym(assumedZero).flatMap(Conv.trans(foundIsZero, _))
      carriedPredicate <- Conv.apTerm(predicate, foundIsTop)
      holds <- LogicError.lift(Kernel.eqMp(carriedPredicate, assumedFound))
      absurd <- rules.notElim(assumedDenial, holds)
      result <- rules.existsElim(assumedSomewhere, found, absurd)
    } yield result
  }

  /**
   * The second half: the least upper bound is `SUC j`, and then `j` is an upper bound as well.
   *
   * Anything satisfying `P` is at most `SUC j`, hence below it or equal to it by [[BelowOrEqual]],
   * and equal is impossible because `P` fails at the bound by assumption. Below `SUC j` is below
   * `j` or equal to `j` by [[BelowSuccessorCases]], and both give `NUM_LE k j`. So `j` is an upper
   * bound below the least one, which is the contradiction.
   */
  private def predecessorIsAlsoAnUpperBound(
    logic: Logic,
    belowSuccessor: Kernel.Thm,
    reflexive: Kernel.Thm,
    belowOrEqual: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    atMostConstant: Term,
    lessThan: Term,
    successor: Term,
    predicate: FVar,
    isSuccessor: Term,
    top: FVar,
    step: FVar,
    other: FVar,
    isBound: Kernel.Thm,
    minimal: Kernel.Thm,
    assumedDenial: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      shape <- logic
        .destExistsPredicate(isSuccessor)
        .toRight(NotOfForm("an existential quantification", isSuccessor))
      applied <- LogicError.lift(Term.app(shape, step))
      contraction <- Conv.betaRoot(applied)
      isStep <- rightOf(contraction)
      assumedStep <- LogicError.lift(Kernel.assume(isStep))
      successorOfStep <- LogicError.lift(Term.app(successor, step))

      holdsAtOther <- LogicError.lift(Term.app(predicate, other))
      assumedHoldsAtOther <- LogicError.lift(Kernel.assume(holdsAtOther))
      goal <- LogicError.lift(Term.appAll(atMostConstant, List(other, step)))

      bounded <- rules.spec(other, isBound).flatMap(rules.mp(_, assumedHoldsAtOther))
      from <- LogicError.lift(Term.app(atMostConstant, other))
      carried <- Conv.apTerm(from, assumedStep)
      belowTheSuccessor <- LogicError.lift(Kernel.eqMp(carried, bounded))

      decided <- rules
        .specAll(belowOrEqual, List(other, successorOfStep))
        .flatMap(rules.mp(_, belowTheSuccessor))
      halves <- logic
        .destDisj(decided.conclusion)
        .toRight(NotOfForm("a disjunction", decided.conclusion))
      (strictlyBelow, equalToSuccessor) = halves

      // Equal to the bound: `P` fails there and holds here, which is the same number.
      assumedEqual <- LogicError.lift(Kernel.assume(equalToSuccessor))
      otherIsTop <- Conv.sym(assumedStep).flatMap(Conv.trans(assumedEqual, _))
      carriedPredicate <- Conv.apTerm(predicate, otherIsTop)
      holdsAtBound <- LogicError.lift(Kernel.eqMp(carriedPredicate, assumedHoldsAtOther))
      contradicted <- rules.notElim(assumedDenial, holdsAtBound)
      equalCase <- rules.falsityElim(goal, contradicted)

      // Below the bound: one step down, and either half of that is the bound one lower.
      assumedStrictly <- LogicError.lift(Kernel.assume(strictlyBelow))
      peeled <- rules
        .specAll(belowSuccessorCases, List(step, other))
        .flatMap(rules.mp(_, assumedStrictly))
      peeledHalves <- logic
        .destDisj(peeled.conclusion)
        .toRight(NotOfForm("a disjunction", peeled.conclusion))
      (belowStep, equalToStep) = peeledHalves

      assumedBelowStep <- LogicError.lift(Kernel.assume(belowStep))
      fromStrict <- rules
        .specAll(atMostFromBelow, List(other, step))
        .flatMap(rules.mp(_, assumedBelowStep))

      assumedEqualToStep <- LogicError.lift(Kernel.assume(equalToStep))
      reflexiveAtStep <- rules.spec(step, reflexive)
      carriedOrder <- Conv.apTerm(atMostConstant, assumedEqualToStep)
      atStep <- Conv.apThm(carriedOrder, step)
      fromEqual <- Conv
        .sym(atStep)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, reflexiveAtStep)))

      strictCase <- rules.disjElim(peeled, fromStrict, fromEqual)
      reached <- rules.disjElim(decided, strictCase, equalCase)
      implied <- rules.disch(holdsAtOther, reached)
      upperAtStep <- rules.gen(other, implied)

      // And it is below the least upper bound, which is what forbids it being one.
      atItsSuccessor <- rules.spec(step, belowSuccessor)
      strictlyFrom <- LogicError.lift(Term.app(lessThan, step))
      carriedStrict <- Conv.apTerm(strictlyFrom, assumedStep)
      stepBelowTop <- Conv
        .sym(carriedStrict)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atItsSuccessor)))
      denied <- rules.spec(step, minimal).flatMap(rules.mp(_, stepBelowTop))
      absurd <- rules.notElim(denied, upperAtStep)
      result <- rules.existsElim(assumedSuccessor, step, absurd)
    } yield result
  }

  /**
   * `|- !m n p. NUM_LE m n /\ NUM_LE n p ==> NUM_LE m p`.
   *
   * The witness is the sum of the two given, and the arithmetic is one use of associativity:
   * `m + (d + e) = (m + d) + e = n + e = p`. Both existentials are opened before the witness is
   * built and closed after, which is the order the side condition on eliminating one forces: the
   * variable it names may not appear in what is proved, and `NUM_LE m p` mentions neither.
   */
  /**
   * `|- !m n p. NUM_LT m n /\ NUM_LT n p ==> NUM_LT m p`, from the non-strict transitivity.
   *
   * `NUM_LT a b` IS `NUM_LE (SUC a) b`, so unfolding the three occurrences turns the goal into
   * `SUC m <= n` and `SUC n <= p` therefore `SUC m <= p`, and the bridge between them is
   * `n <= SUC n`. Two applications of [[Transitive]] and no induction: the strict order is not
   * a second order here, it is the non-strict one shifted by a successor, and every fact about
   * it that does not mention the shift should come out this way.
   *
   * The two successor terms are read OFF the unfolded hypotheses rather than built here. Built
   * here they would be correct and would still be a second copy of something the theorem
   * already contains, and a second copy is what drifts.
   */
  private def strictTransitivity(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    strictDefinition: Kernel.Thm,
    transitive: Kernel.Thm,
    atMostSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def argumentsOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      theorem.conclusion match {
        case App(App(_, left), right) => Right((left, right))
        case other                    => Left(NotOfForm("an order statement", other))
      }

    def instantiate(theorem: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
      arguments.foldLeft[Either[LogicError, Kernel.Thm]](Right(theorem)) { (soFar, argument) =>
        soFar.flatMap(rules.spec(argument, _))
      }

    for {
      statement <- stated(theory, notation, StrictTransitive)
      stripped <- Logic.stripForall(statement)
      (variables, body) = stripped
      first <- variables.lift(0).toRight(NotOfForm("three numbers", body))
      second <- variables.lift(1).toRight(NotOfForm("three numbers", body))
      third <- variables.lift(2).toRight(NotOfForm("three numbers", body))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premise, conclusion) = parts
      assumed <- LogicError.lift(Kernel.assume(premise))

      unfold <- Rewrite.Rule.of(logic, strictDefinition)
      lower <- rules.conjElim1(assumed)
      upper <- rules.conjElim2(assumed)
      lowerLe <- Rewrite
        .rewrite(Vector(unfold), lower.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, lower)))
      upperLe <- Rewrite
        .rewrite(Vector(unfold), upper.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, upper)))

      lowerSides <- argumentsOf(lowerLe)   // (SUC m, n)
      upperSides <- argumentsOf(upperLe)   // (SUC n, p)
      bridge <- rules.spec(second, atMostSuccessor)   // n <= SUC n

      toSuccessor <- rules
        .conjIntro(lowerLe, bridge)
        .flatMap(pair =>
          instantiate(transitive, List(lowerSides._1, second, upperSides._1))
            .flatMap(rules.mp(_, pair)))
      reaching <- rules
        .conjIntro(toSuccessor, upperLe)
        .flatMap(pair =>
          instantiate(transitive, List(lowerSides._1, upperSides._1, third))
            .flatMap(rules.mp(_, pair)))

      asStrict <- Rewrite
        .rewrite(Vector(unfold), conclusion)
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, reaching)))
      discharged <- rules.disch(premise, asStrict)
      general <- rules.genAll(discharged, List(first, second, third))
      result <- checked(theory, notation, StrictTransitive, general)
    } yield result
  }

  private def transitivity(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm,
    arithmetic: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val p = Term.variable("p", numbers)
    val d = Term.variable("d", numbers)
    val e = Term.variable("e", numbers)

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      belowN <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      belowP <- Parser.proposition(theory, notation, "NUM_LE (n:num) (p:num)")
      both <- logic.mkConj(belowN, belowP)
      assumed <- LogicError.lift(Kernel.assume(both))
      first <- rules.conjElim1(assumed)
      second <- rules.conjElim2(assumed)

      firstGap <- gap(logic, definition, m, n, first)
      secondGap <- gap(logic, definition, n, p, second)

      reachesN <- LogicError.lift(
        Term.appAll(plus, List(m, d)).flatMap(Term.eq(_, n)).flatMap(Kernel.assume)
      )
      reachesP <- LogicError.lift(
        Term.appAll(plus, List(n, e)).flatMap(Term.eq(_, p)).flatMap(Kernel.assume)
      )

      grouped <- rules.specAll(arithmetic(AddAssociative), List(m, d, e))
      ungrouped <- Conv.sym(grouped)
      carried <- Conv.apTerm(plus, reachesN).flatMap(Conv.apThm(_, e))
      whole <- Conv.trans(ungrouped, carried).flatMap(Conv.trans(_, reachesP))

      witness <- LogicError.lift(Term.appAll(plus, List(d, e)))
      reaches <- atMost(logic, definition, m, p, witness, whole)

      withoutE <- rules.existsElim(secondGap, e, reaches)
      withoutD <- rules.existsElim(firstGap, d, withoutE)
      result <- rules
        .disch(both, withoutD)
        .flatMap(rules.genAll(_, List(m, n, p)))
        .flatMap(checked(theory, notation, Transitive, _))
    } yield result
  }

  /**
   * `|- !n m. NUM_ADD m n = m ==> n = ZERO`, by induction on `m`.
   *
   * Cancellation, and the goal is an implication rather than an equation, so the rewriting driver
   * cannot close either half: both are written out. The base is `ZERO + n = ZERO` read against
   * `ZERO + n = n`, and the step takes `SUC k + n = SUC k` to `SUC (k + n) = SUC k` and then to
   * `k + n = k` by the injectivity of the successor, which is where the hypothesis applies.
   *
   * **The variables are taken off the goal rather than named here**, and that is not a shortcut:
   * the driver opens the quantifier itself, so the variable the step is about is fresh and a caller
   * cannot name it. `n` is the left side of what is to be proved in both halves, and `k` is the
   * argument of the successor the premise equates to.
   */
  private def cancellation(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules

    def halves(goal: Term): Either[LogicError, (Term, Term, Term)] =
      for {
        parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
        (premise, conclusion) = parts
        sides <- Term.destEq(conclusion).toRight(NotOfForm("an equation", conclusion))
      } yield (premise, conclusion, sides._1)

    for {
      statement <- stated(theory, notation, AddCancels)
      injective <- naturals.fact(Natural.SuccessorInjective)

      result <- driver.proveBy(
        statement,
        goal =>
          for {
            parts <- halves(goal)
            (premise, _, number) = parts
            assumed <- LogicError.lift(Kernel.assume(premise))
            unit <- rules.spec(number, arithmetic(ZeroPlus))
            reversed <- Conv.sym(unit)
            reached <- Conv.trans(reversed, assumed)
            discharged <- rules.disch(premise, reached)
          } yield discharged,
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          for {
            parts <- halves(goal)
            (premise, _, number) = parts
            sides <- Term.destEq(premise).toRight(NotOfForm("an equation", premise))
            step <- sides._2 match {
              case App(_, argument) => Right(argument)
              case other => Left(NotOfForm("a successor", other))
            }

            assumed <- LogicError.lift(Kernel.assume(premise))
            moved <- rules.specAll(arithmetic(SuccessorPlus), List(step, number))
            reversed <- Conv.sym(moved)
            equalSuccessors <- Conv.trans(reversed, assumed)

            // `k + n`, taken off the recurrence rather than rebuilt, so that what injectivity is
            // pointed at is the term that is actually under the successor.
            stepped <- rightOf(moved)
            inside <- stepped match {
              case App(_, argument) => Right(argument)
              case other => Left(NotOfForm("a successor", other))
            }
            smaller <- rules
              .specAll(injective, List(inside, step))
              .flatMap(rules.mp(_, equalSuccessors))
            reached <- rules.mp(hypothesis, smaller)
            discharged <- rules.disch(premise, reached)
          } yield discharged
      )
    } yield result
  }

  /**
   * `|- !x y a. NUM_ADD a x = NUM_ADD a y ==> x = y`, by induction on `a`.
   *
   * The induction is on the summand being cancelled and not on either of the two being compared,
   * which is what makes it three lines a side: at `ZERO` the recurrence [[ZeroPlus]] removes the
   * summand outright, and at `SUC a` the recurrence [[SuccessorPlus]] lifts both sides to
   * successors, whose injectivity takes one step off and leaves the hypothesis to apply.
   *
   * It is not derived from [[AddCancels]] and could not be: that one has `ZERO` on the right of its
   * conclusion, and the step from it to this is exactly the induction below.
   */
  private def leftCancellation(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    /** The premise, and the two numbers the conclusion compares. */
    def parts(goal: Term): Either[LogicError, (Term, Term, Term)] =
      for {
        implication <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
        (premise, conclusion) = implication
        sides <- Term.destEq(conclusion).toRight(NotOfForm("an equation", conclusion))
      } yield (premise, sides._1, sides._2)

    for {
      statement <- stated(theory, notation, AddCancelsLeft)
      injective <- naturals.fact(Natural.SuccessorInjective)
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      result <- driver.proveBy(
        statement,
        goal =>
          for {
            split <- parts(goal)
            (premise, left, right) = split
            assumed <- LogicError.lift(Kernel.assume(premise))
            atLeft <- rules.spec(left, arithmetic(ZeroPlus))
            atRight <- rules.spec(right, arithmetic(ZeroPlus))
            reached <- Conv
              .sym(atLeft)
              .flatMap(Conv.trans(_, assumed))
              .flatMap(Conv.trans(_, atRight))
            discharged <- rules.disch(premise, reached)
          } yield discharged,
        opened =>
          for {
            split <- parts(opened.goal)
            (premise, left, right) = split
            assumed <- LogicError.lift(Kernel.assume(premise))

            atLeft <- rules.specAll(arithmetic(SuccessorPlus), List(opened.variable, left))
            atRight <- rules.specAll(arithmetic(SuccessorPlus), List(opened.variable, right))
            equalSuccessors <- Conv
              .sym(atLeft)
              .flatMap(Conv.trans(_, assumed))
              .flatMap(Conv.trans(_, atRight))

            insideLeft <- LogicError.lift(Term.appAll(plus, List(opened.variable, left)))
            insideRight <- LogicError.lift(Term.appAll(plus, List(opened.variable, right)))
            smaller <- rules
              .specAll(injective, List(insideLeft, insideRight))
              .flatMap(rules.mp(_, equalSuccessors))

            reached <- rules.mp(opened.hypothesis, smaller)
            discharged <- rules.disch(premise, reached)
          } yield discharged
      )
    } yield result
  }

  /**
   * `|- !m n. NUM_ADD m n = ZERO ==> m = ZERO`, by induction on `n`.
   *
   * An induction whose step never uses its hypothesis: `m + SUC k = SUC (m + k)` is a successor,
   * a successor is never zero, and there is nothing to prove about a case that cannot arise. The
   * base is the first recurrence, where `m + ZERO = ZERO` says `m = ZERO` directly.
   */
  private def sumVanishes(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm],
    naturals: Natural
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules

    for {
      statement <- stated(theory, notation, SumIsZero)
      notZero <- naturals.fact(Natural.SuccessorNotZero)

      result <- driver.proveBy(
        statement,
        goal =>
          for {
            parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
            (premise, _) = parts
            sides <- Term.destEq(premise).toRight(NotOfForm("an equation", premise))
            number <- sides._1 match {
              case App(App(_, left), _) => Right(left)
              case other => Left(NotOfForm("a sum", other))
            }
            assumed <- LogicError.lift(Kernel.assume(premise))
            unit <- rules.spec(number, arithmetic(AddAtZero))
            reversed <- Conv.sym(unit)
            reached <- Conv.trans(reversed, assumed)
            discharged <- rules.disch(premise, reached)
          } yield discharged,
        opened =>
          val goal = opened.goal
          for {
            parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
            (premise, conclusion) = parts
            sides <- Term.destEq(premise).toRight(NotOfForm("an equation", premise))
            pieces <- sides._1 match {
              case App(App(_, left), App(_, step)) => Right((left, step))
              case other => Left(NotOfForm("a sum with a successor on its right", other))
            }
            (number, step) = pieces

            assumed <- LogicError.lift(Kernel.assume(premise))
            moved <- rules.specAll(arithmetic(AddAtSuccessor), List(number, step))
            reversed <- Conv.sym(moved)
            successorIsZero <- Conv.trans(reversed, assumed)

            stepped <- rightOf(moved)
            inside <- stepped match {
              case App(_, argument) => Right(argument)
              case other => Left(NotOfForm("a successor", other))
            }
            never <- rules.spec(inside, notZero)
            absurd <- rules.notElim(never, successorIsZero)
            anything <- rules.falsityElim(conclusion, absurd)
            discharged <- rules.disch(premise, anything)
          } yield discharged
      )
    } yield result
  }

  /**
   * `|- !m n. NUM_LE m n /\ NUM_LE n m ==> m = n`.
   *
   * Both witnesses are opened, and together they give `m + (d + e) = m`. Cancellation turns that
   * into `d + e = ZERO`, the second lemma turns that into `d = ZERO`, and then `n`, which is
   * `m + d`, is `m + ZERO`, which is `m`.
   */
  private def antisymmetry(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm,
    arithmetic: Map[String, Kernel.Thm],
    lemmas: (Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)
    val e = Term.variable("e", numbers)
    val (cancels, sumIsZero) = lemmas

    for {
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      belowN <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      belowM <- Parser.proposition(theory, notation, "NUM_LE (n:num) (m:num)")
      both <- logic.mkConj(belowN, belowM)
      assumed <- LogicError.lift(Kernel.assume(both))
      first <- rules.conjElim1(assumed)
      second <- rules.conjElim2(assumed)

      firstGap <- gap(logic, definition, m, n, first)
      secondGap <- gap(logic, definition, n, m, second)

      reachesN <- LogicError.lift(
        Term.appAll(plus, List(m, d)).flatMap(Term.eq(_, n)).flatMap(Kernel.assume)
      )
      reachesM <- LogicError.lift(
        Term.appAll(plus, List(n, e)).flatMap(Term.eq(_, m)).flatMap(Kernel.assume)
      )

      // `m + (d + e) = (m + d) + e = n + e = m`
      grouped <- rules.specAll(arithmetic(AddAssociative), List(m, d, e))
      ungrouped <- Conv.sym(grouped)
      carried <- Conv.apTerm(plus, reachesN).flatMap(Conv.apThm(_, e))
      whole <- Conv.trans(ungrouped, carried).flatMap(Conv.trans(_, reachesM))

      witness <- LogicError.lift(Term.appAll(plus, List(d, e)))
      vanishes <- rules.specAll(cancels, List(witness, m)).flatMap(rules.mp(_, whole))
      firstVanishes <- rules.specAll(sumIsZero, List(d, e)).flatMap(rules.mp(_, vanishes))

      // `n = m + d = m + ZERO = m`, and then the other way round.
      from <- LogicError.lift(Term.app(plus, m))
      atWitness <- Conv.apTerm(from, firstVanishes)
      unit <- rules.spec(m, arithmetic(AddAtZero))
      reachesItself <- Conv.trans(atWitness, unit)
      fromN <- Conv.sym(reachesN)
      equal <- Conv.trans(fromN, reachesItself).flatMap(Conv.sym)

      withoutE <- rules.existsElim(secondGap, e, equal)
      withoutD <- rules.existsElim(firstGap, d, withoutE)
      result <- rules
        .disch(both, withoutD)
        .flatMap(rules.genAll(_, List(m, n)))
        .flatMap(checked(theory, notation, AntiSymmetric, _))
    } yield result
  }

  /**
   * `|- NUM_LE left right`, from a proof that `left + witness = right`.
   *
   * The definition unfolded, the existential introduced at the witness, and the definition folded
   * back. Written once because every fact about the order below is this and one equation.
   */
  private def atMost(
    logic: Logic,
    definition: Kernel.Thm,
    left: Term,
    right: Term,
    witness: Term,
    evidence: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv.unfold(definition, List(left, right))
      body <- rightOf(unfolded)
      predicate <- logic.destExistsPredicate(body).toRight(NotOfForm("an existential", body))
      witnessed <- logic.rules.existsIntro(predicate, witness, evidence)
      result <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))
    } yield result

  /** `G |- ?d. left + d = right`, from `G |- NUM_LE left right`: the same step the other way. */
  private def gap(
    logic: Logic,
    definition: Kernel.Thm,
    left: Term,
    right: Term,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv.unfold(definition, List(left, right))
      result <- LogicError.lift(Kernel.eqMp(unfolded, theorem))
    } yield result

  /* -------------------------------------------------------------- embedding */

  /* ------------------------------------------------------------ subtraction */

  /**
   * The predecessor, the truncated difference, and the nine facts a consumer of one needs.
   *
   * Two definitions rather than one, and the first is not a convenience: `NUM_SUB` recurses on its
   * second argument like the other two operations, so its step has to say what one more subtracted
   * unit does to a number, and that **is** the predecessor. Defining the difference directly would
   * mean writing the same case split inside it and then having no name for it.
   *
   * Six of the nine close by rewriting and three are written out, and which is which is the useful
   * part:
   *
   *  - [[ZeroMinus]], [[SubSuccessors]], [[SubSelf]], [[SumMinus]] and [[Truncates]] are
   *    inductions the rewriter settles. The rule sets are **not** the union of everything proved so
   *    far and that is deliberate: [[SubAtSuccessor]] is left out of the last three, because it
   *    unfolds `NUM_SUB m (SUC n)` at the node where [[SubSuccessors]] or the induction hypothesis
   *    was the rule that had to fire, and a rewriter that has taken the redex apart cannot put it
   *    back. Measured: with it in the set, [[SubSelf]]'s step stops at
   *    `PRE (NUM_SUB (SUC k) k)` against `ZERO`.
   *  - [[SubIsZero]] and [[MinusThenPlus]] carry a hypothesis, so they are not equations and the
   *    driver cannot take them. Both are the same three lines: open `NUM_LE`, rewrite the witness
   *    equation into the goal, and close with one of the two inductions above.
   *  - [[PredecessorBelow]] is a case split rather than an induction, and [[SubBelow]] is an
   *    induction whose step is a transitivity. Neither is an equation either.
   */
  private def subtraction(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    addition: Map[String, Kernel.Thm],
    orderDefinitions: Map[String, Kernel.Thm],
    orderFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, (Theory, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)

    for {
      // `PRE` takes the recursion's step function to its *index*, which is the number one below the
      // successor it is being asked about. That is the whole definition.
      predecessor <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Predecessor,
        numbers,
        "ZERO",
        "\\v:num. \\i:num. i",
        None
      )
      (withPredecessor, predecessorDefinition, preZero, preSuccessor) = predecessor

      preAtZero <- checked(withPredecessor, notation, PreAtZero, preZero)
      preAtSuccessor <- checked(withPredecessor, notation, PreAtSuccessor, preSuccessor)

      defined <- Recursion.define(
        logic,
        naturals,
        withPredecessor,
        notation,
        recursion,
        Subtraction,
        numbers,
        "m:num",
        "\\v:num. \\i:num. PRE v",
        Some(m)
      )
      (theory, subtractionDefinition, subZero, subSuccessor) = defined

      subAtZero <- checked(theory, notation, SubAtZero, subZero)
      subAtSuccessor <- checked(theory, notation, SubAtSuccessor, subSuccessor)

      recurrences = Vector(subAtZero, subAtSuccessor, preAtZero, preAtSuccessor)

      zeroMinus <- byInduction(driver, theory, notation, ZeroMinus, recurrences)

      // The one place the hypothesis has to be tried before the recurrences. Both sides of the step
      // are `NUM_SUB` at a successor, so `NUM_SUB_SUC` matches at the very node the hypothesis was
      // for, and the two normal forms come out as `PRE (PRE (NUM_SUB (SUC m) k))` against
      // `PRE (NUM_SUB m k)`. `Induct.settle` puts the hypothesis first for the same reason and says
      // so at more length.
      subSuccessors <- byInduction(
        driver,
        theory,
        notation,
        SubSuccessors,
        recurrences,
        hypothesisFirst = true
      )

      subSelf <- byInduction(driver, theory, notation, SubSelf, Vector(subAtZero, subSuccessors))

      sumMinus <- byInduction(
        driver,
        theory,
        notation,
        SumMinus,
        Vector(addition(AddAtZero), addition(AddAtSuccessor), subAtZero, subSuccessors)
      )

      subTwice <- byInduction(
        driver,
        theory,
        notation,
        SubTwice,
        Vector(addition(AddAtZero), addition(AddAtSuccessor), subAtZero, subAtSuccessor)
      )

      truncates <- byInduction(
        driver,
        theory,
        notation,
        Truncates,
        Vector(
          addition(AddAtZero),
          addition(AddAtSuccessor),
          subAtSuccessor,
          preAtZero,
          subSelf
        )
      )

      subIsZero <- vanishes(logic, theory, notation, orderDefinitions, truncates)
      predecessorBelow <- belowItsSuccessor(
        logic,
        theory,
        notation,
        naturals,
        (preAtZero, preAtSuccessor),
        orderFacts
      )
      subBelow <- differenceBelow(
        driver,
        theory,
        notation,
        (subAtZero, subAtSuccessor),
        predecessorBelow,
        orderFacts
      )
      minusThenPlus <- restores(logic, theory, notation, orderDefinitions, addition, sumMinus)
      stepMinus <- successorMinus(
        logic, theory, notation, minusThenPlus, addition(SuccessorPlus), sumMinus)
      atMostDouble <- atMostDoubleMinus(
        logic, theory, notation, orderDefinitions(NonStrictOrder), addition, sumMinus,
        orderFacts(AtMostSum))
      stepMinusSelf <- successorMinusSelf(
        logic, theory, notation, stepMinus, subSelf, orderFacts(Reflexive))
    } yield (
      theory,
      Map(Predecessor -> predecessorDefinition, Subtraction -> subtractionDefinition),
      Map(
        PreAtZero -> preAtZero,
        PreAtSuccessor -> preAtSuccessor,
        SubAtZero -> subAtZero,
        SubAtSuccessor -> subAtSuccessor,
        ZeroMinus -> zeroMinus,
        SubSuccessors -> subSuccessors,
        SubSelf -> subSelf,
        SumMinus -> sumMinus,
        SubTwice -> subTwice,
        Truncates -> truncates,
        SubIsZero -> subIsZero,
        PredecessorBelow -> predecessorBelow,
        SubBelow -> subBelow,
        MinusThenPlus -> minusThenPlus,
        SuccessorMinus -> stepMinus,
        SuccessorMinusSelf -> stepMinusSelf,
        AtMostDoubleMinus -> atMostDouble
      )
    )
  }

  /**
   * `|- !m n. NUM_LE m n ==> NUM_SUB m n = ZERO`, from [[Truncates]] and the witness.
   *
   * `NUM_LE m n` **is** `?d. NUM_ADD m d = n`, so the bound is exactly the permission to write `n`
   * as a sum starting at `m`, and [[Truncates]] is the same claim about that sum. Nothing here is
   * an induction: the induction was done on the sum, where there was something to recurse on.
   */
  private def vanishes(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    orderDefinitions: Map[String, Kernel.Thm],
    truncates: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    for {
      definition <- orderDefinitions.get(NonStrictOrder).toRight(MissingDefinition(NonStrictOrder))
      minus <- LogicError.lift(
        theory.constant(Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      assumed <- LogicError.lift(Kernel.assume(below))
      opened <- gap(logic, definition, m, n, assumed)

      reaching <- LogicError.lift(Term.appAll(plus, List(m, d)).flatMap(Term.eq(_, n)))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      // `m - n = m - (m + d) = ZERO`
      fromM <- LogicError.lift(Term.app(minus, m))
      rewritten <- Conv.sym(reaches).flatMap(Conv.apTerm(fromM, _))
      atSum <- rules.specAll(truncates, List(m, d))
      whole <- Conv.trans(rewritten, atSum)

      withoutWitness <- rules.existsElim(opened, d, whole)
      result <- rules
        .disch(below, withoutWitness)
        .flatMap(rules.genAll(_, List(m, n)))
        .flatMap(checked(theory, notation, SubIsZero, _))
    } yield result
  }

  /**
   * `|- !n. NUM_LE (PRE n) n`, by the case split on a number and not by an induction.
   *
   * There is nothing to induct on: the claim at `SUC k` says nothing about the claim at `k`. What
   * decides it is which of the two shapes `n` has, and the two answers are already theorems —
   * `ZERO` is below everything, and `k` is below `SUC k`.
   *
   * It is also where `PRE ZERO = ZERO` earns the choice made for it. A predecessor that refused at
   * zero would make this statement unwritable rather than false, and every consumer of
   * [[SubBelow]] would carry a side condition it cannot discharge.
   */
  private def belowItsSuccessor(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    recurrences: (Kernel.Thm, Kernel.Thm),
    orderFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val (preAtZero, preAtSuccessor) = recurrences

    for {
      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      split <- rules.spec(n, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = branches

      relation <- LogicError.lift(
        theory.constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      predecessor <- LogicError.lift(theory.constant(Predecessor, Type.fun(numbers, numbers)))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      // `n = ZERO`: the predecessor is `ZERO` as well, and `ZERO` is below everything.
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      predecessorIsZero <- Conv.apTerm(predecessor, assumedZero).flatMap(Conv.trans(_, preAtZero))
      leastAtN <- rules.spec(n, orderFacts(ZeroIsLeast))
      sameClaim <- Conv.apTerm(relation, predecessorIsZero).flatMap(Conv.apThm(_, n))
      zeroBranch <- Conv
        .sym(sameClaim)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, leastAtN)))

      // `n = SUC k`: the predecessor is `k`, and `k <= SUC k` is already a fact.
      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      step = Conv.freshVariable("k", numbers, Term.freeVariables(isSuccessor) + n)
      successorOfStep <- LogicError.lift(Term.app(successor, step))
      isStep <- LogicError.lift(Term.eq(n, successorOfStep))
      assumedStep <- LogicError.lift(Kernel.assume(isStep))
      atStep <- rules.spec(step, preAtSuccessor)
      predecessorIsStep <- Conv.apTerm(predecessor, assumedStep).flatMap(Conv.trans(_, atStep))
      belowSuccessor <- rules.spec(step, orderFacts(AtMostSuccessor))
      onTheLeft <- Conv.apTerm(relation, predecessorIsStep).flatMap(Conv.apThm(_, n))
      fromStep <- LogicError.lift(Term.app(relation, step))
      onTheRight <- Conv.apTerm(fromStep, assumedStep)
      sameClaimAtStep <- Conv.trans(onTheLeft, onTheRight)
      reached <- Conv
        .sym(sameClaimAtStep)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, belowSuccessor)))
      successorBranch <- rules.existsElim(assumedSuccessor, step, reached)

      decided <- rules.disjElim(split, zeroBranch, successorBranch)
      result <- rules
        .gen(n, decided)
        .flatMap(checked(theory, notation, PredecessorBelow, _))
    } yield result
  }

  /**
   * `|- !m n. NUM_LE (NUM_SUB m n) m`, by induction on what is taken away.
   *
   * The base is the first recurrence and reflexivity. The step is the second recurrence and one
   * transitivity: `m - SUC k` is `PRE (m - k)`, which is below `m - k` by [[PredecessorBelow]],
   * which is below `m` by the hypothesis.
   *
   * `Induct.afterRewriting` rather than a hand-built conversion, because the goal is a bound and
   * not an equation: the rewriting brings the goal to the shape the two facts are about and carries
   * the result back, and a rule set that had not finished is reported as that rather than as a
   * false bound.
   */
  private def differenceBelow(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    recurrences: (Kernel.Thm, Kernel.Thm),
    predecessorBelow: Kernel.Thm,
    orderFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val (subAtZero, subAtSuccessor) = recurrences

    for {
      statement <- stated(theory, notation, SubBelow)
      predecessor <- LogicError.lift(theory.constant(Predecessor, Type.fun(numbers, numbers)))
      atZero <- Rewrite.Rule.of(logic, subAtZero)
      atSuccessor <- Rewrite.Rule.of(logic, subAtSuccessor)

      result <- driver.proveBy(
        statement,
        goal =>
          Induct.afterRewriting(Vector(atZero), goal) { rewritten =>
            for {
              subject <- rewritten match {
                case App(App(_, left), _) => Right(left)
                case other => Left(NotOfForm("a bound on a number", other))
              }
              reflexive <- rules.spec(subject, orderFacts(Reflexive))
            } yield reflexive
          },
        opened =>
          for {
            sides <- opened.hypothesis.conclusion match {
              case App(App(_, left), right) => Right((left, right))
              case other => Left(NotOfForm("a bound on a number", other))
            }
            (difference, subject) = sides
            reached <- Induct.afterRewriting(Vector(atSuccessor), opened.goal) { _ =>
              for {
                smaller <- LogicError.lift(Term.app(predecessor, difference))
                dropped <- rules.spec(difference, predecessorBelow)
                pair <- rules.conjIntro(dropped, opened.hypothesis)
                chained <- rules
                  .specAll(orderFacts(Transitive), List(smaller, difference, subject))
                  .flatMap(rules.mp(_, pair))
              } yield chained
            }
          } yield reached
      )
    } yield result
  }

  /**
   * `|- !n. NUM_SUB (SUC n) n = SUC ZERO`, which is [[SuccessorMinus]] with its bound spent here.
   *
   * Three lines, and the only reason it is a lemma of its own is that a conditional equation is not
   * a rewrite rule. `Rewrite.Rule.of` refuses an implication, so a caller rewriting a difference
   * inside a sum cannot reach the general fact at all; this is the instance that fires.
   */
  private def successorMinusSelf(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    successorMinus: Kernel.Thm,
    subSelf: Kernel.Thm,
    reflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      atMost <- rules.spec(n, reflexive)
      stepped <- rules.specAll(successorMinus, List(n, n)).flatMap(rules.mp(_, atMost))
      vanishes <- rules.spec(n, subSelf).flatMap(Conv.apTerm(successor, _))
      result <- Conv
        .trans(stepped, vanishes)
        .flatMap(rules.gen(n, _))
        .flatMap(checked(theory, notation, SuccessorMinusSelf, _))
    } yield result
  }

  /**
   * `|- !m n. NUM_LE n m ==> NUM_SUB (SUC m) n = SUC (NUM_SUB m n)`, from the two that exist.
   *
   * No induction: [[MinusThenPlus]] restores what the difference took away, a successor is put on
   * both sides of that equation by congruence, [[SuccessorPlus]] moves it inside the sum, and
   * [[SumMinus]] takes the summand off again with **no** hypothesis, since by then the sum is one
   * nothing was truncated out of. The bound is spent once, at the first step, and nowhere after.
   */
  private def successorMinus(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    minusThenPlus: Kernel.Thm,
    successorPlus: Kernel.Thm,
    sumMinus: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      minus <- LogicError.lift(
        theory.constant(Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (n:num) (m:num)")
      assumed <- LogicError.lift(Kernel.assume(below))

      restored <- rules.specAll(minusThenPlus, List(m, n)).flatMap(rules.mp(_, assumed))
      difference <- Term.destEq(restored.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", restored.conclusion))
      gap <- difference match {
        case App(App(_, left), _) => Right(left)
        case other                => Left(NotOfForm("a sum", other))
      }

      stepped <- Conv.apTerm(successor, restored)
      pushed <- rules.specAll(successorPlus, List(gap, n))
      joined <- Conv.trans(pushed, stepped)

      stepGap <- LogicError.lift(Term.app(successor, gap))
      cancelled <- rules.specAll(sumMinus, List(stepGap, n))
      carried <- Conv.sym(joined).flatMap(Conv.apTerm(minus, _)).flatMap(Conv.apThm(_, n))

      result <- Conv
        .trans(carried, cancelled)
        .flatMap(rules.disch(below, _))
        .flatMap(rules.genAll(_, List(m, n)))
        .flatMap(checked(theory, notation, SuccessorMinus, _))
    } yield result
  }

  /**
   * `|- !m n. NUM_LE n m ==> NUM_ADD (NUM_SUB m n) n = m`, the converse of [[SumMinus]].
   *
   * The witness of `n <= m` is the answer: `n + d = m`, so `d + n = m` by commutativity, so
   * `m - n = (d + n) - n = d` by [[SumMinus]], and `(m - n) + n` is `d + n`, which is `m`.
   *
   * The commutation is there because [[SumMinus]] is stated with what is taken away on the right of
   * the sum and `NUM_LE` puts its witness on the right of the other one. Stating the two to agree
   * would save this step and cost it at every other call site, since `m + d = n` is the form the
   * order unfolds to everywhere else in the file.
   */
  private def restores(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    orderDefinitions: Map[String, Kernel.Thm],
    addition: Map[String, Kernel.Thm],
    sumMinus: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    for {
      definition <- orderDefinitions.get(NonStrictOrder).toRight(MissingDefinition(NonStrictOrder))
      plus <- LogicError.lift(
        theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      minus <- LogicError.lift(
        theory.constant(Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (n:num) (m:num)")
      assumed <- LogicError.lift(Kernel.assume(below))
      opened <- gap(logic, definition, n, m, assumed)

      reaching <- LogicError.lift(Term.appAll(plus, List(n, d)).flatMap(Term.eq(_, m)))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      swapped <- rules.specAll(addition(AddCommutative), List(n, d))
      sorted <- Conv.sym(swapped).flatMap(Conv.trans(_, reaches))

      cancelled <- rules.specAll(sumMinus, List(d, n))
      carried <- Conv.sym(sorted).flatMap(Conv.apTerm(minus, _)).flatMap(Conv.apThm(_, n))
      difference <- Conv.trans(carried, cancelled)

      restored <- Conv.apTerm(plus, difference).flatMap(Conv.apThm(_, n))
      whole <- Conv.trans(restored, sorted)

      withoutWitness <- rules.existsElim(opened, d, whole)
      result <- rules
        .disch(below, withoutWitness)
        .flatMap(rules.genAll(_, List(m, n)))
        .flatMap(checked(theory, notation, MinusThenPlus, _))
    } yield result
  }

  /* ------------------------------------------------------------ partial sums */

  /**
   * [[PartialSum]], its two recurrences and its bounded congruence.
   *
   * Last of the stages and it needs three of the earlier ones: `NUM_ADD` for the step of the
   * recursion, `NUM_LT` for the bound of the congruence, and the two order facts that lift an index
   * from below a number to below its successor.
   *
   * The congruence is the only part that is not the recursion, and it is [[congruenceOnARange]],
   * which is `Series`'s proof of the same lemma at the reals with one difference: there the step
   * closes an equation between REALS and goes to the linear reader, and here the equation is
   * between naturals, where no decision procedure applies. It closes by rewriting instead, with the
   * induction hypothesis and the agreement at the top index as the two rules, and demands that the
   * two sides reach the same term. That demand is the point rather than a formality: `Rewrite`
   * hands back the theorem it had when the step limit ran out, so without it an exhausted rewrite
   * and a false identity are the same object.
   */
  /**
   * `NUM_CHOOSE`, and the three facts that are Pascal's triangle.
   *
   * The recursion's value is a **function**, which is what the rule needs and what nothing else in
   * this file does. What that costs is here rather than in the caller: the two equations
   * `Recursion.define` hands back are between functions, so each of the three published facts is
   * one of them applied to a column and then opened at its `COND`.
   *
   * Opening the `COND` is the whole of the work and it is two lines each: at `ZERO` the condition
   * holds by reflexivity, and at `SUC k` it fails by `Natural.NUM_SUC_NOT_ZERO`. `Classical`'s
   * `COND_TRUE` and `COND_FALSE` are what turn that into the branch, and they cost the choice
   * axiom the naturals already pay for, so this stage adds nothing to what a development believes.
   */
  private def binomials(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    subtractionFacts: Map[String, Kernel.Thm],
    orderDefinitions: Map[String, Kernel.Thm],
    addition: Map[String, Kernel.Thm],
    induction: Kernel.Thm
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val k = Term.variable("k", numbers)

    /** `theorem` applied to `argument`, with the redex the application builds reduced away. */
    def at(theorem: Kernel.Thm, argument: Term): Either[LogicError, Kernel.Thm] =
      Conv.apThm(theorem, argument).flatMap(applied =>
        Conv
          .betaNormalise(applied.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, applied))))

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Choose,
        Type.fun(numbers, numbers),
        "\\k:num. COND (k = ZERO) (SUC ZERO) ZERO",
        "\\v:num -> num. \\i:num. \\k:num. " +
          "COND (k = ZERO) (SUC ZERO) (NUM_ADD (v (PRE k)) (v k))",
        None
      )
      (theory, definition, chooseAtZero, chooseAtSuccessor) = defined

      // **At `num` before anything is specialised.** `COND_TRUE` and `COND_FALSE` quantify their
      // two branches at `'a`, so specialising one of them at a number without instantiating the
      // type first refuses with `application: expected a, found num`, which reads as a defect in
      // the recursion rather than in the caller and is where this stage lost an hour.
      condTrue <- naturals.classical
        .fact(Classical.CondTrue)
        .map(Kernel.instType(Map("a" -> numbers), _))
      condFalse <- naturals.classical
        .fact(Classical.CondFalse)
        .map(Kernel.instType(Map("a" -> numbers), _))
      successorNotZero <- naturals.fact(Natural.SuccessorNotZero)
      preAtSuccessor <- subtractionFacts
        .get(PreAtSuccessor)
        .toRight(MissingDefinition(PreAtSuccessor))

      zero <- Parser.term(theory, notation, "ZERO", numbers)
      successorOfK <- Parser.term(theory, notation, "SUC (k:num)", numbers)
      holds = Kernel.refl(zero)
      fails <- rules.spec(k, successorNotZero)

      /* The two equations the recursion hands back are between FUNCTIONS, and the second is
         quantified over its row. So every published fact below is that equation specialised at a
         row, applied to a column, and then opened at the `COND` the column decides. */
      stepEquation <- rules.spec(n, chooseAtSuccessor)

      // The left edge. Both rows reach the answer through a condition that HOLDS, and neither
      // reads the induction hypothesis: the induction is here because the two rows are two
      // different equations and not because anything is built up.
      emptyColumn <- Parser.proposition(
        theory, notation, "!n:num. NUM_CHOOSE n ZERO = SUC ZERO")
      chooseNone <- driver.proveBy(
        emptyColumn,
        goal =>
          for {
            opened <- at(chooseAtZero, zero)
            reached <- openTrue(rules, condTrue, holds, opened)
            _ <- sameAs(goal, reached)
          } yield reached,
        step =>
          for {
            equation <- rules.spec(step.variable, chooseAtSuccessor)
            opened <- at(equation, zero)
            reached <- openTrue(rules, condTrue, holds, opened)
            _ <- sameAs(step.goal, reached)
          } yield reached
      )

      // The top row past its first entry, and Pascal's rule. The same two lines at the other
      // equation and at a column that is a successor, where the condition FAILS and what is left
      // is the second branch.
      chooseEmpty <- at(chooseAtZero, successorOfK)
        .flatMap(openFalse(rules, condFalse, fails, _))
        .flatMap(rules.gen(k, _))
        .flatMap(checked(theory, notation, ChooseEmpty, _))

      choosePascal <- for {
        opened <- at(stepEquation, successorOfK)
        selected <- openFalse(rules, condFalse, fails, opened)
        // `PRE (SUC k)` is `k`, which is the one rewrite between the shape the recursion has to
        // be written in and the shape Pascal's rule is read in.
        peeled <- rules.spec(k, preAtSuccessor)
        reached <- Rewrite.Rule
          .of(logic, peeled)
          .flatMap(rule => Rewrite.rewrite(Vector(rule), selected.conclusion))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, selected)))
          .flatMap(rules.genAll(_, List(n, k)))
        checkedFact <- checked(theory, notation, ChoosePascal, reached)
      } yield checkedFact

      chooseNoneChecked <- checked(theory, notation, ChooseNone, chooseNone)

      chooseAboveDiagonal <- chooseAbove(
        logic, theory, notation, induction, orderDefinitions, addition, chooseEmpty, choosePascal)

      onTheDiagonal <- chooseDiagonal(
        logic, theory, notation, driver, orderDefinitions, addition, chooseNoneChecked,
        choosePascal, chooseAboveDiagonal)
    } yield (
      theory,
      definition,
      Map(
        ChooseNone -> chooseNoneChecked,
        ChooseEmpty -> chooseEmpty,
        ChoosePascal -> choosePascal,
        ChooseAbove -> chooseAboveDiagonal,
        ChooseDiagonal -> onTheDiagonal
      )
    )
  }

  /**
   * `|- !m. NUM_CHOOSE m m = SUC ZERO`, the diagonal of the triangle.
   *
   * One ordinary induction over Pascal's recurrence, and the only thing it needs beyond the
   * hypothesis is that the entry one step past the diagonal is zero: `NUM_CHOOSE p (SUC p)` is
   * [[Peano.ChooseAbove]] at `p < SUC p`, so the recurrence's two summands are the hypothesis
   * and nothing.
   *
   * **`p < SUC p` is built here rather than taken from the order's own facts**, and the reason is
   * where this function sits: the block that defines `NUM_CHOOSE` has the two order *definitions*
   * and the addition, and the order's published lemmas are derived elsewhere in this file. What
   * the definitions give is enough and is three steps: `NUM_LT p (SUC p)` unfolds to
   * `NUM_LE (SUC p) (SUC p)`, which unfolds to `?d. SUC p + d = SUC p`, whose witness is `ZERO`
   * by `NUM_ADD_ZERO`.
   *
   * It exists for `Coding.NUM_CHOOSE_FACTORIAL`, which is the one case of that identity the
   * strong induction cannot reach from below: at `j = 0` the claim is about `NUM_CHOOSE n n` and
   * the sum `i + j` is `n` itself.
   */
  private def chooseDiagonal(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    driver: Induct,
    orderDefinitions: Map[String, Kernel.Thm],
    addition: Map[String, Kernel.Thm],
    chooseNone: Kernel.Thm,
    choosePascal: Kernel.Thm,
    chooseAbove: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def settled(goal: Term): Either[LogicError, Kernel.Thm] =
      Term.destEq(goal) match {
        case Some((left, right)) if left == right => Right(Kernel.refl(left))
        case _                                    => Left(NotOfForm("a closed equation", goal))
      }

    for {
      zero <- Parser.term(theory, notation, "ZERO", numbers)
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
      strictOrder <- orderDefinitions.get(StrictOrder).toRight(MissingDefinition(StrictOrder))
      nonStrict <- orderDefinitions.get(NonStrictOrder).toRight(MissingDefinition(NonStrictOrder))
      addAtZero <- addition.get(AddAtZero).toRight(MissingDefinition(AddAtZero))
      addAtZeroRule <- Rewrite.Rule.of(logic, addAtZero)
      pascalRule <- Rewrite.Rule.of(logic, choosePascal)

      statement <- Parser.proposition(
        theory, notation, "!m:num. NUM_CHOOSE m m = SUC ZERO")

      result <- driver.proveBy(
        statement,
        _ => rules.spec(zero, chooseNone),
        step =>
          for {
            here <- LogicError.lift(Term.app(successor, step.variable))

            // `p < SUC p`, out of the two definitions and the addition, in three steps.
            witnessed <- rules.specAll(addAtZero, List(here))
            reflexive <- Conv
              .unfold(nonStrict, List(here, here))
              .flatMap(equation =>
                Term
                  .destEq(equation.conclusion)
                  .toRight(NotOfForm("an equation", equation.conclusion))
                  .flatMap(sides =>
                    Conv.betaNormalise(sides._2).flatMap(Conv.trans(equation, _))))
            reflexiveBody <- Term
              .destEq(reflexive.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", reflexive.conclusion))
            reflexivePredicate <- logic
              .destExistsPredicate(reflexiveBody)
              .toRight(NotOfForm("an existential quantification", reflexiveBody))
            atZeroGap <- rules.existsIntro(reflexivePredicate, zero, witnessed)
            atMost <- Conv
              .sym(reflexive)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atZeroGap)))
            strict <- Conv
              .unfold(strictOrder, List(step.variable, here))
              .flatMap(equation =>
                Term
                  .destEq(equation.conclusion)
                  .toRight(NotOfForm("an equation", equation.conclusion))
                  .flatMap(sides =>
                    Conv.betaNormalise(sides._2).flatMap(Conv.trans(equation, _))))
              .flatMap(equation =>
                Conv.sym(equation).flatMap(back => LogicError.lift(Kernel.eqMp(back, atMost))))

            vanishes <- rules
              .specAll(chooseAbove, List(step.variable, here))
              .flatMap(rules.mp(_, strict))
            vanishesRule <- Rewrite.Rule.of(logic, vanishes)
            hypothesisRule <- Rewrite.Rule.of(logic, step.hypothesis)

            closed <- Induct.afterRewriting(
              Vector(pascalRule, hypothesisRule, vanishesRule, addAtZeroRule), step.goal)(settled)
          } yield closed
      )
    } yield result
  }

  /**
   * `|- !n k. NUM_LT n k ==> NUM_CHOOSE n k = ZERO`, the triangle above its own diagonal.
   *
   * == Written additively inside and ordered outside, which is the whole of the design ==
   *
   * The induction is not on the statement above. `NUM_LT n k` **is** `?d. NUM_ADD (SUC n) d = k`,
   * so the claim can be written `!n j. NUM_CHOOSE n (NUM_ADD n (SUC j)) = ZERO`, and in that form
   * the proof asks for no order fact, no `NUM_CASES` and no case split at all: the base is
   * [[ZeroPlus]] with [[ChooseEmpty]], and the step is [[SuccessorPlus]], Pascal's rule and the
   * hypothesis at **two** columns. Stated with `NUM_LT` the same induction wants a number known
   * positive to be a successor, and every route to that is a disjunction with an existential in
   * one branch.
   *
   * What is published is the ordered form, because that is what a consumer holds: a shifted sum
   * meets this at its last entry, where what is known is that the column has gone past the row.
   * Crossing between the two is one existential elimination and two rewrites, and it happens once.
   *
   * == The inner quantifier is why this is not `Induct.proveBy` ==
   *
   * That driver inducts on the **last** leading quantifier and leaves the others free, so
   * `!n j. P n j` would induct on `j` with `n` fixed. The step needs the hypothesis at two
   * different columns of one row, which is a claim about every column, so the column has to be
   * quantified **inside** the predicate the induction is handed. `Language.NUM_NUMERAL_INJECTIVE`
   * is the other place in this repository that meets this, and it runs `Natural.Induction`
   * directly for the same reason.
   */
  private def chooseAbove(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induction: Kernel.Thm,
    orderDefinitions: Map[String, Kernel.Thm],
    addition: Map[String, Kernel.Thm],
    chooseEmpty: Kernel.Thm,
    choosePascal: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val k = Term.variable("k", numbers)
    val d = Term.variable("d", numbers)

    /** An equation between two terms that are already the same, which is what a closed goal is. */
    def settled(goal: Term): Either[LogicError, Kernel.Thm] =
      Term.destEq(goal) match {
        case Some((left, right)) if left == right => Right(Kernel.refl(left))
        case _                                    => Left(NotOfForm("a closed equation", goal))
      }

    def normalise(equations: Vector[Rewrite.Rule])(
      theorem: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      Rewrite
        .rewrite(equations, theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    for {
      zeroPlus <- addition.get(ZeroPlus).toRight(MissingDefinition(ZeroPlus))
      successorPlus <- addition.get(SuccessorPlus).toRight(MissingDefinition(SuccessorPlus))
      addAtSuccessor <- addition.get(AddAtSuccessor).toRight(MissingDefinition(AddAtSuccessor))
      addAtZero <- addition.get(AddAtZero).toRight(MissingDefinition(AddAtZero))
      nonStrict <- orderDefinitions.get(NonStrictOrder).toRight(MissingDefinition(NonStrictOrder))
      strictOrder <- orderDefinitions.get(StrictOrder).toRight(MissingDefinition(StrictOrder))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )

      arithmetic <- Rewrite.Rule.all(
        logic, Vector(zeroPlus, successorPlus, addAtSuccessor, addAtZero))
      pascalRule <- Rewrite.Rule.of(logic, choosePascal)
      emptyRule <- Rewrite.Rule.of(logic, chooseEmpty)
      shared = arithmetic :+ pascalRule

      // The predicate the induction is handed, with the COLUMN quantified inside it.
      claim <- Parser.proposition(
        theory, notation, "!j:num. NUM_CHOOSE (n:num) (NUM_ADD n (SUC j)) = ZERO")
      predicate <- LogicError.lift(Term.abs(n, claim))
      instance <- rules.spec(predicate, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      // The base. The top row is zero at every column past the first, which is `ChooseEmpty` once
      // `NUM_ADD ZERO` is out of the way.
      baseStripped <- Logic.stripForall(baseTerm)
      baseColumn <- baseStripped._1.headOption
        .toRight(NotOfForm("a claim about every column", baseTerm))
      base <- Induct
        .afterRewriting(shared :+ emptyRule, baseStripped._2)(settled)
        .flatMap(rules.gen(baseColumn, _))
      _ <-
        if (base.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the base the induction asks for", base.conclusion))

      // The step. Pascal turns one entry into two and the hypothesis settles both, at the column
      // and at the one above it. The two instances are built BY HAND rather than offered as a
      // schematic rule, because what the arithmetic leaves is `SUC (SUC (n + j))` and a pattern
      // written `NUM_ADD n (SUC ?j)` has already been normalised past by the time it would match.
      stepStripped <- Logic.stripForall(stepTerm)
      row <- stepStripped._1.headOption.toRight(NotOfForm("a claim about every row", stepTerm))
      stepParts <- logic
        .destImp(stepStripped._2)
        .toRight(NotOfForm("an implication", stepStripped._2))
      hypothesis <- LogicError.lift(Kernel.assume(stepParts._1))
      goalStripped <- Logic.stripForall(stepParts._2)
      column <- goalStripped._1.headOption
        .toRight(NotOfForm("a claim about every column", stepParts._2))
      nextColumn <- LogicError.lift(Term.app(successor, column))
      here <- rules.spec(column, hypothesis).flatMap(normalise(shared))
      above <- rules.spec(nextColumn, hypothesis).flatMap(normalise(shared))
      hereRule <- Rewrite.Rule.of(logic, here)
      aboveRule <- Rewrite.Rule.of(logic, above)
      step <- Induct
        .afterRewriting(Vector(hereRule, aboveRule) ++ shared, goalStripped._2)(settled)
        .flatMap(rules.gen(column, _))
      _ <-
        if (step.conclusion == stepParts._2) Right(())
        else Left(NotOfForm("the step the induction asks for", step.conclusion))
      generalStep <- rules.disch(stepParts._1, step).flatMap(rules.gen(row, _))
      everywhere <- rules.conjIntro(base, generalStep).flatMap(rules.mp(opened, _))

      // And out to the order, where a consumer meets it. The witness of `NUM_LT n k` is the `j`
      // the induction was run over, one rewrite away: `SUC n + d` and `n + SUC d` are the same
      // number by the two recurrences of addition read in opposite directions.
      below <- Parser.proposition(theory, notation, "NUM_LT (n:num) (k:num)")
      assumed <- LogicError.lift(Kernel.assume(below))
      weakened <- Conv
        .unfold(strictOrder, List(n, k))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))
      successorOfRow <- LogicError.lift(Term.app(successor, n))
      witnessed <- gap(logic, nonStrict, successorOfRow, k, weakened)

      reaching <- Parser.proposition(
        theory, notation, "NUM_ADD (SUC (n:num)) (d:num) = k:num")
      reaches <- LogicError.lift(Kernel.assume(reaching))

      // `n + SUC d = SUC (n + d) = SUC n + d = k`, which is the whole of the crossing.
      through <- rules
        .specAll(addAtSuccessor, List(n, d))
        .flatMap(left =>
          rules
            .specAll(successorPlus, List(n, d))
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(left, _)))
      bridge <- Conv.trans(through, reaches)

      atWitness <- rules.specAll(everywhere, List(n, d))
      carried <- atWitness.conclusion match {
        case App(App(_, App(partial, _)), _) =>
          Conv
            .apTerm(partial, bridge)
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, atWitness))
        case other => Left(NotOfForm("an entry of the triangle", other))
      }

      withoutWitness <- rules.existsElim(witnessed, d, carried)
      result <- rules
        .disch(below, withoutWitness)
        .flatMap(rules.genAll(_, List(n, k)))
        .flatMap(checked(theory, notation, ChooseAbove, _))
    } yield result
  }

  /** `x = COND p a b` with `p` proved, carried to `x = a`. */
  private def openTrue(
    rules: Rules,
    condTrue: Kernel.Thm,
    holds: Kernel.Thm,
    opened: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    opened.conclusion match {
      case App(App(_, _), App(App(App(_, condition), whenTrue), whenFalse)) =>
        rules
          .specAll(condTrue, List(condition, whenTrue, whenFalse))
          .flatMap(rules.mp(_, holds))
          .flatMap(Conv.trans(opened, _))
      case other => Left(NotOfForm("a conditional", other))
    }

  /** `x = COND p a b` with `p` refuted, carried to `x = b`. */
  private def openFalse(
    rules: Rules,
    condFalse: Kernel.Thm,
    fails: Kernel.Thm,
    opened: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    opened.conclusion match {
      case App(App(_, _), App(App(App(_, condition), whenTrue), whenFalse)) =>
        rules
          .specAll(condFalse, List(condition, whenTrue, whenFalse))
          .flatMap(rules.mp(_, fails))
          .flatMap(Conv.trans(opened, _))
      case other => Left(NotOfForm("a conditional", other))
    }

  /** Refuse with both statements named where a derivation and its target have drifted apart. */
  private def sameAs(target: Term, theorem: Kernel.Thm): Either[LogicError, Unit] =
    if (theorem.conclusion == target) Right(())
    else Left(NotOfForm("the goal the driver opened", theorem.conclusion))

  private def partialSums(
    logic: Logic,
    driver: Induct,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    orderFacts: Map[String, Kernel.Thm],
    addFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val f = Term.variable("f", Type.fun(numbers, numbers))

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        PartialSum,
        numbers,
        "ZERO",
        "\\v:num. \\i:num. NUM_ADD v ((f:num -> num) i)",
        Some(f)
      )
      (theory, definition, sumZero, sumSuccessor) = defined

      atZero <- checked(theory, notation, PartialSumAtZero, sumZero)
      atSuccessor <- checked(theory, notation, PartialSumAtSuccessor, sumSuccessor)

      strictTransitive <- orderFacts.get(StrictTransitive).toRight(MissingDefinition(StrictTransitive))
      belowSuccessor <- orderFacts.get(BelowSuccessor).toRight(MissingDefinition(BelowSuccessor))
      congruence <- congruenceOnARange(
        logic, driver, theory, notation, atZero, atSuccessor, strictTransitive, belowSuccessor)

      reflexive <- orderFacts.get(Reflexive).toRight(MissingDefinition(Reflexive))
      addMonotoneBoth <- orderFacts.get(AddMonotoneBoth).toRight(MissingDefinition(AddMonotoneBoth))
      monotone <- monotoneOnARange(
        logic,
        driver,
        theory,
        notation,
        atZero,
        atSuccessor,
        strictTransitive,
        belowSuccessor,
        reflexive,
        addMonotoneBoth
      )

      addAtZero <- addFacts.get(AddAtZero).toRight(MissingDefinition(AddAtZero))
      addAtSuccessor <- addFacts.get(AddAtSuccessor).toRight(MissingDefinition(AddAtSuccessor))
      addAssociative <- addFacts.get(AddAssociative).toRight(MissingDefinition(AddAssociative))
      split <- partialSumSplit(
        logic, driver, theory, notation,
        addAtZero, addAtSuccessor, addAssociative, atZero, atSuccessor)
    } yield (
      theory,
      definition,
      Map(
        PartialSumAtZero -> atZero,
        PartialSumAtSuccessor -> atSuccessor,
        PartialSumCongruenceBelow -> congruence,
        PartialSumMonotoneBelow -> monotone,
        PartialSumSplit -> split
      )
    )
  }

  /**
   * The binary numerals of `num`: three definitions, their equations, and the three that cross.
   *
   * Last, and it has to be: [[EmbedsNumeralOne]] and the two below it mention `real_of_num`, the
   * bits are defined through `NUM_ADD`, and the odd bit is a successor. So it needs the addition,
   * the embedding and the two recurrences the embedding proves, which is everything the stages
   * above produce.
   *
   * The notation comes back out with the encoding added to it, rather than being added by the
   * caller, because a notation naming constants that do not exist is a notation that reads `3` and
   * then fails at the theory. The parser filters by what the theory declares, so the two would not
   * actually break; they would just be a pair a reader has to check agrees, and returning them
   * together removes the question.
   */
  private def numerals(
    logic: Logic,
    base: Theory,
    notation: Notation,
    arithmetic: Map[String, Kernel.Thm]
  ): Either[LogicError, (Theory, Notation, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      oneBody <- Parser.term(base, notation, "SUC ZERO")
      defineOne <- LogicError.lift(Kernel.defineConstant(base, NumeralOne, oneBody))
      (withOne, oneDefinition) = defineOne

      bit0Body <- Parser.term(withOne, notation, "\\n:num. NUM_ADD n n")
      defineBit0 <- LogicError.lift(Kernel.defineConstant(withOne, NumeralBit0, bit0Body))
      (withBit0, bit0Definition) = defineBit0

      bit1Body <- Parser.term(withBit0, notation, "\\n:num. SUC (NUM_ADD n n)")
      defineBit1 <- LogicError.lift(Kernel.defineConstant(withBit0, NumeralBit1, bit1Body))
      (theory, bit1Definition) = defineBit1

      // From here on the notation reads a digit string at `num` as well as at `real`. It is
      // extended after the three constants exist and not before, which is what makes the pair
      // consistent by construction rather than by inspection.
      //
      // The four operators are added at the same point and for the same reason. They are the four
      // `docs/adr/0018` admits and not the seven this development has: `NUM_SUB` is truncated and
      // `NUM_DIV` is floor division, so neither is the operation `-` and `/` name over a field, and
      // a reader who forgot that would write a lemma that is false at `y > x`. `NUM_POW` is refused
      // for a second reason, that it does not share a shape with `Power`, which takes a real base.
      // Those three keep the prefix form and the spellings `Spellings` already gives them.
      //
      // The precedences are the reals' own, which is not a convenience: one symbol with two
      // precedences is an ambiguous grammar rather than an overload, since the reader picks the
      // precedence before anything is known about types and so cannot pick it per candidate.
      spelled = notation
        .withNumerals(Natural.NumberZero, NumeralOne, NumeralBit0, NumeralBit1)
        .withInfix("+", Addition, Real.AdditionPrecedence)
        .withInfix("*", Multiplication, Real.MultiplicationPrecedence)
        .withInfix("<", StrictOrder, Real.OrderPrecedence)
        .withInfix("<=", NonStrictOrder, Real.OrderPrecedence)
        // `>` and `>=` are the same two relations read from the other end, so they are declared
        // here for the reason `Real` declares them: not overloading them would leave `!n:num. n < n`
        // reading and `!n:num. n > n` refused, an asymmetry a reader meets on their second line and
        // which this change would have INTRODUCED. `Counterpart` used to answer that refusal and
        // cannot any more, since the row it answered from is one of the four overloading removed.
        // No constant and no axiom: `a > b` builds the term `b < a`, to the node.
        .withFlippedInfix(">", StrictOrder, Real.OrderPrecedence)
        .withFlippedInfix(">=", NonStrictOrder, Real.OrderPrecedence)

      oneIsSuccessor <- checked(theory, spelled, NumeralOneIsSuccessorOfZero, oneDefinition)

      bit0At <- Conv.unfold(bit0Definition, List(n))
      bit0Doubles <- rules
        .gen(n, bit0At)
        .flatMap(checked(theory, spelled, NumeralBit0Doubles, _))

      bit1At <- Conv.unfold(bit1Definition, List(n))
      bit1Doubles <- rules
        .gen(n, bit1At)
        .flatMap(checked(theory, spelled, NumeralBit1Doubles, _))

    } yield (
      theory,
      spelled,
      Map(
        NumeralOne -> oneDefinition,
        NumeralBit0 -> bit0Definition,
        NumeralBit1 -> bit1Definition
      ),
      Map(
        NumeralOneIsSuccessorOfZero -> oneIsSuccessor,
        NumeralBit0Doubles -> bit0Doubles,
        NumeralBit1Doubles -> bit1Doubles
      )
    )
  }

  /**
   * [[PartialSumSplit]] by induction on the second addend, which is the last bound quantified.
   *
   * Both halves are a rewrite to a common term rather than an arithmetic argument, and the rule
   * set is what carries them. The base takes `m + ZERO` to `m` and the empty sum to `ZERO`, and
   * both sides land on `NUM_SUM f m`. The step takes `m + SUC n` to `SUC (m + n)` and opens both
   * sums at their successor; what is left on the left is `NUM_SUM f (m + n) + f (m + n)` and on
   * the right `NUM_SUM f m + (NUM_SUM g n + g n)`, and the induction hypothesis rewrites the first
   * summand of the left into the two of the right.
   *
   * **The associativity is in the rule set rather than applied**, which is the only thing here
   * worth a line: after the hypothesis fires, the left is bracketed to the left and the right to
   * the right, and one unconditional rewrite by [[AddAssociative]] puts both in the same shape.
   * Reaching for it by hand would mean knowing which of the two to move, and the rewriter does not
   * have to be told.
   */
  private def partialSumSplit(
    logic: Logic,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    addAtZero: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    addAssociative: Kernel.Thm,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      statement <- stated(theory, notation, PartialSumSplit)
      stripped <- Logic.stripForall(statement)
      (outer, inner) = stripped
      summand <- outer.lift(0).toRight(NotOfForm("a summand", inner))
      start <- outer.lift(1).toRight(NotOfForm("a starting point", inner))
      bound <- outer.lift(2).toRight(NotOfForm("a bound to induct on", inner))
      overEveryBound <- logic.mkForall(bound, inner)

      shared = Vector(addAtZero, addAtSuccessor, atZero, atSuccessor)

      proved <- driver.proveBy(
        overEveryBound,
        goal =>
          for {
            conversions <- normalisation(logic, shared, Vector.empty)
            base <- Rewrite.proveEquation(logic, conversions._1, goal)
          } yield base,
        step =>
          for {
            // The hypothesis goes into the rule set rather than being applied at a site chosen
            // here: it is an equation between closed terms of this proof, so it rewrites wherever
            // it matches and matches in one place.
            conversions <- normalisation(
              logic, shared ++ Vector(step.hypothesis, addAssociative), Vector.empty)
            closed <- Rewrite.proveEquation(logic, conversions._1, step.goal)
          } yield closed
      )

      result <- rules.gen(start, proved).flatMap(rules.gen(summand, _))
    } yield result
  }

  /**
   * [[PartialSumCongruenceBelow]] by induction on the bound, with the implication carried through.
   *
   * The base is `NUM_SUM f ZERO = NUM_SUM g ZERO`, which is the zero recurrence twice and does not
   * use the hypothesis at all: it is discharged from a proof that did not assume it, which is the
   * honest reading of an empty range.
   *
   * The step cannot be a rewrite of the goal, because the induction hypothesis is itself an
   * implication and has to be taken apart. Assume the agreement below `SUC v`; every index below
   * `v` is below `SUC v`, by [[StrictTransitive]] with [[BelowSuccessor]], so the agreement below
   * `v` follows and the hypothesis applies; the agreement AT `v` is the same assumption used once
   * more, at the index the successor added. What is left is
   * `NUM_ADD (NUM_SUM f v) (f v) = NUM_ADD (NUM_SUM g v) (g v)` under two equations, which is a
   * rewrite to a common term and not an arithmetic fact.
   */
  private def congruenceOnARange(
    logic: Logic,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    strictTransitive: Kernel.Thm,
    belowSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    /** The head of `NUM_LT a b`, read off a statement that uses it rather than rebuilt. */
    def strictlyBelow(sample: Term): Either[LogicError, Term] = sample match {
      case App(App(head, _), _) => Right(head)
      case other => Left(NotOfForm("an order statement", other))
    }

    for {
      statement <- stated(theory, notation, PartialSumCongruenceBelow)
      stripped <- Logic.stripForall(statement)
      (outer, inner) = stripped
      summands = outer.take(2).toList
      left <- outer.lift(0).toRight(NotOfForm("two summands", inner))
      right <- outer.lift(1).toRight(NotOfForm("two summands", inner))
      bound <- outer.lift(2).toRight(NotOfForm("a bound to induct on", inner))
      // `stripForall` takes ALL of them and the driver wants a claim about every number, so the
      // bound goes back on; the two summands stay free and are generalised at the end.
      overEveryBound <- logic.mkForall(bound, inner)

      proved <- driver.proveBy(
        overEveryBound,
        goal =>
          for {
            parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
            unfoldLeft <- rules.spec(left, atZero)
            unfoldRight <- rules.spec(right, atZero)
            conversions <- normalisation(logic, Vector(unfoldLeft, unfoldRight), Vector.empty)
            base <- Rewrite.proveEquation(logic, conversions._1, parts._2)
            result <- rules.disch(parts._1, base)
          } yield result,
        step =>
          for {
            goalParts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
            (agreesBelowSuccessor, equalSums) = goalParts
            assumed <- LogicError.lift(Kernel.assume(agreesBelowSuccessor))

            // `v < SUC v`, which is what lifts an index from below v to below its successor
            atTheVariable <- rules.spec(step.variable, belowSuccessor)

            // rebuild `u < v` for a fresh u, with the order constant taken from the statement
            openedPremise <- Logic.stripForall(agreesBelowSuccessor)
            innerParts <- logic
              .destImp(openedPremise._2)
              .toRight(NotOfForm("a bounded agreement", openedPremise._2))
            below <- strictlyBelow(innerParts._1)
            index <- openedPremise._1.lift(0).toRight(NotOfForm("one index", openedPremise._2))
            smallerTerm <- LogicError.lift(Term.app(below, index).flatMap(Term.app(_, step.variable)))
            smaller <- LogicError.lift(Kernel.assume(smallerTerm))

            // u < v and v < SUC v give u < SUC v, and the assumption then gives f u = g u. The
            // successor is read off `v < SUC v` rather than built.
            successor <- atTheVariable.conclusion match {
              case App(App(_, _), above) => Right(above)
              case other => Left(NotOfForm("an order statement", other))
            }
            liftedAt <- rules
              .spec(index, strictTransitive)
              .flatMap(rules.spec(step.variable, _))
              .flatMap(rules.spec(successor, _))
            chained <- rules.conjIntro(smaller, atTheVariable).flatMap(rules.mp(liftedAt, _))
            agreementAt <- rules.spec(index, assumed).flatMap(rules.mp(_, chained))
            agreesBelow <- rules.disch(smallerTerm, agreementAt).flatMap(rules.gen(index, _))

            // the induction hypothesis applies, and the top index is the assumption once more
            sumsBelow <- rules.mp(step.hypothesis, agreesBelow)
            top <- rules.spec(step.variable, assumed).flatMap(rules.mp(_, atTheVariable))

            // the successor recurrence on both sides, and the two equations above close what is
            // left by rewriting to a common term
            unfoldLeft <- rules.spec(left, atSuccessor).flatMap(rules.spec(step.variable, _))
            unfoldRight <- rules.spec(right, atSuccessor).flatMap(rules.spec(step.variable, _))
            conversions <- normalisation(
              logic, Vector(unfoldLeft, unfoldRight, sumsBelow, top), Vector.empty)
            settled <- Rewrite.proveEquation(logic, conversions._1, equalSums)
            result <- rules.disch(agreesBelowSuccessor, settled)
          } yield result
      )
      general <- rules.genAll(proved, summands)
    } yield general
  }

  /* ---------------------------------------------------------------- drivers */

  /**
   * The statement named, proved by induction, with both halves closed by rewriting.
   *
   * `plain` are the equations that may fire anywhere: the recurrences of whatever the statement
   * mentions and the facts already proved. `sorting` are the ones that hold in both directions and
   * may fire only where they make the term smaller, which is how a sum is ordered without a rule
   * rewriting its own output for ever. The induction hypothesis joins `plain` inside the step and
   * nowhere else.
   *
   * The comparison is between two normal forms and it has to be exact: if the rules do not bring
   * the two sides of the step together, this refuses instead of trying something else, and
   * `Rewrite.proveWith` distinguishes a difference that is about the identity from one that is
   * about the step limit.
   *
   * == Where the induction hypothesis goes in the list, and when it matters ==
   *
   * Last by default and **first** when `hypothesisFirst` is set. `Rewrite.stepConv` is a depth
   * conversion over `firstConv`, so at any one node the first rule that applies wins, and the two
   * orders differ exactly where a recurrence and the hypothesis both match the same node. Every
   * lemma above this line is one where they do not, and the default is the order those were proved
   * in.
   *
   * [[SubSuccessors]] is the one where they do: its step is `NUM_SUB (SUC m) (SUC (SUC k))` against
   * `NUM_SUB m (SUC k)`, [[SubAtSuccessor]] matches the inner `NUM_SUB (SUC m) (SUC k)` that the
   * hypothesis was for, and with the recurrence first the two sides stop at
   * `PRE (PRE (NUM_SUB (SUC m) k))` and `PRE (NUM_SUB m k)`. `Induct.settle` reaches the same
   * conclusion from a different consumer and its comment is the longer version of this one.
   */
  /**
   * Prove a listed statement by induction from a fixed set of rewrite rules.
   *
   * **The rules a law needs are decided by the terms in it, not by the operation it is about.**
   * That sounds like nothing and costs an hour. `NUM_POW_ADD`, which is a law about
   * exponentiation, has an exponent that is a SUM, so the induction opens `NUM_ADD` and needs
   * addition's recurrences in its rule set; given only multiplication's, its base case comes
   * back as
   *
   * {{{
   *   NUM_POW x (NUM_ADD y ZERO)     against     NUM_ADD ZERO (NUM_POW x y)
   * }}}
   *
   * which is the two sides each rewritten as far as the rules allow and no further. A goal pair
   * of that shape is not a false statement; it is a missing rule, and which rule is missing can
   * be read straight off the two terms that failed to meet.
   */
  /**
   * `!m n. ZERO < m ==> ZERO < NUM_POW m n`, by induction on the exponent.
   *
   * The base is `NUM_POW m ZERO = SUC ZERO` and a successor is positive; the step is
   * `NUM_POW m (SUC n) = NUM_MUL (NUM_POW m n) m` and a product of positives is positive. The
   * hypothesis carries the same side condition as the conclusion, so the step discharges it once
   * and uses it twice: on the induction hypothesis and on the base of the power.
   */
  private def powerIsPositive(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    powFacts: Map[String, Kernel.Thm],
    orderFacts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules
    for {
      statement <- stated(theory, notation, PowPositive)
      atZero <- powFacts.get(PowAtZero).toRight(MissingDefinition(PowAtZero))
      atSuccessor <- powFacts.get(PowAtSuccessor).toRight(MissingDefinition(PowAtSuccessor))
      successorPositive <-
        orderFacts.get(SuccessorPositive).toRight(MissingDefinition(SuccessorPositive))
      mulPositive <- orderFacts.get(MulPositive).toRight(MissingDefinition(MulPositive))
      recurrences <- Rewrite.Rule.all(logic, Vector(atZero, atSuccessor))
      proved <- driver.proveBy(
        statement,
        goal =>
          Induct.afterRewriting(recurrences, goal) { rewritten =>
            for {
              body <- logic.destImp(rewritten).toRight(NotOfForm("an implication", rewritten))
              positive <- rules.specTo(successorPositive, body._2)
              out <- rules.disch(body._1, positive)
            } yield out
          },
        opened =>
          Induct.afterRewriting(recurrences, opened.goal) { rewritten =>
            for {
              body <- logic.destImp(rewritten).toRight(NotOfForm("an implication", rewritten))
              (positiveBase, conclusion) = body
              assumed <- LogicError.lift(Kernel.assume(positiveBase))
              atThisExponent <- rules.mp(opened.hypothesis, assumed)
              inner <- logic.mkImp(positiveBase, conclusion)
              instance <- logic.mkImp(atThisExponent.conclusion, inner)
              both <- rules.specTo(mulPositive, instance)
              once <- rules.mp(both, atThisExponent)
              twice <- rules.mp(once, assumed)
              out <- rules.disch(positiveBase, twice)
            } yield out
          }
      )
      result <- checked(theory, notation, PowPositive, proved)
    } yield result
  }


  private[theories] def byInduction(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    name: String,
    plain: Vector[Kernel.Thm],
    sorting: Vector[Kernel.Thm] = Vector.empty,
    hypothesisFirst: Boolean = false
  ): Either[LogicError, Kernel.Thm] = {
    def withHypothesis(hypothesis: Kernel.Thm): Vector[Kernel.Thm] =
      if (hypothesisFirst) hypothesis +: plain else plain :+ hypothesis

    for {
      statement <- stated(theory, notation, name)
      proved <- driver.proveBy(
        statement,
        goal => settle(driver.logic, plain, sorting, goal),
        opened => settle(driver.logic, withHypothesis(opened.hypothesis), sorting, opened.goal)
      )
    } yield proved
  }

  /**
   * The statement named, proved by rewriting alone, for the facts that need no induction.
   *
   * `NUM_MUL n (SUC ZERO) = n` is the whole of what this is for: both recurrences apply to it and
   * what is left is a unit law already proved, so an induction would be a step with nothing in it.
   */
  private[theories] def byRewriting(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    name: String,
    plain: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- stated(theory, notation, name)
      conversions <- normalisation(logic, plain, Vector.empty)
      proved <- Rewrite.proveEquation(logic, conversions._1, statement)
      result <- checked(theory, notation, name, proved)
    } yield result

  /** Prove an equation by bringing both of its sides to the same normal form. */
  private[theories] def settle(
    logic: Logic,
    plain: Vector[Kernel.Thm],
    sorting: Vector[Kernel.Thm],
    goal: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      conversions <- normalisation(logic, plain, sorting)
      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      proved <- Rewrite.proveWith(conversions._1, sides._1, sides._2, Some(conversions._2))
    } yield proved

  /**
   * The conversion, repeated and once, from the two kinds of rule.
   *
   * Both are returned because the caller needs both: the repeated one normalises, and the single
   * pass is what the question "had the rewriting finished" has to be asked with. Asking the
   * repeated one gives a wrong answer where two rules undo each other, which `Rewrite.stepConv`
   * says at more length.
   *
   * == Why the sorting is by `Term.ordering` and not by `Arithmetic.ringOrder` ==
   *
   * `Arithmetic.ringOrder` exists because over the reals the sorting has a second job: it has to
   * put a term next to its own negation, so that the two are neighbours and one rule cancels them.
   * Sorting a ring expression by the kernel's own order breaks that silently, which is why the
   * warning about it is written where it is.
   *
   * Nothing here cancels. There is no negation over `num` and no inverse, and the subtraction this
   * file defines is not one either: `NUM_SUB` is truncated, `m - m` reaches `ZERO` by its own lemma
   * rather than by two terms meeting and annihilating, and no rule below ever puts a term next to
   * anything it cancels against. So what the ordered rules have to do is only to make a sum's
   * summands land in one arrangement, and any total order does that. `Term.ordering` is one, it is
   * the kernel's and needs no argument of its own, and the termination argument is the one
   * `Arithmetic` gives: the unconditional rules
   * strictly reduce how much structure is left to expand, and the ordered ones leave the size of
   * the term alone while strictly decreasing a total order on the finitely many terms of that size.
   */
  private[theories] def normalisation(
    logic: Logic,
    plain: Vector[Kernel.Thm],
    sorting: Vector[Kernel.Thm]
  ): Either[LogicError, (Rewrite.Conversion, Rewrite.Conversion)] =
    for {
      unconditional <- Rewrite.Rule.all(logic, plain)
      ordered <- Rewrite.Rule.all(logic, sorting)
    } yield {
      // These six lines were written out here and are `Rewrite.passOver`, which `normaliser`
      // built inside itself and did not publish. That made this the third copy of the pass whose
      // own docstring says why there is one function rather than one per arithmetic, and nothing
      // compared them, so it was invisible. Published on 2026-09-18 and called here; `normaliser`
      // is the same expression repeated, with the refusal `Rule.iterable` carries.
      val once = Rewrite.passOver(unconditional, ordered, Term.ordering)

      (Rewrite.normaliser(unconditional, ordered, Term.ordering), once)
    }

  /** Carry an equation into a term that mentions its left side, as `Series` does. */
  /** The statement named, read from the text this file writes it by. */
  private[theories] def stated(
    theory: Theory,
    notation: Notation,
    name: String
  ): Either[LogicError, Term] =
    statements.get(name) match {
      case None => Left(MissingDefinition(name))
      case Some(text) => Parser.proposition(theory, notation, text)
    }

  /**
   * The theorem, if it is the statement as written.
   *
   * Every fact of this development goes through here. A derivation that reaches something else is
   * a refusal and not a fact under the wrong name, which is the mistake this catches: a recurrence
   * whose quantifiers came out in the other order, or a lemma about the variable the driver chose
   * rather than the one the statement names, are both true theorems and neither is the one asked
   * for.
   */
  private[theories] def checked(
    theory: Theory,
    notation: Notation,
    name: String,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- stated(theory, notation, name)
      result <-
        if (theorem.conclusion == statement) Right(theorem)
        else Left(NotOfForm(s"$name as it is written", theorem.conclusion))
    } yield result

  private[theories] def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private[theories] def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))
}
