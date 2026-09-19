package garden.xeno.symbolum.theories

import garden.xeno.symbolum.logic.*

/**
 * Everything this repository proves, in one signature, in the order that works.
 *
 * The naturals and the reals were the whole of it until 2026-09-12 and are still the part the order
 * argument is about, so that argument is first and is unchanged; what sits above the pair is the
 * section after it.
 *
 * The order is not free and it is not obvious: **the naturals are built first and the reals over
 * them.** The tactics are constructed over a `RealTheory`, so if the reals came first, `Ring`,
 * `Order` and `Arithmetic` would be reading a signature that has no `num` in it, and a goal
 * mentioning a natural number would be outside every one of them. Building the other way round
 * gives a signature with both types and tactics that read half of it, which is a failure that looks
 * like a tactic being weak rather than like a chain being assembled backwards.
 *
 * That was documented and documented is better than nothing. This makes it un-mistakable instead of
 * known, which is the difference the card asked for.
 *
 * == What is in it, and what "in it" buys ==
 *
 * Everything this repository has proved. Until 2026-09-12 five developments sat **beside** this
 * chain rather than in it, each built over a second copy of the arithmetic below it:
 * `Divisibility`, `Modular`, `Product`, `Word` and `Bounded`. Being beside it is not a smaller
 * version of being in it, and the cost was not duplicated work:
 *
 *  - A constant defined over a theory of one's own is a **different constant** with the same name,
 *    which `docs/adr/0008` is about. So `Divides x y /\ Sum f n = 0` was not a proposition in any
 *    signature that existed, and no amount of care at the call site could make it one.
 *  - `Library.of` collects the chain's developments, so the facts of the five were in no library.
 *    `docs/lemmas.md` is generated from that library, so they were in no document either, and
 *    `docs/naming.md` had to carry the absence as a paragraph of prose.
 *  - `Prove`, `Ask` and `Find` all read [[widest]]. A goal about `NUM_GCD` could not be typed, so
 *    could not be refused by name either: it came back as a parse error about an unknown constant.
 *
 * The four that declare something are now links in the same chain and [[widest]] is built over all
 * of them. `Bounded` declares nothing and is a driver, so it sits beside `Induct` instead; see its
 * field comment.
 *
 * == It is not a cache, and the measurement says so ==
 *
 * Each stage is built once here, and the reason is the order and not the cost. The card that
 * proposed it measured the stages first and withdrew its own speed argument, and `ChainSpec` prints
 * a reading rather than asserting a bound, for the reason that file gives.
 *
 * The reading was about 110 ms while the chain ended at `Series`. It is larger since 2026-09-12,
 * and how much larger is not a number this machine can supply: three runs on one afternoon printed
 * 214, 253 and 1137 ms, which is the spread this repository has already stopped asserting against
 * after four tests with a stopwatch went red on correct code. What is worth saying instead is what
 * was added, which is four developments and forty-eight derived facts, and that it is paid once per
 * process. Anybody proposing this arrangement for speed has the wrong argument; anybody worried
 * about the cost should count inferences, which `Derivation.size` does and a clock here does not.
 */
final class Chain private (
  val classical: Classical,
  val naturals: Natural,
  val reals: RealTheory,
  val arithmetic: Arithmetic,
  val ring: Ring,
  val order: Order,
  val series: Series,
  /**
   * Arithmetic and order on `num`, and the series are built **over** it.
   *
   * The order between these two was the whole of the question and it was settled twice. Until
   * 2026-09-11 `Peano` and `Series` were siblings over the reals and the chain built neither on the
   * other, so nothing in it declared `NUM_ADD`, `NUM_MUL` or `NUM_LE` and the arithmetic on `num`
   * that landed on 2026-09-10 was unreachable from the widest signature this repository assembles.
   * That was repaired by putting `Peano` on top of `Series`, which made every constant sayable and
   * left one thing that is not the same: a constant can be **named** in a goal without being usable
   * **inside** a definition made earlier. `Sum (\i. f (NUM_ADD m i)) n` was still not a
   * proposition, because `Sum` had been defined over a theory with no addition in it.
   *
   * So the order is the other way round now, and it is the one that gives both: `Peano` needs
   * nothing from `Series`, `Series` needs `NUM_ADD` under its own binder, and `Series.Reindex` is
   * what comes out. `Series` was [[Chain.widest]] for a day because of it, and is not any more:
   * five further developments went on top on 2026-09-12 and the last of them is [[word]]. The
   * argument above decides `Peano` against `Series` and nothing else; it does not decide what sits
   * above the pair.
   *
   * The first half of that was found by a trap corpus for the naturals, which wrote `NUM_LE ZERO n`
   * and had it read as a **free variable**: an unknown letter-initial name parses as one, so the
   * statement was well-typed, about an arbitrary function, and separated from its twin for a reason
   * that had nothing to do with the naturals. The guard that caught it is in that file and is the
   * first assertion of it.
   */
  val peano: Peano,
  /**
   * Divisibility over the reals, defined over everything above it rather than beside it.
   *
   * The first of the five developments that were built beside this chain until 2026-09-12 and are
   * in it since. Each of them was reachable only by constructing a second copy of the arithmetic
   * underneath it, and the consequence was not inconvenience: a `Divides` defined over a bare
   * `RealTheory` is a different constant from the one defined here, so a claim naming it and `Sum`
   * together was not a proposition anywhere, `Library.of` could not collect the facts, and
   * `docs/lemmas.md` did not list them. `docs/naming.md` said so in its own prose, which is how the
   * absence was visible at all.
   */
  val divisibility: Divisibility,
  /** Divisibility, congruence and the greatest common divisor on `num`, over [[divisibility]]. */
  val modular: Modular,
  /** The type of a pair, over [[modular]], so that `prod` sits in the same signature as `num`. */
  val product: Product,
  /** Finite words over [[product]], the only one of the five that needs another of them. */
  val word: Word,
  /**
   * Two-by-two real matrices, appended to the chain where the five were moved into it.
   *
   * This read "and the last link rather than one of the five" until 2026-09-19. That was true on
   * the day it was written and false from the next link onwards, and it is the one of the four
   * claims in this file that carried no date at all, which is the form `Rotation.scala` and
   * `Concatenation.scala` each had removed from them once before. Which link is the end is
   * [[widest]] and is not written in prose; what the sentence was for survives without the claim,
   * and it is the contrast in the line above.
   *
   * It arrived on 2026-09-12, after the five went in, and it went straight into the chain for the
   * reason they had to be moved into it: a `MAT_DET` defined beside this would be a constant no
   * claim mentioning `Sum` or `NUM_GCD` could be stated alongside, its facts would reach no
   * library, and `docs/lemmas.md` would not list them. That argument was settled that morning and
   * is not re-litigated per development.
   *
   * It extends [[word]] and needs nothing from it: what it needs is [[product]], for the type, and
   * [[ring]], which settles every one of its component equations. The order between it and `Word`
   * is therefore free, and it is second because a development with no prerequisite belongs at the
   * end, where adding it moves nothing below it.
   */
  val matrix: Matrix,
  /**
   * The rotation of a word, and the last extension of the signature until 2026-09-13.
   *
   * A development that needs two of the others at once: [[word]] for the type it rebuilds, and
   * [[modular]] for the `NUM_MOD` that sits inside its own definition. That is why it could not
   * live in `Word`, whose own standard development is built below `Modular` and cannot even state
   * it, and why it extends [[matrix]] rather than sitting beside it. It was [[widest]] itself until
   * [[magnitude]] joined, and what is last is the only thing that moved.
   */
  val rotation: Rotation,
  val induct: Induct,
  /**
   * The bounded-universal driver, which declares nothing and is therefore not in the order at all.
   *
   * It sits beside [[induct]] rather than in the run of signature extensions above, and the reason
   * is worth one line: `Bounded.construct` defines no constant and no type, so it extends no
   * theory, so nothing downstream of it could be widened by it. Both of these are proof drivers
   * over a signature somebody else assembled, and putting either in the chain's extension order
   * would suggest it contributes to the signature, which is the one thing a reader must not
   * conclude. Neither holds a `facts` map, so neither reaches `Library.of` either.
   *
   * There are three of them since 2026-09-13 and [[successor]] is the third, on the same argument.
   */
  val bounded: Bounded,
  /**
   * A number written as a numeral, opened into the successors every recurrence over `num` is
   * stated at.
   *
   * The third driver, and here for the reason the two above are: it declares nothing, so nothing
   * downstream could be widened by it. What it needs is both halves at once, `Peano` for the
   * encoding and the addition that collects it and `Series` for the two recurrences of the power,
   * and neither of those holds the other. A caller reaching it through the chain is reaching the
   * one built over the same signature its goal is written in, which is the whole reason the five
   * developments were moved into this chain on 2026-09-12.
   */
  val successor: Successor,
  /**
   * The larger of two reals, the smaller, the distance from zero and the sign, and the last
   * extension of the signature.
   *
   * It joined on 2026-09-13, nine months after the argument for putting a development in this
   * chain was settled and a day after five of them were moved in on it. Being outside was not a
   * smaller version of being inside, and the cost is the one the [[divisibility]] comment lists,
   * met twice over: seventeen proved facts reached no library, so `docs/lemmas.md` did not list
   * them; and `max`, `min`, `abs` and `sgn` were not constants of [[widest]], so a goal naming
   * `abs` beside `Sum` **parsed**, as a claim about a free variable of that name, and nothing
   * refused. That is the trap the [[peano]] comment records for `NUM_LE ZERO n`, and it was still
   * live here.
   *
   * Nothing that was built before it changed. It needs [[classical]] for the choice operator its
   * first line checks for and [[order]] for eight facts, both of which sit far below, and nothing
   * in the chain needs `max`, so it goes where adding it moves nothing: last, which is the
   * argument [[matrix]] makes for its own position.
   */
  val magnitude: Magnitude,
  /** The bottom of the Goedel numbering: the factorial and the Chinese remainder theorem. */
  val coding: Coding,
  /**
   * Theorems about the primes that are results rather than infrastructure.
   *
   * It sits above [[coding]] and not in [[modular]] for one reason: Euclid's theorem is proved from
   * the factorial, which `Coding` defines. Like [[deduction]] it declares nothing.
   */
  val primes: Primes,
  /** The Goedel numbering of the object language, starting at the pairing. */
  val numbering: Numbering,
  /** The embedded theory's own language, coded as numbers. */
  val language: Language,
  /** What that language can prove, which is the last thing before the diagonal. */
  val provability: Provability,
  /**
   * Derivations of the embedded theory, which is the first link whose product is not a definition.
   *
   * `docs/adr/0013` decided that a development producing object-level derivations is its own piece
   * of work rather than a helper inside whichever development first needs one, and this is it. It
   * declares no type and no constant, so [[widest]] does **not** move to it: the last link and the
   * widest signature stopped being the same thing when this landed.
   */
  val deduction: Deduction,
  /**
   * Convergence and the limit of a sequence of reals, and the first analysis in the chain.
   *
   * It is above the arithmetisation rather than beside it for the reason every link above [[peano]]
   * is where it is: it declares `converges` and `lim`, and a constant declared into a side branch
   * is unreachable from everything. Nothing in `Provability` needs a limit and nothing here needs a
   * provability predicate, so the order between the two is free and this is second because it was
   * written second.
   */
  val limit: Limit,
  /**
   * The exponential, the sine, the cosine and the logarithm.
   *
   * Four constants that are definitions and no axiom, which `docs/adr/0017` decides. It was
   * [[widest]] from 2026-09-15 until [[concatenation]] landed on it the next day, and this sentence
   * named it as the current one for the day after that: [[widest]] is where to read which link is,
   * and the paragraph on that field says why no docstring here should answer it.
   *
   * It is above [[limit]] because it is the only link that needs it, and nothing decides how far
   * above: the order over [[magnitude]] is free, and a development with no dependent belongs
   * wherever adding it moves nothing below it.
   */
  val transcendental: Transcendental,
  /**
   * Concatenating two words, and the three relations that are nothing but that.
   *
   * It was [[widest]] for part of 2026-09-16 and is not, because two links went on top of it the
   * same day. The field is what to read for which one is; this sentence deliberately no longer
   * names it.
   *
   * Six constants and no axiom, and the position is the one the last four links have taken: it
   * needs [[word]] for the type and [[peano]] for fourteen facts about `num`, both far below, and
   * it extends [[transcendental]] because that is where the chain's end is. The extension order and
   * the dependency order are different things and `Rotation.construct`'s comment is the one that
   * says so.
   *
   * It is not in `Word.scala`, and that is a decision rather than a constraint: `Rotation` **had**
   * to be a development of its own because `NUM_MOD` is outside `Word.standard`'s signature, and
   * nothing here is. `Concatenation`'s own docstring carries the argument that decided it.
   */
  val concatenation: Concatenation,
  /**
   * The set defined by rules.
   *
   * Two constants, `MONOTONE` and `INDUCTIVE`, and no axiom. It sits where it does because the
   * order over [[magnitude]] is free and it needs none of the links under it: nothing in it
   * mentions a number, a word or a pair, so what it extends is whatever the chain's end was when it
   * landed rather than anything it depends on, which is the distinction `Rotation.construct`'s
   * comment draws. It was that end for the hours between landing and [[reaching]], and this
   * sentence said it was still the last link for the day after.
   *
   * Being in the chain rather than beside it is not free to choose either way. It declares
   * constants, so a version sitting outside would declare them into a theory nothing else can see,
   * its facts would reach no library and `docs/lemmas.md` would not list them. That is the defect
   * `ChainCoverageSpec` exists to make fail rather than be noticed, and it is the same argument the
   * five developments moved into the chain on 2026-09-12 were moved by.
   */
  val inductive: Inductive,
  /**
   * Derivations of a relation with their length.
   *
   * The first thing built on [[inductive]] and the reason it was built: `REACH R A x q` says `FST q`
   * is reachable from `x` spending `SND q` steps of `A`, so the reflexive-transitive closure and the
   * length of a derivation are one construction rather than two. One constant, no axiom.
   *
   * It needs [[inductive]] for the closure, [[product]] for the pair the count rides in and
   * [[peano]] for the arithmetic its potential-function lemma is stated in. What it extends is the
   * chain's end as it stood, which is [[inductive]]'s theory, and that those coincide here is an
   * accident of ordering rather than the reason.
   */
  val reaching: Reaching,

  /**
   * The right forward closure of a string rewriting system.
   *
   * The second thing built on [[inductive]] and the one the rewriting work was for: `RFC(R)` is
   * the least set holding the right-hand sides of `R` and closed under a step anywhere inside a
   * member and under extending a member on the right by a rule that overlaps its end. Two
   * constants, no axiom, and the four facts it publishes cost none either.
   *
   * It is built over [[concatenation]] rather than beside it, because the inside-reduction clause
   * says the left-hand side occurs with a context on each side and that sentence needs
   * `WORD_CONCAT`. Before 2026-09-16 it could not be written at all.
   */
  val forward: Forward,
  /**
   * The integers, and the fifth type operator this chain declares.
   *
   * A quotient of `prod(num,num)` under `a + d = c + b`, which `docs/adr/0016` names as the first
   * real consumer of the quotient builder and which that record's own alternatives section rejects
   * the cheap version of. It needs [[peano]] for the arithmetic its carrier's equations are settled
   * by and [[product]] for the pair, both far below, and it extends [[forward]] because that is
   * where the chain's end was: the extension order and the dependency order are different things,
   * which is `Rotation.construct`'s sentence and the one every link above [[magnitude]] has been
   * placed by.
   *
   * What it is **for** is not the construction of the reals. Two open formalisations were blocked
   * on a signed ring in two different ways at once, `Divisibility` stating its condition vacuously
   * over a field and [[modular]] unable to state it at all, and neither is repaired by moving a
   * file.
   */
  val integers: Integer,
  /**
   * The integers inside the reals, and the one piece of [[integers]] that mentions a real.
   *
   * `real_of_int`, the facts that make it a ring embedding, and the order map. It is a link of its own rather
   * than a section of `Integer.scala` because that file says of itself that nothing in it reaches
   * for a real, and `docs/adr/0033` rests a consequence on the sentence: when the reals are
   * constructed, that development moves below `Real` instead of being rewritten, and this is the
   * one part of it that cannot make the move. `docs/adr/0016` has the precedent one type down,
   * where the seventeen facts of `Peano` that cannot be stated without the reals went into
   * `Embedding.scala`.
   *
   * It declares one constant and no axiom, which is why it costs nothing to put it here: what a
   * link buys is that the constant is reachable from `Ask`, from `Find` and from `docs/lemmas.md`,
   * and what it costs is a row in `docs/reading-register.md`.
   */
  val inclusion: Inclusion
) {

  /**
   * The signature that holds everything this chain assembled.
   *
   * `Language` is built last and over all of the others, so it is the one that declares `NUM_ADD`,
   * `NUM_MUL`, `NUM_LE`, `real_of_num`, `Sum`, `Power`, `Prod`, `Divides`, `NUM_DIVIDES`,
   * `NUM_CONG`, `NUM_GCD`, `PAIR`, `FST`, `SND`, the word operations, the matrix operations,
   * `max`, `min`, `abs`, `sgn`, `NUM_FACT`, `NUM_PROD`, `NUM_BETA`, `NUM_TRI`, `NUM_PAIR`,
   * `NUM_CODE` and `NUM_TERM` at once. A caller stating a goal about
   * any of them wants this rather than a guess about which development owns which constant.
   *
   * **The name of the last link is not written here any more, and that is the point of the field.**
   * It was `Series` until 2026-09-12, `Word` for a few hours of that day, then `Matrix`, then
   * [[rotation]], [[magnitude]], [[coding]], [[numbering]], [[language]], [[transcendental]], and
   * on 2026-09-16 one more: nine entries in five days. The paragraph that used to stand here named
   * the current one, was corrected twice for it, and had gone stale a third time before this
   * sentence replaced it, naming `language` while the field read `transcendental`. A prose name for
   * a thing that moves this often is a defect with a schedule. The rule is what does not move: the
   * widest signature is whatever link extended the theory last, because a constant declared into a
   * side branch is unreachable from everything, and this field is the one place to read which that
   * is.
   *
   * What makes the move necessary rather than cosmetic is that `docs/lemmas.md` is printed through
   * this signature: a library carrying `FST_PAIR` and a `widest` that cannot name `FST` would
   * generate a document of lemmas nobody can parse back, and the same goes for `MAT_DET_MUL` and
   * for `WORD_ROTATE`.
   */
  val widest: Signature = inclusion

  /**
   * The logic, read against the widest signature of the chain, which is what a caller wants.
   *
   * That sentence was the docstring before 2026-09-12 and was **not** what the field held: it was
   * `induct.logic`, and `Induct.construct` widens over `ring.reals.theory`, which is two stages
   * below [[widest]]. So a caller building a quantifier over a goal that mentioned `Sum` or
   * `NUM_ADD` asked a theory that had never heard of either. Nothing caught it because the callers
   * that needed the wider one, `Series` and `Peano`, had built their own.
   *
   * **It said it was repaired by reading the field off [[widest]], and it was not: it named a
   * development by hand and read `magnitude.logic`.** So the same defect came back on 2026-09-13
   * the moment [[coding]] became the last link, and for a day this logic could not name `NUM_FACT`
   * or `NUM_PROD` while [[widest]] could. That is the identical failure the paragraph above
   * records, reintroduced by the one line the paragraph was about, which is what a correction
   * written as prose beside a value maintained by hand is worth.
   *
   * It now reads [[widest]], so the two cannot disagree again. That is why this field is below it
   * rather than above: a `val` here that referred to a later one would be `null`, and the ordering
   * is the thing keeping them in step.
   */
  val logic: Logic = widest.logic
}

object Chain {

  /** The standard chain, built once. */
  lazy val standard: Chain =
    construct(Classical.standard).fold(
      error => throw new IllegalStateException(s"the standard chain does not build: ${error.message}"),
      identity
    )

  /**
   * The chain over a classical logic of one's own.
   *
   * Written as one comprehension deliberately: the order is the content of this function, and a
   * reader checking it should be able to read it top to bottom without following a call.
   */
  def construct(classical: Classical): Either[LogicError, Chain] =
    for {
      naturals <- Natural.construct(classical)
      reals <- Real.construct(classical.logic, naturals.theory)
      arithmetic <- Arithmetic.construct(reals)
      ring <- Ring.construct(arithmetic)
      order <- Order.construct(ring)
      peano <- Peano.construct(naturals, ring, order)
      series <- Series.construct(peano, order)

      // The five that were beside this chain until 2026-09-12, in the order their prerequisites
      // force. The first three are interchangeable among themselves and are written cheapest first:
      // `Divisibility` needs only the reals, `Modular` needs the arithmetic of `num`, `Product`
      // needs neither and is put where it is so that the two type definitions are adjacent.
      // `Word` is the only one that is not free to move: its representation is
      // `prod(num, num -> 'a)`, so it needs a `Product` and it needs one over a theory that already
      // holds `num`.
      divisibility <- Divisibility.construct(ring, series.theory)
      modular <- Modular.construct(peano, divisibility.theory)
      product <- Product.construct(classical, modular.theory, peano.notation)
      word <- Word.construct(peano, product)

      // The sixth, and the one that was never beside the chain. It needs `Product` for the type it
      // is a pair of pairs of, and `Ring` for every component equation; it needs nothing from
      // `Word`, and extends it only because a development with no prerequisite belongs last.
      matrix <- Matrix.construct(ring, product, word.theory)

      // The seventh, and the last until `Magnitude` joined on 2026-09-13, because it needs two of
      // the others at once: `Word` for the type it rebuilds and `Modular` for the `NUM_MOD` inside
      // its own definition. It extends `matrix.theory` rather than `word.theory` for the reason the
      // comment in `Rotation.construct` gives: a constant declared into a side branch is
      // unreachable from everything, and `widest` is built over this one.
      rotation <- Rotation.construct(word, modular, matrix.theory)

      induct <- Induct.construct(naturals, ring)
      bounded <- Bounded.construct(peano)

      // The third driver, and it needs both halves: `Peano` for the numerals and the addition
      // that collects them, `Series` for the two recurrences of the power. It declares nothing,
      // so it is not in the extension order above and its position here is free.
      successor <- Successor.construct(peano, series)

      // Last, and the position is free: nothing in the chain needs `max`. It was outside the chain
      // until 2026-09-13, which cost its seventeen facts every document and let a goal naming `abs`
      // parse as a claim about a free variable.
      magnitude <- Magnitude.construct(classical, order, rotation.theory, rotation.notation)

      // Last, and it extends `magnitude.theory` rather than `modular.theory`, which is where its
      // prerequisites are. The two orders are different things and `Rotation.construct`'s comment
      // is the one that says so: a constant declared into a side branch is unreachable from
      // everything, and `widest` is built over the last extension. `Coding` draws its facts from
      // `Modular` and declares `NUM_FACT` into the widest theory there is.
      //
      // It was outside the chain from the day it was written until 2026-09-13, a few hours, and
      // that cost `NUM_FACT` and its four facts every document exactly as `Magnitude`'s seventeen
      // were costing them that morning. `ChainCoverageSpec` is what makes the third time fail
      // rather than be noticed.
      coding <- Coding.construct(modular, magnitude.theory, magnitude.notation)

      // Beside the extension order, like `bounded` and `deduction`: it declares nothing and is a
      // field here so that `Library.of` reaches its facts.
      primes <- Primes.construct(coding)

      // The arithmetisation, landed 2026-09-14. It extends the arithmetic rather than sitting
      // beside it because `docs/adr/0014` decides that a term of the embedded theory IS a number,
      // so what it adds is the pairing and the constructor and not a syntax.
      //
      // This read "The last link since 2026-09-14, and the first one that is about a language" and
      // both halves went on 2026-09-19. The first is the claim this file stopped writing in prose,
      // and `widest` is where it is read. The second was held by TWO bindings at once: `language`,
      // the next binding, makes it in the same words and out of the same record, and at most one
      // link can be first. It belongs there, because `NUM_TERM` is where the embedded language
      // starts and the constants here are numbers that happen to code one.
      numbering <- Numbering.construct(coding, coding.theory, coding.notation)

      // The first link that is about a language rather than about numbers, which under
      // `docs/adr/0014` is the same thing: `NUM_TERM` is a predicate on `num`.
      language <- Language.construct(
        numbering, induct, successor, numbering.theory, numbering.notation)

      // Landed 2026-09-14. It is about the language rather than part of it: nothing in it declares
      // a constructor or a predicate of the object syntax, and it is a separate development for
      // that reason rather than because `Language.scala` was getting long.
      //
      // This read "The last link since 2026-09-14" until 2026-09-19, which is word for word what
      // `numbering` said three bindings above with the same date on it. At most one of the two
      // could have been the last link on any day, so the pair was unusable whichever way "since"
      // was read, and neither said what the last link is now. `widest` does.
      provability <- Provability.construct(language, language.theory, language.notation)

      // Beside the extension order rather than in it, the way `bounded` is: it declares nothing and
      // extends nothing, and what it produces is derivations of the embedded theory. It is a field
      // here rather than a development sitting outside because `Library.of` collects the chain's
      // developments, and a fact reachable from no library is in no document either.
      deduction <- Deduction.construct(provability)

      // The first analysis this repository has: what a sequence of reals converges to and the value
      // it converges to, both definitions. It extends `provability.theory` rather than
      // `magnitude.theory`, where its prerequisites are, for the reason `Rotation.construct`'s
      // comment gives: the extension order and the dependency order are different things, and
      // `widest` is built over the last extension.
      limit <- Limit.construct(
        magnitude, peano, series, reals, induct, provability.theory, provability.notation)

      // Landed 2026-09-15 and was the last link until `concatenation` went on top of it the next
      // day, which the binding below says of itself. It is the only one that needs a limit, and
      // this read "The last link since 2026-09-15" until 2026-09-19. `docs/adr/0017` is the
      // decision it spends: these four constants are their power series rather than four axioms, so
      // the trusted base does not move and `TranscendentalSpec` asserts that as an equality rather
      // than as a ceiling.
      transcendental <- Transcendental.construct(
        limit, series, peano, coding, induct, successor, naturals, limit.theory, limit.notation)

      // Landed 2026-09-16 and was the last link for part of that day. It needs `word` for the type and `peano` for the arithmetic
      // of an index, and it extends `transcendental.theory` because that is the chain's end: a
      // constant declared into a side branch is unreachable from everything, which is the sentence
      // `Rotation.construct` carries and the one every link above `magnitude` has been placed by.
      concatenation <- Concatenation.construct(word, peano, transcendental.theory)

      // The only link whose prerequisites are empty: `MONOTONE`
      // and `INDUCTIVE` are polymorphic and mention nothing this chain built. So what it takes is
      // the last theory rather than a theory it needs, which is the one case where
      // `Rotation.construct`'s distinction between the two orders is the whole of the argument.
      inductive <- Inductive.construct(
        classical, concatenation.theory, concatenation.notation)

      // The first consumer of the one below it. Unlike
      // `Inductive` its prerequisites are not empty -- it needs the closure, the pair and the
      // arithmetic -- and they still do not decide where it goes: what it extends is the chain's
      // end as it stands here, for the reason `Rotation.construct`'s comment gives.
      reaching <- Reaching.construct(
        inductive, peano, product, inductive.theory, inductive.notation)

      // Over `reaching` rather than beside it, so the widest signature carries both. Nothing here
      // needs a derivation's step count, but a goal about a closure and a goal about a derivation
      // should be typable against one theory rather than two.
      forward <- Forward.construct(
        inductive, concatenation, reaching.theory, reaching.notation)

      // The fifth type operator. It needs `peano` for the arithmetic of the carrier and `product`
      // for the pair; what it extends is the chain's end as it stands here, for the reason
      // `Rotation.construct`'s comment gives. This read "and the last link" until 2026-09-18 and
      // stopped being true in the commit that added `inclusion` two bindings below it and moved
      // `widest` off this one in the same diff, which is the defect `widest`'s own docstring is
      // about, met beside the field rather than in prose about it. Nothing went red on it:
      // `DocumentationSpec` holds the `widest` claim and says in writing that a positional "is
      // last" has no shape it can separate from the prose around it, so which link is the end is
      // read off `widest` and is not written here.
      integers <- Integer.construct(
        classical, peano, product, forward.theory, forward.notation)

      // The one part of the integers that mentions a real, and so the one part that cannot move
      // below `Real` when the construction arrives. It needs `integers` for the quotient it lifts
      // through, `product` for the two projections, `peano` for the facts that carry `real_of_num`
      // through the arithmetic of the carrier, and `ring` to close the identities that are left;
      // what it extends is the chain's end as it stands here, which is also the theory the quotient
      // is re-based onto and the one place that re-basing is checked.
      inclusion <- Inclusion.construct(
        classical, integers, product, peano, ring, order, integers.theory, integers.notation)
    } yield new Chain(
      classical,
      naturals,
      reals,
      arithmetic,
      ring,
      order,
      series,
      peano,
      divisibility,
      modular,
      product,
      word,
      matrix,
      rotation,
      induct,
      bounded,
      successor,
      magnitude,
      coding,
      primes,
      numbering,
      language,
      provability,
      deduction,
      limit,
      transcendental,
      concatenation,
      inductive,
      reaching,
      forward,
      integers,
      inclusion
    )
}
