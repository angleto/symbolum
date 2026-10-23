package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import scala.jdk.CollectionConverters.*

class LibrarySpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val chain = Chain.standard
  private val library = Library.of(chain)

  "The library" should "hold everything the chain assumed and everything it derived" in {
    // The count is the assertion: a development whose facts stop being collected drops out here
    // rather than in somebody's search coming back empty.
    //
    // The four that arrived on 2026-09-12 are the second half of the assertion and the reason it is
    // written as a sum rather than as a number: `Divisibility`, `Modular`, `Product` and `Word`
    // were beside the chain until then, so their facts were in no library and in no document.
    // `Bounded` is the fifth and is deliberately absent: it holds no facts of its own.
    // `Classical` is the sixth and last of these and arrived on 2026-09-12. It is not a development
    // of `modules/theories` at all, which is exactly why nothing here reached it: the list below is
    // written by hand, so a thing that is not on it is invisible rather than wrong. This assertion
    // caught that the moment the library gained it and the sum did not, which is what a sum asserts
    // that a literal cannot.
    val expected = chain.classical.definitions.size + chain.classical.facts.size +
      chain.reals.laws.size + chain.reals.definitions.size +
      chain.ring.positivity.facts.size + chain.order.facts.size +
      chain.naturals.facts.size + chain.peano.facts.size + chain.series.facts.size +
      chain.divisibility.facts.size + chain.modular.facts.size +
      chain.product.facts.size + chain.word.facts.size + chain.matrix.facts.size +
      chain.rotation.facts.size + chain.magnitude.facts.size + chain.coding.facts.size +
      chain.numbering.facts.size + chain.language.facts.size +
      chain.provability.facts.size + chain.deduction.facts.size +
      // The truth of the object language, 2026-09-25, added after this sum caught it.
      chain.truth.facts.size +
      chain.primes.facts.size +
      // The two of 2026-09-15. This sum is the assertion's whole point and it caught them: they
      // were added to `Library.of` and not to this list, and what failed was the count rather than
      // anything about the developments, which is the shape of failure the comment above describes.
      chain.limit.facts.size + chain.transcendental.facts.size +
      // 2026-09-16, and this sum caught it too: fifteen facts in `Library.of` and not here.
      chain.concatenation.facts.size +
      // And the two of 2026-09-16, which this sum caught the same way: each was in `Library.of`
      // and not here, so the count moved and nothing about the development did.
      chain.inductive.facts.size + chain.reaching.facts.size +
      chain.forward.facts.size +
      // 2026-09-18, and added here in the change that added the link rather than after this sum
      // caught it, which is what the three comments above record happening three times.
      chain.integers.facts.size +
      // The bridge into the reals, the same day and the same discipline. It is the piece of the
      // link above that mentions a real, and it is a development of its own for the reason
      // `Inclusion`'s first paragraph gives, so it is a development this sum has to name.
      chain.inclusion.facts.size +
      // The rationals and the cuts, 2026-09-27, in the change that collected them. Both were links
      // of the chain from phase 5 of `docs/adr/0007` and in no library, which this sum could not
      // see: it counts what `Library.of` should hold, and nobody had written these two into it.
      chain.fractions.facts.size +
      chain.cuts.facts.size +
      // The list interface, 2026-09-23, added here in the change that added the link rather
      // than after this sum caught it, which is what the four comments above record happening
      // four times.
      chain.listing.facts.size +
      // Its consumer, the same day and the same discipline. `Folding` is a development of its own
      // rather than more of `Listing` because it SPENDS that interface's recursion theorem instead
      // of publishing it, and a development of its own is one this sum has to name.
      chain.folding.facts.size +
      // The square root, 2026-09-24, in the change that added the link, and a development of its
      // own for the reason `Root`'s docstring gives: it is neither a limit nor a transcendental
      // function.
      chain.root.facts.size +
      // Continuity, the same day, in the change that added the link: neither a limit, which is
      // about a sequence, nor anything `Root` is about.
      chain.continuity.facts.size +
      // The logarithm, the same day and the same discipline.
      chain.logarithm.facts.size +
      // Resolution, 2026-09-25, in the change that made it a link: its five soundness theorems
      // were in no library while it sat beside the chain, and its seven over the names are new.
      chain.resolving.facts.size +
      // The derivative and Rolle's theorem, the same day, in the change that added the link.
      chain.derivative.facts.size +
      // The gauge integral, the same day. Added after this sum caught it, which is the sixth time
      // the comments here record: the link was in `Library.of` and its first full run went red.
      chain.integral.facts.size +
      // pi, the periods and acos, 2026-09-27, in the change that added the link.
      chain.circle.facts.size +
      // The complex numbers, 2026-10-05, in the change that added the link.
      chain.complex.facts.size +
      // Finite distributions and Blackwell's easy direction, 2026-10-22, in the change that added
      // the link, and added before the run rather than after it caught the sum.
      chain.decision.facts.size

    library.entries.size shouldBe expected

    // 138 until 2026-09-12, then 186 when the five developments beside the chain were threaded
    // into it, and it moved four times more the same day: the naturals got a power, `Modular` got
    // the quotient, the remainder, Bezout and Euclid, the two halves of a doubled range followed,
    // and `Matrix` arrived with twenty-four.
    //
    // **The pair below was MEASURED on the fused tree at each of those steps, never obtained
    // by adding a branch's own arithmetic to the previous figure.** It has been wrong three times
    // by being computed that way: 193 against 198 against 205 after one merge, 205 against 207
    // after the next, and 207 against 231 after the one that brought the matrices. Every branch
    // was right about itself and no branch was right afterwards, which is the whole of why this
    // comment is here.
    // 233 since `NUM_LT_TRANS` and `SUM_CONGRUENCE_BELOW` arrived on a branch of their own. This
    // is the one delta here that was DERIVED before it was measured and then confirmed by the
    // measurement: two facts, two names neither development already held, so +2 to both figures.
    // 242 since `Classical` was collected, and the delta is DERIVED and then confirmed: eight
    // facts (the excluded middle, the two De Morgans, double negation, `T` is not `F`,
    // extensionality and the two conditional equations) and one definition, `COND`. The eight had
    // been proved and reachable by nothing here since the day each landed, which is a
    // longer-standing absence than any figure in this file has recorded before.
    //
    // Not eleven: the classical AXIOMS stay out, for the reason `RestsOn` records and this file's
    // own comment above repeats. A first attempt added them and `RestsOnSpec` is what said no.
    // 243 since `SUM_CONSTANT`, and the delta is DERIVED before it was measured: one fact, one
    // name no development here already held, so +1 to both figures and to neither of them twice.
    // 246 since `NUM_SUM` and its three facts, and the delta is DERIVED: three facts, three names
    // no development here already held, so +3 to both figures. The DEFINITION of `NUM_SUM` is not
    // a fourth: a definitional entry belongs to the register's table and this library counts the
    // facts, which is why the two documents move by three and by one.
    // 252 since the numerals on `num`, and the delta is DERIVED the same way: SIX facts
    // (`NUM_ONE_SUC`, `NUM_BIT0_ADD`, `NUM_BIT1_SUC` and the three that cross `real_of_num`), six
    // names no development here already held, so +6 to both figures. The three DEFINITIONS that
    // came with them are the register's three and not this library's, which is the same split
    // `NUM_SUM` made and the reason the register moves by three while this moves by six.
    // 255 since `Rotation`, and the delta is DERIVED again and by the same split: THREE facts
    // under three names nothing held, and one definition, `WORD_ROTATE`, which belongs to the
    // register's table. So this moves by three and the register by one on the same change.
    // 256 since `NUM_ARCHIMEDES`, and the delta is DERIVED and is the smallest one there is: ONE
    // fact, under a name nothing held, and no definition, because it names nothing new. So both
    // figures move by one and the register's table does not move at all, which is the split the
    // three notes above describe from the other side.
    // 260 since the floor and the ceiling, and the delta is DERIVED once more: FOUR facts, two per
    // constant, under four names nothing held. The two DEFINITIONS that came with them are the
    // register's and not this library's, which is the same split `NUM_SUM` and `WORD_ROTATE` made.
    // 277 since `Magnitude` joined the chain on 2026-09-13, and the delta is DERIVED and then
    // confirmed: SEVENTEEN facts about `max`, `min`, `abs` and `sgn`, under seventeen names no
    // other development held, so +17 to both figures. Four DEFINITIONS came with them and belong
    // to the register's table rather than here, which is the split `NUM_SUM` and `WORD_ROTATE`
    // made and the reason the register moves by four while this moves by seventeen.
    //
    // That development had been proved and collected by nothing since the day it was written,
    // which is a longer absence than `Classical`'s eight. What made it visible was not a reading
    // of anything: it was a census of `specAll` call sites, grouped by file, which turned up two
    // files holding a `facts` map that `Library.of` does not name. The sum above is what would
    // have caught it had anybody added `Magnitude` to the list; nothing catches a development
    // nobody ever put on either.
    // 278 since `POWER_ONE`, asked for by the collatz repository on 2026-09-13 and checked absent
    // by name, by constant and by shape before it was proved. The delta is the smallest there is
    // and is DERIVED: one fact, one name nothing held, no definition, so both figures move by one
    // and the register's table does not move at all.
    //
    // 282 since `Coding` joined the chain later that day, and the interesting half of that delta is
    // that the development existed for hours before it counted. It was built, proved and green the
    // whole time, and it held `NUM_FACT` and four facts that were in no library and in no document,
    // because nothing assembled it: the same absence `Magnitude`'s seventeen had that morning, and
    // the same one the comment above says nothing catches. Four DERIVED facts under four names
    // nothing held, so both figures move by four; `NUM_FACT` is one DEFINITION and belongs to the
    // register's table, which moves by one while this does not move for it at all.
    // 285 since the finite product and Gauss's lemma, which the beta function's moduli are proved
    // coprime with. Three DERIVED facts under three names nothing held, so both figures move by
    // three; `NUM_PROD` is one DEFINITION and belongs to the register's table, which moves by one
    // while this does not move for it, the same split `NUM_FACT` made an hour earlier.
    // 286 with the bound on a finite stretch of a sequence, the last piece the beta function needs
    // before its moduli. One DERIVED fact under one name, no definition, so both figures move by
    // one and the register's table does not move at all: the smallest delta there is, and the same
    // shape `POWER_ONE` made.
    // 289 with `POWER_MULTIPLICATIVE`, `POWER_NEG_DOUBLE` and `SUM_GEOMETRIC`, from a CONSUMER
    // rather than from a development of this repository: each was being proved by hand downstream
    // for want of the library carrying it, which is the request that produced `SUM_CONGRUENCE` and
    // `POWER_ADD` before them. Three derived facts under three names nothing held, so both figures
    // move by three and the definitional count does not move.
    //
    // THIS LINE HAS NOW BEEN MERGED WRONG IN BOTH OF THE TWO WAYS, an hour apart, by two agents
    // moving one axis from one base. They are not the same failure and the second is the worse.
    //
    // SILENT. The first pair of deltas were both written `282 -> 285`, the same text from the same
    // base, so `git` merged the NUMBERS without a word and raised a conflict only on the prose
    // beside them. The figure would have read 285, looked resolved, and been wrong by three.
    //
    // NOISY, AND WORSE. The second pair wrote DIFFERENT values on this line, 286 against 288, so
    // `git` did raise it. Whoever resolves it is shown two candidates and asked to choose, and
    // BOTH ARE WRONG: the answer is 289 and it is not on the screen. A conflict that presents
    // itself as a choice between two candidates neither of which is the answer is more dangerous
    // than one that never appears, because it closes with the feeling of work done.
    //
    // What caught both was deriving the figure before opening the file, and the order is the whole
    // of it: derive first so a silent merge is audible, then MEASURE, and never one alone.
    // Deriving alone is how the wrong number gets written confidently; measuring alone is how a
    // silent merge survives, because the measurement agrees with whatever the file now says.
    // 290 with `NUM_DIVIDES_ONE`, the converse of `NUM_ONE_DIVIDES` and the atom every coprimality
    // argument reduces to. One DERIVED fact under one name and no definition, so both figures move
    // by one and the register's table does not move.
    // 291 with the moduli's coprimality, which is the fifth of the beta function's six pieces and
    // the first whose statement mentions none of the others: it says what it needs of `b` as a
    // hypothesis rather than naming the factorial that supplies it.
    // 292 with the congruence that descends to a divisor of its modulus, which the Chinese
    // remainder theorem over many moduli needs to read its answer back at each factor.
    // 295 with the three the Chinese remainder theorem over many moduli wants: a product of two
    // positives is positive, each factor divides the product, and a product of a whole family of
    // positives is positive. The first is `Peano`'s, because `NUM_MUL` and `NUM_LT` are both its
    // and nothing had needed a statement about the two together. That sentence named the third
    // twice and the second not at all until 2026-09-14, which is what a list written from memory
    // rather than from the three names looks like.
    // 298 with the Chinese remainder theorem over many moduli itself and the two coprimality
    // lemmas it stands on: coprime to each factor is coprime to the product, once for a pair and
    // once for a family. All three DERIVED, none a definition, so both figures move by three and
    // the register's table does not move.
    // 303 with the beta function and the four lemmas under it, and the delta was DERIVED WRONG in
    // one half, which is worth more here than the number. Five facts and one definition were
    // added, so the derivation said 304 entries and SEVEN definitional ones. The measurement says
    // 303 and six.
    //
    // The definition is `NUM_BETA` and it is not here, and neither is `NUM_GCD`, `NUM_DIVIDES`,
    // `NUM_FACT` or any of the sixty-odd others: `Library.of` collects `definitions` from
    // `Classical` and `Real` ALONE. The six are those two developments' and nothing else's. Every
    // defined constant is tracked, in `docs/reading-register.md`, which went from 69 rows to 70 on
    // this same change; that is the document for constants and this is the library for lemmas.
    //
    // The derivation read the words "definitional entries" and answered for defined constants,
    // which is `ProposeSpec`'s recorded mistake about `aboutNumbers` one day later and on another
    // bucket: **the criterion is the collection, not the name of the count.** It is written here
    // rather than there because this is the count that has it.
    // 311 with the arithmetisation's first slice, and this time the delta was derived in full and
    // came out right, INCLUDING the definitional entries, which do not move: `NUM_TRI` and
    // `NUM_PAIR` are two more defined constants and the paragraph above says why that figure stays
    // at six. `docs/reading-register.md` is where they show, going from 70 rows to 72.
    // 315 with the constructor `NUM_CODE` and its four facts: injective, both components strictly
    // below it, and never zero. One more defined constant and the definitional figure stays at six
    // for the third time, which is the paragraph above rather than a coincidence.
    // 322 with the term predicate of the embedded theory: the recursion equation, five
    // introduction rules and the refusal at zero. `NUM_TERM` is a fifth defined constant and the
    // definitional figure stays at six for the fourth time.
    // 328 with the formula predicate beside the term one: its recursion equation, four
    // introduction rules and the refusal at zero. `NUM_FORM` is a sixth defined constant and the
    // definitional figure stays at six for the fifth time.
    // 332 with the object language's numerals: two recurrences, that every one is a term, and
    // that distinct numbers get distinct ones. The definitional figure stays at six for the sixth
    // time with a seventh defined constant.
    // 336 with the four projections of the coding, and this is the addition that moves the OTHER
    // document furthest: four defined constants at once take `docs/reading-register.md` from 76
    // rows to 80, while the definitional figure here stays at six for the seventh time. The two
    // counts are about different populations and this change shows the gap widening.
    // 341 with the substitution, the first FUNCTION over codes this development has: its five
    // equations, one per tag the terms use.
    // 345 with the substitution on formulas, which completes the pair. The renaming of
    // `NUM_SUBST` to `NUM_SUBST_TERM` that came with it moves nothing here, because a rename is
    // not an addition and this count is of entries rather than of characters.
    // 346 with course-of-values induction, and it is the first addition in a while that moves
    // ONLY this figure: it declares no constant, so the register does not move, and it binds one
    // variable which is a predicate, so neither of `CLAUDE.md`'s two figures moves either.
    // 347 with substitution keeping a term a term, which is course-of-values induction's first
    // consumer and the reason it was derived one commit earlier.
    // 348 with the same for formulas, which is what the induction scheme of PA needs before it
    // can be stated: every instance of it is a formula built by substituting into another.
    // 356 with the axioms of PA, eight at once, which is the largest single addition here and the
    // only one whose facts cost no axiom: membership in the axiom set is settled by unfolding a
    // disjunction. It moves `CLAUDE.md`'s two figures by exactly one each, because of the eight
    // only `NUM_PA_INDUCTION` binds two variables of a kind, and it moves the register by one row
    // while the definitional figure stays at six for the eighth consecutive time.
    // 357 with every axiom being a formula, which declares no constant and binds one variable, so
    // it is the rarest kind of addition here: it moves this figure and nothing else at all. The
    // register does not move and neither of `CLAUDE.md`'s two do.
    // 366 with freeness on terms and on formulas, nine clause equations and two constants. Its two
    // `CLAUDE.md` figures were derived as nine and measured as EIGHT: `NUM_FREE_TERM_ZERO` binds the
    // index alone, since its code has no parts, and every other clause here binds the index and at
    // least one component beside it. A count of lemmas and a count of binders do not move together
    // and this is the change that shows it by one.
    // 377 with the logical axioms: eight schemes, the two equations that characterise them and
    // `NUM_CLOSED`, and every axiom being a formula. Its two `CLAUDE.md` figures move by SEVEN, and
    // this time that was derived rather than found: of the eleven, `NUM_LOGIC_REFLEXIVE` binds one
    // variable because its scheme has one hole, and the three equations bind one each.
    // 382 with `Provability`, the twenty-first link and the first that is about the language
    // rather than in it. Five facts and three constants, and only two of the five bind more than
    // one variable, which is why `CLAUDE.md`'s two figures move by two where the library moves by
    // five: three of them are about a single subject.
    // 384 with the shift lemma and the strict monotonicity of addition it rests on, which is the
    // first thing `Provability` has needed from `Peano` that was not there.
    // 386 with the two order facts the concatenation of two derivations needs: that the strict
    // order excludes the other one, which is what makes a case split on them a split, and that a
    // summand is at most its sum. Both are general and neither has a consumer in the chain yet.
    // 388 with the closure of `NUM_PROV` under modus ponens and the cancellation of a summand out
    // of a comparison that it needed. Its two `CLAUDE.md` figures move by two, which is both of
    // them: one binds three variables of a kind and the other binds two. The second was not in the
    // plan for the first. `NUM_ADD_CANCEL_LEFT` cancels a summand out of an EQUATION and nothing
    // cancelled one out of an order, which only showed when the derivation reached for it.
    // 389 with the closure under generalisation, the other rule of the embedded theory's Hilbert
    // system. One fact and no constant, and it moves both of `CLAUDE.md`'s figures because it
    // binds an index and a formula, two of a kind.
    // 391 with `Deduction`, the twenty-third link and the first whose product is derivations of
    // the embedded theory rather than definitions of it. Two facts and no constant, so the register
    // does not move; `CLAUDE.md`'s two figures move by ONE each and not by two, because the
    // identity binds a single formula and only the syllogism binds three of a kind.
    // 393 with Euclid's theorem and the lemma it needed, `NUM_PRIME_FACTOR`, which the library
    // turned out not to have: `NUM_PRIME_DIVISOR` is a letter away and says the other direction.
    // Neither of `CLAUDE.md`'s figures moves, because both bind a single variable, which this file
    // has called the rarest kind of addition twice before and is the third time.
    // 396 with the three multiplicative lemmas the irrationality of the square root of two needed
    // and `Peano` did not have, though it had all three additive counterparts. Each binds three
    // variables of a kind, so both of `CLAUDE.md`'s figures move by three as well.
    // 398 with two being prime and with no square being twice a square, which is the arithmetic
    // content of the irrationality of the square root of two. `CLAUDE.md`'s two figures move by
    // ONE each, not two: `NUM_PRIME_TWO` binds nothing at all, being a claim about one number.
    // 401 with the three rules the deduction theorem needs: weakening under a hypothesis, modus
    // ponens under one, and generalisation under one. Each binds two or three variables of a kind,
    // so both of `CLAUDE.md`'s figures move by three as well.
    // 404 with the deduction theorem and the two definitions it needed. It is the first addition
    // in a while to DECLARE anything: `NUM_STEP_FROM` and `NUM_PROV_FROM` are constants, so the
    // reading register moves by two rows where nothing else recently has. The definitional figure
    // below does NOT move, and the reason is worth knowing: `Library.of` collects each
    // development's `facts` and not its `definitions`, so a constant defined in `Provability`
    // reaches the register and not the library.
    // 416 with the first analysis: five facts about `converges` and `lim`, and seven about the six
    // transcendental constants. Both of `CLAUDE.md`'s figures move by three and by two rather than
    // by twelve, which is the measurement rather than a guess: most of the twelve bind one variable
    // or none, `exp 0 = 1` binding nothing at all. The definitional figure does not move for the
    // reason four paragraphs up: `Library.of` collects `facts` and not `definitions`, so the six
    // new constants reach the reading register and not this count.
    // 417 with the closure of the numerals, which is one fact and is the first thing the library
    // says is closed at all. Neither of `CLAUDE.md`'s figures moves: it binds a single variable,
    // which this file has called the rarest kind of addition and is now the fourth time.
    // 418 with specialisation as a rule of the embedded theory rather than a scheme about it.
    // Both of `CLAUDE.md`'s figures move by one, which is the ordinary case for this development:
    // it binds an index, a term and a formula, three of a kind.
    // 419 with the idleness of the substitution, which is one fact and the first thing anywhere
    // to say when a substitution does NOT move. Both of `CLAUDE.md`'s figures move by one: it
    // binds an index, a replacement and a subject, three of a kind.
    // 424 with the monotone convergence theorem: `NOT_FORALL` in `Classical`, the two negated
    // comparisons in `Order`, and `MONOTONE_LE` with `MONOTONE_CONVERGES` here. Both of
    // `CLAUDE.md`'s figures move by TWO and not by five, and which two is the content: only the
    // pair in `Order` carries two leading quantifiers, and both of theirs are reals.
    //
    // **That last figure was written three times before it was right, and never because the five
    // were miscounted.** It was derived as 422, then 423, then 424, each time by adding five to
    // the figure a file was carrying: first to another session's uncommitted edit of this one,
    // then to a line this session had itself rebased onto the wrong predecessor. Every one of the
    // three was right about the tree it was taken on, which is what makes the failure quiet. The
    // baseline on a shared checkout is `git show HEAD:<path>` and nothing else: the number in the
    // working tree can be somebody else's prediction, or your own.
    // 427 with the three rules of the embedded theory's equality, symmetry, transitivity and the
    // congruence of the successor. `Language` has said since it was written that two equality
    // axioms suffice because those three are consequences; they are derived rather than asserted
    // now. Both of `CLAUDE.md`'s figures move by three, since each binds two or three terms.
    // 434 with PA proving its own addition on numerals and the six facts under it: the four
    // closure introduction rules, which are what a compound closed term needs, and PA's two
    // addition axioms at closed terms rather than at variables. `CLAUDE.md`'s two figures move by
    // FOUR rather than by seven, which was derived: three of the seven bind one variable or none.
    // 436 with the two lemmas of the `prime-power-cancellation` branch, which had fallen 24
    // commits behind and was recovered on 2026-09-15: the power's positivity and the cancellation
    // of a prime power. Both of `CLAUDE.md`'s figures move by two, one binding two variables and
    // the other four, all of the same type.
    // 454 with `Concatenation`'s fifteen and the three facts about `num` that had to be proved in
    // front of them, `NUM_ADD_LT_CANCEL`, `NUM_LE_OF_NOT_LT` and `NUM_SUB_SUB`. `CLAUDE.md`'s two
    // figures both move by **twelve**, which is the first delta here where the two move together
    // and all the way: twelve of the eighteen have two or more leading quantifiers, and every one
    // of those twelve has two of one type, because a claim about a concatenation binds two words
    // and a claim about an index binds a pair of numbers. The six that move neither are the ones
    // binding one variable or none: the two unit laws, the empty word's length, the two singleton
    // laws, and the induction, whose single leading binder is the predicate.
    //
    // Derived by hand from `docs/lemmas.md` and compared against what this suite computed, in that
    // order, which is the check the paragraph above says was skipped three times.
    // 462 with `Inductive` and `Reaching`, eight facts under eight new names: the least fixed
    // point of a monotone operator with its induction principle, introduction rules and fixpoint
    // equation, and over them the counted reachability of a relation with its own induction
    // principle and the potential-function lemma.
    //
    // **This one arrived as a conflict offering 454 and 444, and neither was right.** Two branches
    // moved the same pinned count from the same base, which is the shape this repository has now
    // paid for three times: where the two write the same number git merges it silently, and where
    // they write different ones it shows two candidates and closes with the feeling of having done
    // the work. The operation is addition -- 436 at the shared base, plus eighteen, plus eight --
    // and picking a side is never it. Derived from the base and the two addends before this file
    // was opened, and then measured.
    //
    // `CLAUDE.md`'s two figures move by six and by five, which is the first delta here where they
    // move by different amounts in the same change: of the eight, `INDUCTIVE_INDUCT` and all five
    // `REACH` facts have two or more leading binders, and only the five have two of one type,
    // because every `REACH` statement binds the relation and its counted sub-relation at
    // `'a -> 'a -> bool` while `INDUCTIVE_INDUCT` binds an operator and a set, which differ.
    //
    // **463 with `SUM_COMPARISON`, and this row was missing for the length of one card.** The
    // count was moved and the derivation was not written, in the file whose whole purpose is that
    // the derivation exists: the assertion below read 463 while the rows above it stopped at 462,
    // so the arithmetic that is supposed to reach the figure reached one less than it. A peer
    // reading the two together is what found it. It is worth more than the missing sentence,
    // because a pin whose derivation is absent looks exactly like a pin whose derivation is right,
    // and the check this file performs is the derivation and not the number. `CLAUDE.md`'s two
    // figures both moved by one: the comparison test binds `f` and `g`, which is two leading
    // quantifiers, and they are both `num -> real`, which is two of one type.
    //
    // 465 with `CONVERGES_ADD` and `CONVERGES_NEG`, the additive half of the algebra of limits,
    // which is what `Limit` had none of: of its eight facts before these, not one related two
    // convergent sequences to each other. `CLAUDE.md`'s two figures move by **two and by one**,
    // and the split is the whole reason to write the row rather than the delta. Both new
    // statements have two or more leading quantifiers, so the first moves by two. Only the sum has
    // two of one type, twice over: `s` and `t` are both `num -> real` and `a` and `b` are both
    // `real`. The negation binds `s` at `num -> real` and `a` at `real` and shares nothing, which
    // makes it the rarer case this figure exists to count -- a lemma whose binders cannot be
    // silently transposed, because the kernel's own typing refuses it.
    // 477 with the object language's six derived connectives: twelve facts under twelve new
    // names, six defining equations and six well-formedness rules, one of each per constant.
    // **The six DEFINITIONS are not in this count and that is the thing to get right here**, since
    // it is what a reader adding a constant to `Language` will assume. `Library.of` collects
    // `chain.language.facts` and not `chain.language.definitions`; the only developments whose
    // definitions it collects are `Classical` and `Real`, which is why the definitional entries
    // below do not move and why the whole delta lands on the facts. Derived from that reading of
    // `Library.of` and from the twelve names, before this suite was run.
    //
    // `CLAUDE.md`'s two figures move by **twelve**, both of them and all the way, which has
    // happened once before, when `Concatenation` landed. Every one of the twelve binds two or more
    // leading variables and every one of those binds them all at `num`: a claim about a code is a
    // claim about numbers, so there is no binder here of any other type to break the run.
    //
    // **This entry was first written against a base of 463 and is 465 plus twelve, not 475.** Two
    // lemmas landed underneath it while the work was in flight. The addend is the thing this ledger
    // records and it did not change; what changed is what it is added to, which is why a rebase
    // takes the base in one piece and re-derives rather than choosing between two numbers.
    //
    // 489 with the twelve clauses under those same six constants: where an index occurs free in
    // each, and what a substitution does to it. **The addend is the same twelve as the row above
    // and the reason is different, which is the thing to read rather than the arithmetic.** That
    // row added facts because six constants arrived; this one adds none, and the twelve are facts
    // about constants the library already held. So the definitional entries do not move here for a
    // second reason on top of the first: there is no new definition at all, not merely none that
    // `Library.of` collects. Derived from the twelve names before this suite was run, and the
    // suite returned 489, 486, 480 and 6.
    //
    // `CLAUDE.md`'s two figures move by **twelve** again and for the reason they did then: every
    // one of the twelve binds three or more leading variables and every one of those is a `num`.
    //
    // 493 with the right forward closure: `Forward`'s four, which are the three introduction rules
    // of `RFC(R)` and its induction principle. Two constants arrive with them, `WORD_STEP` and
    // `WORD_RFC`, and **neither moves the definitional entries**, for the reason two rows above:
    // `Library.of` collects a development's `facts` and takes `definitions` only from `Classical`
    // and `Real`. Derived from the four names before this suite was run.
    //
    // `CLAUDE.md`'s two figures move by **four and by three**, and the one that does not move is
    // the one worth reading. All four bind two or more leading variables, so the first figure takes
    // all of them. `WORD_RFC_INDUCT` binds the system and the carrier, `word('a)->word('a)->bool`
    // against `word('a)->bool`, which share no type, so it is the second instance in this ledger of
    // a lemma whose binders the kernel's own typing refuses to transpose. The other three bind
    // words throughout and are transposable in exactly the way the figure exists to count.
    //
    // 494 with `NUM_SUM_SPLIT`, a sum over a range split at a point. **ONE**, derived before the
    // run: it is a single equation and the developments around it do not move. What it is for is
    // not arithmetic at all -- a word is a concatenation, so a tally over the positions of
    // `WORD_CONCAT x y` is this lemma at `m = WORD_LENGTH x`, and the real-valued `Sum` has had
    // the same fact as `SUM_REINDEX` since it existed while `NUM_SUM` had three facts and no way
    // to be split.
    //
    // `CLAUDE.md`'s two figures move by **one and by one**. It binds `f` at `num -> num` and `m`
    // and `n` at `num`, so it has two or more leading quantifiers, and `m` and `n` are two of one
    // type. Derived before the run from the statement rather than read off it afterwards.
    //
    // 495 with `WORD_CONCAT_TALLY`, a tally over the positions of a word split where the word is.
    // **ONE**, derived before the run. It is the consumer `NUM_SUM_SPLIT` was added for one row
    // above, and the pair is the shape to expect whenever a fact about `num` is added so that a
    // fact about `word` can be stated: two entries, in two developments, one session apart.
    //
    // `CLAUDE.md`'s two figures move by **one and by one**. It binds `f` at `num -> 'a -> num` and
    // `u` and `v` at `word('a)`, so it has two or more leading quantifiers and two of one type --
    // and the two of one type are the two halves of a concatenation, which is exactly the pair a
    // positional specialisation would silently swap, giving the tally of the other half.
    //
    // 500 with the fundamental theorem of arithmetic: `NUM_PROD_CONG` in `Coding`, and
    // `NUM_PRIME_DIVIDES_PROD`, `NUM_PRIME_PROD_ONE`, `NUM_FACTORISATION` and
    // `NUM_FACTORISATION_UNIQUE` in `Primes`. **FIVE**, derived from the five names before the run.
    // No constant arrives with them, which is the whole shape of the work: a factorisation is a
    // family and a length, so the existence and the uniqueness are written with `NUM_PROD` and
    // nothing new had to be declared to say them.
    //
    // `CLAUDE.md`'s two figures move by **four and by three**, and the one that moves neither is
    // the theorem itself. `NUM_FACTORISATION` binds **one** leading universal, `!n`, and everything
    // else in it is existential, so it is outside the first figure's population altogether; a
    // reader expecting the headline result to be the one that counts has it backwards.
    // `NUM_PRIME_PROD_ONE` is in the first figure and not the second: it binds `f` at `num -> num`
    // and `k` at `num`, which is two leading quantifiers and no two alike. The other three are in
    // both, and `NUM_FACTORISATION_UNIQUE` is the sharpest instance the second figure has, since it
    // binds two families and two lengths alternately: a positional specialisation that swapped
    // either pair would compare one factorisation with itself and prove nothing.
    //
    // 502 with the two bounds on where a limit sits, `CONVERGES_LE` and `CONVERGES_GE`. **TWO**,
    // derived before the run: two derived facts under two names nothing held and no constant, so
    // the register does not move and the definitional figure stays at six.
    //
    // `CLAUDE.md`'s two figures move by **two and by two**, derived from the statements rather than
    // read off the run. Each binds `s` at `num -> real`, `l` and `b` at `real` and `N` at `num`, so
    // both have two or more leading quantifiers, and in both the two reals are alike AND adjacent:
    // the narrow reading and the broad one agree here, as that paragraph in `CLAUDE.md` says they
    // have so far.
    //
    // 503 with `WORD_LENGTH_ZERO`, a word of no letters being the empty word. **ONE**, derived
    // before the run. It was derived inside the base case of `WORD_INDUCTION` from the day that
    // landed and is published now because a second consumer arrived: a step of a rewriting system
    // splits a word into a context, a left-hand side and a tail, and the branch where the tail is
    // absent needs a length of zero turned back into `WORD_EMPTY`. It binds ONE leading quantifier,
    // so neither of `CLAUDE.md`'s two figures moves.
    //
    // **This line is the tip plus this branch's one, and it has been rebased four times tonight
    // onto four different bases.** Twice git offered two numbers of which neither was right,
    // because two branches had moved the same quantity from the same base. The operation is always
    // addition and picking a side is never it -- it only sometimes agrees, which is how a wrong
    // rule earns confidence. The safe form is to take whatever the tip now says and add this
    // branch's delta, never to carry forward a total computed against an earlier one.
    // 511 and 508 with the four `Deduction` facts that put PA's multiplication to work and prove
    // it on numerals. Tip plus this branch's delta, which is what the paragraph above insists on:
    // four entries, four names, none of them shared with another development.
    // 552 and 549 with the integers, 2026-09-18: forty-one facts under forty-one names, none of
    // them shared with another development, which is the whole of the delta and is what the
    // paragraph above insists a number here is. Tip plus this branch's delta, never a total carried
    // forward against an earlier base. The gap between the two figures does not move, three names
    // being held by two developments apiece since long before this.
    // 560 and 557 with the bridge into the reals, the same day: eight facts under eight names,
    // none of them shared with another development, so the gap between the two figures does not
    // move either. Tip plus this branch's delta, which is what the paragraph above insists a
    // number here is, and the delta is checkable against `docs/lemmas.md`'s new section by eye.
    // 562 and 559 with the order map, the same day: two facts under two names, `NUM_REAL_LE_BACK`
    // in `Peano` and `INT_REAL_LE` in `Inclusion`, neither shared with another development, so the
    // gap between the two figures does not move. Tip plus this branch's delta. Two and not one
    // because the biconditional at `int` needs both directions at `num` and the library held the
    // outward one alone.
    // 564 and 561 with the embedding's divisibility, 2026-09-19: two facts under two names,
    // `INT_DIVIDES_OF_NUM` and `INT_TWO_NOT_DIVIDES_ONE`, both in `Integer` and neither shared
    // with another development, so the gap between the two figures does not move. Tip plus this
    // branch's delta, which is what the paragraph above insists a number here is. One of the two
    // binds two leading quantifiers of one type and the other binds none, so exactly one of
    // `CLAUDE.md`'s two figures-per-lemma moves by one and both move by one in total.
    // 565 and 562 with the dominating series for the exponential, 2026-09-20: one fact under one
    // name, `NUM_POW_LE_FACT` in `Coding`, not shared with another development, so the gap between
    // the two figures does not move. Tip plus this branch's delta. It binds ONE leading quantifier,
    // so neither of `CLAUDE.md`'s two figures-per-lemma moves and only the library's own total does,
    // which is the case the line above describes from the other side.
    // 566 and 563 with `exp 1 > 2`, the same day: one fact under one name,
    // `EXP_ONE_ABOVE_TWO` in `Transcendental`, not shared with another development, so the gap
    // between the two figures does not move. Tip plus this branch's delta. It binds nothing at
    // all, being a claim about two constants, so neither figure-per-lemma in `CLAUDE.md` moves.
    // 569 and 566 with the three facts about `abs` that landed on 2026-09-20 for the Cauchy
    // product's sake: `ABS_OF_NONNEG`, `ABS_OF_NONPOS` and `ABS_MUL`, all in `Magnitude`, none
    // shared with another development, so the gap between the two figures does not move. Tip plus
    // this branch's delta. **Only `ABS_MUL` binds two leading quantifiers**, and they are both
    // reals, so `CLAUDE.md`'s two figures-per-lemma each move by one where the library moves by
    // three: the two conditional ones bind a single variable.
    // 570 and 567 with `INT_MUL_CANCEL_NUM`, 2026-09-20: one fact under one name, in `Integer`,
    // not shared with another development, so the gap does not move. Tip plus this branch's delta.
    // It binds three leading quantifiers of which the first two are both `int`, so **both** of
    // `CLAUDE.md`'s figures-per-lemma move by one where the three `abs` facts of the same day
    // moved them by one between them.
    // 571 and 568 with `CONVERGES_MUL`, the same day: one fact under one name, in `Limit`, not
    // shared with another development, so the gap of three does not move. Tip plus this branch's
    // delta. Its four leading quantifiers are two sequences and two reals, so it has two alike
    // and both of `CLAUDE.md`'s figures-per-lemma move by one, as the entry above did.
    // 577 and 574 with the Cauchy product's finite half, 2026-09-20: SIX facts under six names,
    // two in `Peano` and four in `Series`, none shared with another development, so the gap of
    // three does not move. Tip plus this branch's delta. `CLAUDE.md`'s two figures-per-lemma move
    // by five and by two, and both were derived from the statements before the run: of the six,
    // `NUM_SUC_SUB_SELF` binds one leading quantifier and the other five bind two or more, and of
    // those five only `NUM_SUC_SUB` (two `num`) and `SUM_OF_PRODUCTS` (two `num -> real`) bind two
    // that share a type.
    // 580 and 577 with the binomial coefficients, 2026-09-20: three facts under three names, all
    // in `Peano`, none shared with another development, so the gap of three does not move. Tip
    // plus this branch's delta. `CLAUDE.md`'s two figures-per-lemma each move by **one**, derived
    // from the statements before the run: `NUM_CHOOSE_ZERO` and `NUM_CHOOSE_EMPTY` bind a single
    // leading quantifier each, and only `NUM_CHOOSE_SUC` binds two, which are both `num`.
    // 582 and 579 with the two facts the binomial theorem asks for in front of it, 2026-09-21:
    // `NUM_CHOOSE_ABOVE` and `NUM_LE_OF_LT_SUC`, both in `Peano`, neither shared, so the gap of
    // three does not move. Tip plus this branch's delta. Each binds two leading quantifiers and
    // both of each pair are `num`, so `CLAUDE.md`'s two figures-per-lemma move by **two** each,
    // derived from the statements before the run.
    // 583 and 580 with the binomial theorem itself, 2026-09-21: one fact under one name, in
    // `Series`, not shared with another development, so the gap of three does not move. Tip plus
    // this branch's delta. It binds three leading quantifiers of which the first two are both
    // `real`, so **both** of `CLAUDE.md`'s figures-per-lemma move by one.
    // 584 and 581 with the absolute convergence theorem, 2026-09-21: one fact under one name, in
    // `Limit`, not shared, so the gap of three does not move. Tip plus this branch's delta. It
    // binds two leading quantifiers and they are a **sequence** and a real, so `CLAUDE.md`'s
    // first figure moves by one and its second does not move at all — the first entry today
    // whose two figures part company, and both were derived from the statement before the run.
    // 586 and 583 with the Cauchy product's partial sum and its gap, 2026-09-21: two facts under
    // two names, both in `Series`, neither shared, so the gap of three does not move. Tip plus
    // this branch's delta. Each binds three leading quantifiers of which the first two are both
    // `num -> real`, so **both** of `CLAUDE.md`'s figures-per-lemma move by two.
    // 588 and 585 with the two tail facts, 2026-09-21: two facts under two names, both in
    // `Limit`, neither shared, so the gap of three does not move. Tip plus this branch's delta.
    // Each binds two leading quantifiers, a **sequence** and a real, so they do not share a type
    // and `CLAUDE.md`'s first figure moves by two while its second does not move at all.
    // 589 and 586 with the bounded monotone, 2026-09-21: one fact under one name, in `Series`,
    // not shared, so the gap of three does not move. Tip plus this branch's delta. It binds three
    // leading quantifiers of which the first two are both `num -> real`, so **both** of
    // `CLAUDE.md`'s figures-per-lemma move by one.
    // 593 and 590 with the sandwich and what it wanted in front of it, 2026-09-21: four facts
    // under four names, three in `Limit` and one in `Peano`, none shared, so the gap of three
    // does not move. Tip plus this branch's delta. `CLAUDE.md`'s two figures move by **three**
    // and not four, derived before the run: `SUM_GROWS` binds a single leading quantifier, and
    // each of the other three binds two that share a type.
    // 594 and 591 with the Cauchy product, 2026-09-21: one fact under one name, not shared, so
    // the gap of three does not move. Tip plus this branch's delta. `CLAUDE.md`'s two figures
    // move by **one** each, derived before the run: it binds four leading quantifiers and two
    // pairs of those share a type, and that row counts a lemma once however many pairs it has.
    // 598 and 595 with the general Cauchy product and the three lemmas under it, 2026-09-21:
    // four facts under four names, none shared, so the gap of three does not move. Tip plus
    // this branch's delta. `CLAUDE.md`'s two figures move by **four** and **three**, derived
    // before the run and met: all four bind two or more leading quantifiers, and `SUM_ABS`
    // binds `num -> real` then `num`, which is the one of the four with no pair sharing a type.
    // 599 and 596 with `ABS_POWER_LE`, 2026-09-21. One fact, one name, not shared.
    // 602 and 599 with the exponential's absolute convergence and the two lemmas under it,
    // 2026-09-21. `CLAUDE.md`'s two figures move by **two** and **zero**: the halving and the
    // geometric tail each bind `real` then `num`, and the convergence binds one quantifier.
    // 604 and 601 with the triangle's diagonal and the binomial coefficient against the three
    // factorials, 2026-09-21. `CLAUDE.md`'s two figures move by **one** each: the diagonal binds
    // a single quantifier, and the factorial identity binds two that share `num`.
    // 607 and 604 with the addition theorem and the two facts under it, 2026-09-21. All three
    // bind two or more leading quantifiers and all three have a pair sharing `real`, so both of
    // `CLAUDE.md`'s figures move by three.
    // 609 and 606 with the exponential's reciprocal and the hyperbolic identity. Neither moves
    // `CLAUDE.md`'s figures: both bind a single leading quantifier.
    // 617 and 614 with the list interface, 2026-09-23. Eight facts under eight names, none shared,
    // so the gap of three does not move. `CLAUDE.md`'s two figures move by **six** and **one**:
    // six of the eight bind two or more leading quantifiers, and of those only `LIST_CASES`'s
    // sibling `LIST_CONS_INJECTIVE` binds a pair sharing a type, `'a` with `'a` and
    // `word('a)` with `word('a)`.
    // 622 and 619 with the structural recursion theorem and the fold, 2026-09-23. Five facts under
    // five names, none shared, so the gap of three does not move. `CLAUDE.md`'s two figures move by
    // **five** and **two**, derived before the run and met: all five bind two or more leading
    // quantifiers, and the two with a pair sharing a type are `LIST_RECURSION_UNIQUE`, whose `f`
    // and `h` are both `word('a) -> 'b`, and `LIST_FOLD_CONCAT`, whose `u` and `v` are both
    // `word('a)`. The other three bind a step, a start and at most one word between them.
    // 628 and 625 with the square root, 2026-09-24. Six facts under six names, none shared, so the
    // gap of three does not move. `CLAUDE.md`'s two figures move by **one** and **one**: of the six
    // only `SQRT_UNIQUE` binds two leading quantifiers, and its `x` and `y` are both `real`; the
    // existence, the read-back and the square bind one and the two values none. Derived from the
    // statements after the first run had named the figures, and it agrees with them.
    // 629 and 626 with the irrationality of the root of two, the same day. One fact under one name,
    // and `CLAUDE.md`'s two figures move by one each: it binds `p` and `q`, both `num`. Derived
    // after the run had named the figures, and it agrees with them.
    // 634 and 631 with the trigonometric identity, the same day. Five facts under five names, none
    // shared: `CONVERGES_SHIFT`, `SUM_EVEN_ODD`, and `COS_ABSOLUTE`, `SIN_ABSOLUTE` and
    // `SIN_COS_SQUARED`. `CLAUDE.md`'s two figures move by **two** and **none**: only the first two
    // bind two leading quantifiers, a sequence and a number, and the other three bind one `x`.
    // Derived after the run had named the figures, and it agrees with them.
    // 637 and 634 with continuity, the same day, derived before the run and met. Three facts
    // under three names, none shared. `CLAUDE.md`'s figures move by **one** and **one** twice:
    // `CONTINUOUS_CONST` binds `c` and `x`, both `real`, and `INTERMEDIATE_VALUE` binds `f`, `a`,
    // `b` and `y`, three of them `real`; `CONTINUOUS_ID` binds one.
    // 649 and 646 with the logarithm, the same day, derived before the run and met: twelve facts
    // under twelve names, none shared. `CLAUDE.md`'s figures move by **three** and **three**:
    // `EXP_LT_MONOTONE`, `EXP_INJECTIVE` and `LN_MUL` each bind two reals, and the other nine
    // bind one or none.
    // 654 and 651 with the extreme value theorem, 2026-09-25, derived before the run: five facts
    // under five names, none shared. `CLAUDE.md`'s figures move by **five** and **four**: all five
    // bind two or more leading quantifiers, and all but `CONTINUOUS_NEG`, whose `f` and `x` differ
    // in type, bind two reals among them.
    // 667 and 664 with the convergence criteria, 2026-09-25, derived before the run and met:
    // ten facts in `Limit` and three in `Transcendental`, thirteen names none of them shared, and
    // `diverges` is a definition, which is the register's rather than this count's. `CLAUDE.md`'s
    // figures move by **seven** and **one**: seven of the thirteen bind two or more leading
    // quantifiers, and only `SUM_SCALE_CONVERGES` binds two of one type, its `c` and its `l`.
    // 679 and 676 with `Truth`, the same day, derived as that base plus this delta before the run:
    // twelve facts under twelve names, none shared. `CLAUDE.md`'s figures move by **nine** and
    // **five**: every clause but `NUM_VALUE_ZERO` binds the environment and at least one code,
    // which is the nine, and the five are the ones binding two codes, `a` and `b` or `p` and `q`
    // or `j` and `p`; the environment is `num -> num` and shares its type with nothing.
    // 685 and 682 with the polynomial-times-geometric criteria, 2026-09-25, derived as that base
    // plus this delta before the run: six facts under six names, none shared. `CLAUDE.md`'s figures
    // move by **three** and **none**: `CONVERGES_BOUNDED` and the two polynomial facts bind two
    // leading quantifiers each, of different types, and the other three bind one.
    // 691 and 688 with resolution as a link, the same day: twelve facts under twelve names, none
    // shared, so the gap of three does not move. Tip plus this branch's delta. `CLAUDE.md`'s figures
    // move by **eleven** and **nine**, derived from the twelve statements before the run and not
    // measured by it: every one but `RES_WIDTH_ZERO` binds two or more leading quantifiers, and the
    // three with no pair of one type are that one, `RES_WIDTH_SUC` and `RES_WIDTH_ATTAINED`, which
    // bind a length function and a number. The other nine each bind two numbers, or two
    // `num -> bool`.
    // 703 and 700 with the derivative and Rolle's theorem, the same day, derived before the run:
    // six facts under six names, none shared. `CLAUDE.md`'s figures move by **five** and **five**:
    // every fact but `DERIVATIVE_ID`, which binds one `x`, binds two or more, and each of those five
    // binds two reals among them. Tip plus this branch's delta.
    // 709 and 706 with the closed terms, the same day, tip plus this delta, derived before the
    // run: six facts under six names, none shared, four in `Deduction` and two in `Truth`. `CLAUDE.md`'s figures move by
    // **five** and **four**: the three new congruences bind `t`, `u` and `w`, all codes;
    // `NUM_PROV_TRUE_EQ` binds the environment and two codes; `NUM_PROV_VALUE` binds the
    // environment and one code, which share no type; `NUM_PROV_REFL` binds one.
    // 713 and 710 with the mean value theorem, the same day, derived before the run: four facts
    // under four names, none shared, `CONTINUOUS_LINEAR` in `Continuity` and three in `Derivative`.
    // `CLAUDE.md`'s figures move by **four** and **four**: each binds two functions, or two reals,
    // among two or more leading quantifiers. Tip plus this branch's delta.
    // 715 and 712 with the product rule and the continuity of a differentiable function, the same
    // day, derived before the run: two facts under two names, none shared. `CLAUDE.md`'s figures
    // move by **two** and **two**: `DERIVATIVE_CONTINUOUS` binds `x` and `m`, both real, and
    // `DERIVATIVE_PRODUCT` two functions.
    // 716 and 713 with the chain rule, the same day, derived before the run: one fact under one
    // name. `CLAUDE.md`'s figures move by **one** and **one**: it binds two functions.
    // 718 and 715 with the exponential's slope and the estimate under it, the same day, derived
    // before the run: two facts under two names, none shared. `CLAUDE.md`'s figures do not move:
    // `EXP_NEAR_LINE` binds one `h` and `DERIVATIVE_EXP` one `x`.
    // 721 and 718 with the sign of a derivative on an interval, the same day, derived before the
    // run: three facts under three names, none shared. `CLAUDE.md`'s figures move by **three** and
    // **three**: each binds `f`, `a` and `b` in front, and the two ends are both real.
    // 729 and 726 with Fermat's little theorem, the same day, derived before the run: eight facts in
    // `Primes` under eight names, none shared. `CLAUDE.md`'s figures move by **eight** and
    // **eight**: every one binds two or more leading quantifiers, and every one has two of `num`
    // among them, `NUM_SUM_ADD` two functions instead. Tip plus this branch's delta.
    // 730 and 727 with uniform continuity, the same day, derived before the run: one fact under one
    // name. `CLAUDE.md`'s figures move by **one** and **one**: `CONTINUOUS_UNIFORM` binds a function
    // and three reals, `a`, `b` and `e`. Tip plus this branch's delta.
    // 739 and 736 with the gauge integral, the same day, derived before the run: nine facts in
    // `Integral` under nine names, none shared. `CLAUDE.md`'s figures move by **nine** and
    // **nine**: every one binds two or more leading quantifiers, and every one binds two functions
    // or two reals among them. Tip plus this branch's delta.
    // 741 and 738 with the two facts `Collatz` crosses onto the lists by, `LIST_FOLD_EVERY` and
    // `LIST_FOLD_EVERY_CONCAT` in `Folding`, derived before the run: two facts under two names,
    // none shared. `CLAUDE.md`'s figures move by **two** and **one**: the first binds a predicate
    // and a word, two types; the second a predicate and two words, which share one. Tip plus this
    // branch's delta.
    // 748 and 745 with the sine's and the cosine's derivatives, the same day, derived before the
    // run: seven facts under seven names, none shared, two in `Transcendental`, three in
    // `Logarithm` and two in `Derivative`. `CLAUDE.md`'s figures move by **two** and **two**: the
    // two addition formulas bind `x` and `y`, and the other five bind one leading quantifier each.
    // Tip plus this branch's delta.
    // 757 and 754 with Euler's theorem, the same day, derived before the run: nine facts in `Primes`
    // under nine names, none shared; `NUM_TOTIENT` is a definition of `Modular`, which the library
    // does not collect. `CLAUDE.md`'s figures move by **nine** and **nine**. Tip plus this branch's
    // delta.
    // 759 and 756 with the existence of the integral of a continuous function, the same day,
    // derived before the run: two facts in `Integral` under two names. `CLAUDE.md`'s figures move by
    // **two** and **two**: each binds `f`, `a` and `b`, the two ends real. Tip plus this branch's delta.
    // 773 and 770 with the textbook forms of the interval theorems, 2026-09-25, derived before the
    // run: fourteen facts under fourteen names, none shared, eight in `Continuity` and six in
    // `Derivative`. `CLAUDE.md`'s figures move by **fourteen** and **fourteen**: every one binds two
    // or more leading quantifiers, and every one has two reals, or two functions, among them.
    // 777 and 774 with the fundamental theorem relative to `[a, b]`, the same day, derived before
    // the run: two facts in `Derivative` and two in `Integral`, under four names. `CLAUDE.md`'s
    // figures move by **four** and **four**: each binds at least two reals, or two functions.
    // 778 and 775 with the logarithm's slope, 2026-09-26, derived before the run: one fact under
    // one name. `CLAUDE.md`'s figures do not move: it binds one leading quantifier.
    // 781 and 778 with the integral's linearity, 2026-09-26, derived before the run: three facts
    // in `Integral` under three names, none shared. `CLAUDE.md`'s figures move by **three** and
    // **three**: each binds two functions among two or more leading quantifiers.
    // 784 and 781 with additivity and the second half of the fundamental theorem, the same day,
    // derived before the run: three facts in `Integral` under three names. `CLAUDE.md`'s figures
    // move by **three** and **three**: `HAS_INTEGRAL_JOIN` binds a function and five reals, the other
    // two a function and three reals.
    // 788 and 785 with integration by parts and the change of variables, 2026-09-26, derived before
    // the run: four facts in `Integral` under four names, none shared. `CLAUDE.md`'s figures move by
    // **four** and **four**: each binds several functions among its leading quantifiers.
    // 802 and 799 with the p-adic valuation, 2026-09-26, derived before the run: fourteen facts in
    // `Primes` under fourteen names, none shared; `NUM_VALUATION` is a definition of `Modular`, which
    // the library does not collect. `CLAUDE.md`'s figures move by **fourteen** and **fourteen**:
    // every one binds two or more leading quantifiers, all of them `num`.
    // 805 and 802 with Taylor's theorem, 2026-09-26, derived before the run and confirmed by it:
    // `CONTINUOUS_MUL`, `DERIVATIVE_POWER` and `TAYLOR`, three names none shared. `CLAUDE.md`'s
    // figures move by three and **two**: `DERIVATIVE_POWER` binds a real and a number.
    // 812 and 809 with the integral's relative forms, 2026-09-26, derived before the run: seven facts
    // in `Integral` under seven names, none shared, three congruences and four `_WITHIN` twins.
    // `CLAUDE.md`'s figures move by **seven** and **seven**: each binds two functions, or a function
    // and two or more reals. Tip plus this branch's delta.
    // 814 and 811 with Wilson's theorem and the product over paired indices, 2026-09-26, derived
    // before the run: two facts in `Primes` under two names, none shared. `CLAUDE.md`'s figures move
    // by **one** and **one**: `NUM_PROD_PAIRED` binds `m`, `f`, `t` and `n`, two of them `num` and two
    // `num -> num`, and `NUM_WILSON` binds only `p`. Measured as a delta of two, one and one on the
    // branch before the valuation and Taylor landed. Tip plus this branch's delta.
    // 821 and 818 with the reals built from the cuts, 2026-09-26: the seven primitives of `Real`
    // are defined as the cut operations they name, so seven definitional entries under seven names
    // that were declared and not defined before. `CLAUDE.md`'s figures do not move: a definition
    // binds no leading quantifier.
    // 822 and 819 with `TAYLOR_WITHIN`, 2026-09-27, derived before the run: one fact, one name,
    // and `CLAUDE.md`'s three figures move by one each, its binders being `D`, `a`, `b` and `n`.
    // 917 and 914 with the rationals and the cuts collected, 2026-09-27, card `e4a90d43`: 44 facts
    // of `Fraction` and 51 of `Cut`, which were links of the chain and in no library. Measured at
    // `7a15f023` as a delta of 95 and 95, the two figures moving together being the measurement
    // that none of the new names was already held; `CLAUDE.md`'s figures moved by 52 and 52. Tip
    // plus this branch's delta.
    // 921 and 918 with the limit of a function and L'Hopital, 2026-09-27, measured by the run:
    // `CONTINUOUS_TENDS`, `CAUCHY_MEAN_VALUE`, its relative form and `LHOPITAL`. `CLAUDE.md`'s figures
    // move by four, four and **three**: `CONTINUOUS_TENDS` binds a function and a real. Tip plus this
    // branch's delta.
    // 924 and 921 with the sum and the composition of continuous functions and the sum rule,
    // 2026-09-27, derived before the run: three facts under three names, two in `Continuity` and one
    // in `Derivative`. `CLAUDE.md`'s figures move by **three** and **three**: each binds two
    // functions among two or more leading quantifiers.
    // 929 and 926 with parts and the change of variables relative to `[a, b]`, 2026-09-27, derived
    // before the run: five facts in `Integral` under five names, none shared. `CLAUDE.md`'s figures
    // move by **five** and **five**. Base 924 and 921 plus that branch's delta.
    // 922 and 919 with `EXP_ONE_IRRATIONAL`, 2026-09-27, measured as one entry, one name and one
    // fact by the run over 7a15f023: `CLAUDE.md`'s three figures move by one each, its binders
    // being two naturals. Plus one over the base above.
    // 951 and 948 with `Circle`, 2026-09-27: twenty-one facts under twenty-one names, none shared.
    // `CLAUDE.md`'s figures move by **two** and **two**: `COS_DECREASING` and `COS_INJECTIVE` bind
    // `x` and `y`, both real, and the other nineteen bind at most one. Measured over `2cb685b7` and
    // merged as base 930 and 927 plus that delta.
    // 932 and 929 with `TAYLOR_LEFT` and `TAYLOR_LEFT_WITHIN`, 2026-09-28, derived before the run:
    // two facts in `Derivative` under two names. `CLAUDE.md`'s figures move by two each: each binds
    // a family, two reals and a natural, and the two reals share a type. Plus two over the base above.
    // 953 and 950 with both, merged on 2026-09-28 as base 930 and 927 plus `Circle`'s twenty-one and
    // the Taylor pair's two; `CLAUDE.md`'s figures likewise, 953, 632 and 565.
    // 955 and 952 with `HAS_INTEGRAL_SUBST_IMAGE` and `INTEGRAL_SUBST_IMAGE`, 2026-10-02, measured by
    // the run over the branch: two facts in `Integral` under two names. `CLAUDE.md`'s figures move by
    // two each, each binding four functions and four reals. Plus two over the base above.
    // 957 and 954 with `COS_POSITIVE` and `PI_HALF_LEAST_ZERO`, 2026-10-02, card `4bcfc8b9`: two facts
    // in `Circle` under two names, read off the run over that branch. `CLAUDE.md`'s first figure
    // moves by two and the other two do not: each binds one real. Plus two over the base above.
    // 1037 and 1034 with `Complex`, 2026-10-05, card `92c368a1`: eighty facts under eighty names,
    // none shared, derived from `Complex.Statements` before the run and equal to it. `CLAUDE.md`'s
    // figures move by eighty, thirty-eight and twenty-nine, read off the run.
    // 1044 and 1041 with the fundamental theorem of algebra, 2026-10-21, card `b244157b`: seven facts
    // under seven names, none shared, derived from `Fundamental.Statements` before the run and equal
    // to it. `CLAUDE.md`'s figures move by seven, five and one, read off the run.
    // 1049 and 1046 with the finite Fourier inversion and the Collatz iterate, 2026-10-21, card
    // `1ab3b15f`: five facts under five names, none shared, derived from `FiniteFourier.Statements`
    // and `CollatzFourier.Statements` before the run and equal to them. `CLAUDE.md`'s figures move
    // by five, four and two, read off the run.
    // 1058 and 1055 with negation in the embedded arithmetic, 2026-10-22, card `4102f131`: nine
    // facts under nine names, none shared, eight in `Deduction` and `NUM_PROV_FALSE_EQ` in `Truth`.
    // Seven of them moved `CLAUDE.md`'s figures by seven, five and five, read off a run before the
    // two about implication joined them.
    // 1067 and 1064 with `Decision`, 2026-10-22, cards `38b56577`, `a5c6f793`, `443e4c06`: eighteen
    // facts under eighteen names, none shared, derived from `Decision.Statements` before the run and
    // equal to it. `CLAUDE.md`'s figures move by eighteen, sixteen and ten, read off the run.
    // 1076 and 1073 with both, merged 2026-10-22: nine from negation and implication and eighteen
    // from `Decision`, none shared.
    // 1088 and 1085 with the rest of the distributions and the ground completeness, 2026-10-23:
    // 1076 and 1073 plus seven facts under seven names from `Decision.Statements` (card `38b56577`)
    // and five under five from `Truth.Statements` (card `4102f131`), none shared, each derived before
    // its run. `CLAUDE.md`'s figures move by twelve, eleven and nine.
    // 1089 and 1086 with `EXPECTATION_LINEAR`, 2026-10-23, card `38b56577`: one fact under a new
    // name, and six binders of which two pairs share a type, so `CLAUDE.md`'s figures move by one each.
    // 1104 and 1101 with Rule 30, 2026-10-23, card `25c7d137`: fifteen facts under fifteen new names
    // from `RuleThirty.Statements`, derived before the run and equal to it. `CLAUDE.md`'s figures
    // move by fifteen, eight and two, read off the run.
    library.entries.size shouldBe 1104
    library.names.distinct.size shouldBe 1101
  }

  it should "show where the developments overlap rather than pick one arbitrarily" in {
    // Found by building this: `Order` re-exports the facts of `Positivity`, so some names are held
    // by two developments each. A lookup returning the first would have picked by map iteration
    // order, which is a coin toss dressed as an answer.
    library.shared should not be empty
    library.named(Order.AddPositive).map(_.development).distinct.size should be > 1
  }

  it should "find a lemma by name, from any of them" in {
    library.named(Order.AddPositive) should not be empty
    library.named(Series.ByParts) should not be empty
    library.named("NOTHING_IS_CALLED_THIS") shouldBe empty
  }

  "A search by shape" should "find the lemma and not its instances" in {
    // The useful way round: a caller looking for a lemma writes the SHAPE, and the pattern's own
    // free variables are what it may bind. An instance finds nothing, which is right: somebody who
    // knows the instance does not need the search.
    val real = TyApp(Real.TypeName, Nil)
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val plus = chain.reals.theory
      .constant(Real.Addition, Type.fun(real, Type.fun(real, real)))
      .fold(error => fail(error.message), identity)

    def sum(left: Term, right: Term): Term =
      Term.appAll(plus, List(left, right)).fold(error => fail(error.message), identity)

    val shape = Term
      .eq(sum(x, y), sum(y, x))
      .fold(error => fail(error.message), identity)

    library.matching(shape).map(_.name) should contain("ADD_SYM")

    val instance = Term
      .eq(sum(chain.reals.term("0").toOption.get, x), sum(x, chain.reals.term("0").toOption.get))
      .fold(error => fail(error.message), identity)

    library.matching(instance).map(_.name) should not contain "ADD_SYM"
  }

  "A search by name" should "find what a reader half remembers" in {
    // The three searches answer different questions and a reader has one of the three: the name
    // half remembered, the shape without the name, or the constant with neither.
    library.whose("POSITIVE").map(_.name) should contain(Order.AddPositive)
    library.whose("positive").map(_.name) should contain(Order.AddPositive)
    library.whose("NOTHING").map(_.name) shouldBe empty
  }

  "A search by constant" should "answer what a reader actually asks, which is what do I have about Sum" in {
    val aboutSum = library.about(Series.SumName).map(_.name)

    aboutSum should contain(Series.ByParts)
    aboutSum should contain(Series.AtSuccessor)
    aboutSum should not contain Order.AddPositive
  }

  "The library" should "record which development holds each lemma, which is not decoration" in {
    // Two developments can hold a name each, and a caller that wants to REWRITE with a lemma has to
    // ask the one that owns it rather than the union: the union mixes theorems from developments
    // with different axioms, which is the case `docs/adr/0008`'s constant origin covers for defined
    // constants and does not cover for declared ones. Read-only is a decision, not a stage.
    library.from("Series").map(_.name) should contain(Series.ByParts)
    library.from("Series").map(_.name) should not contain Order.CancelPositive
    library.from("Order").map(_.name) contains Order.CancelPositive shouldBe true
  }

  private def document(): String =
    new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(Lemmas.Document)),
      "UTF-8"
    )

  "docs/lemmas.md" should "hold every lemma the library does, so it cannot go stale" in {
    // The document is generated from `Library.listing` and pinned here. A lemma added to any of the
    // developments and not listed fails the build, which is the same arrangement `DocumentationSpec`
    // uses for the guide's examples and for the kernel directory's file classification.
    //
    // Asserted by name as well as whole, and the two are not the same test. The whole-file
    // comparison below fails on any difference, including one in the printing; this one names the
    // lemmas, which is what a reader of the failure can act on.
    val listed = document()

    val missing = library.names.distinct.filterNot(listed.contains)
    withClue(s"in the library and not in ${Lemmas.Document}: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    library.shared.foreach(name => listed should include(name))
  }

  it should "be what the command produces, not something that resembles it" in {
    // The half of "generated" the document claimed and did not have until 2026-09-11. Names alone
    // are not enough: a hand-pasted line carries the name and can carry the wrong statement, and a
    // change to how the theory prints would leave every name present and every line stale.
    //
    // The clue is the command, because this test fails at the moment somebody adds a lemma and the
    // thing they need then is what to run.
    val generated = Lemmas.generatedPartOf(document()).fold(why => fail(why), identity)

    withClue(s"${Lemmas.Document} is not what the code says; run:\n  ${Lemmas.Command}\n") {
      generated shouldBe Lemmas.listing().trim
    }
  }

  it should "be refused rather than guessed at when the markers are not there" in {
    // This writes over somebody's document, and the one thing it must not do is decide for itself
    // where the generated part begins. Each refusal names which marker was the problem, because a
    // document missing the closing one and a document missing the opening one are repaired
    // differently.
    Lemmas.spliced("no markers here", "x").left.map(_.contains("no `")) shouldBe Left(true)
    Lemmas.spliced(s"${Lemmas.Start}\nbody", "x").left.map(_.contains(Lemmas.End)) shouldBe Left(true)
    Lemmas.spliced(s"${Lemmas.End}\nbody\n${Lemmas.Start}", "x").left.map(
      _.contains("wrong way round")
    ) shouldBe Left(true)

    Lemmas.spliced(s"head\n${Lemmas.Start}\nold\n${Lemmas.End}\ntail", "new") shouldBe
      Right(s"head\n${Lemmas.Start}\n\nnew\n\n${Lemmas.End}\ntail")
  }

  /* ------------------------------------------------------------------- the names */

  "Every name in the library" should "have the shape the convention names" in {
    // `docs/naming.md` is the convention, read off these names rather than invented for them. This
    // is the half a test can hold: uppercase letters and digits, single underscores between the
    // parts, nothing leading or trailing. All of them match it today, which is what made it worth
    // writing down as a rule rather than as an aspiration.
    val shape = "[A-Z][A-Z0-9]*(_[A-Z0-9]+)*".r

    // The facts, not the definitions. A definitional entry is keyed by the **constant** it defines,
    // and a constant is named by whatever its own development calls it: `le`, `div` and `sub` are
    // the reals' and are lowercase, `NUM_ADD` and `SUC` are the naturals' and are not, and `Sum`,
    // `Power` and `Prod` are a third style again. `docs/naming.md` records that as a description
    // rather than a rule, because it is one.
    val wrong = library.entries
      .filterNot(_.development.endsWith("defined"))
      .map(_.name)
      .distinct
      .filterNot(name => shape.matches(name))
    withClue(s"names that are not SCREAMING_SNAKE_CASE: ${wrong.mkString(", ")}\n") {
      wrong shouldBe empty
    }
  }

  it should "be counted in `docs/naming.md` by numbers that are still true" in {
    // The repair for the way that document actually broke, which was not a wrong rule: it opens by
    // counting the library four times in prose, and every one of those numbers had drifted by the
    // afternoon `SUM_CONSTANT` landed. A reader quoted one of them back at a session that was
    // holding the real figure, which is the only reason anybody looked.
    //
    // What makes it worth a test rather than a habit is that the document has been ARGUING for this
    // since its first draft: "a count maintained by hand in a document drifts from the thing it
    // counts; a count asserted in a test cannot". It went on maintaining four by hand while saying
    // so. This is that sentence applied to the file it is written in.
    //
    // Derived before it is observed, which is the discipline this axis has broken more than any
    // other here: the four figures are one total, one after removing the duplicate names, and that
    // total split into the facts and the definitional entries, so the last two must sum to the
    // second and the test says so rather than listing three independent constants.
    val document = new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get("docs/naming.md")),
      "UTF-8"
    )

    val entries = library.entries.size
    val distinct = library.names.distinct.size
    val definitional =
      library.entries.filter(_.development.endsWith("defined")).map(_.name).distinct.size
    val facts = distinct - definitional

    withClue("the document's split does not add up to the library's names\n") {
      facts + definitional shouldBe distinct
    }

    // One sentence rather than four loose figures, because four loose figures cannot fail. A number
    // as small as the definitional count can turn up in that document for unrelated reasons, so a
    // check that looked for each number somewhere in the file would pass whatever the count was.
    // That is the vacuity this repository's conventions warn about, met while writing the guard
    // against a different one.
    val sentence =
      s"the library holds $entries entries, $distinct distinct names, $facts facts and " +
        s"$definitional definitional entries"

    withClue(s"docs/naming.md does not contain, verbatim:\n  $sentence\n") {
      document should include(sentence)
    }
  }

  it should "say in `CLAUDE.md` how wide the positional-specialisation hole is, in numbers it counts" in {
    // The same repair as the one above, on a different count and for a sharper reason. `CLAUDE.md`
    // tells a reader not to specialise a library lemma by position, and the argument for it is a
    // measurement of this library: a reversal of two quantifiers is invisible to the type checker
    // exactly where two of them range over the same type. That figure moves whenever a lemma lands,
    // and a stale one understates a hole rather than overstating it, which is the direction that
    // gets somebody hurt.
    //
    // What the number counts, said here because the sentence in the document cannot carry it: two
    // leading binders that share a type ANYWHERE in the prefix, not only adjacent ones. So it is an
    // upper bound on the surface actually at risk, since swapping the first and the fifth is a
    // mistake nobody makes; the narrow reading would be `sliding(2)` and is a different number.
    val document = new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get("CLAUDE.md")),
      "UTF-8"
    )

    val prefixes = library.entries.flatMap(entry =>
      Logic.stripForall(entry.theorem.conclusion).toOption.map(_._1.map(_.ty))
    )
    val manyBinders = prefixes.filter(_.length >= 2)
    val alike = manyBinders.count(types => types.distinct.length != types.length)

    // Derived before it is observed, the way the four above are: the exposed lemmas are a subset of
    // the ones with two or more binders, which is a subset of the library. A guard that let those
    // three be independent constants could pass on three numbers that cannot all be true at once.
    withClue("the three figures are not nested\n") {
      alike should be <= manyBinders.length
      manyBinders.length should be <= library.entries.size
    }

    val sentence =
      s"of the library's ${library.entries.size} lemmas, ${manyBinders.length} have two or more " +
        s"leading quantifiers and **$alike of\nthose have two that share a type**"

    withClue(s"CLAUDE.md does not contain, verbatim:\n  $sentence\n") {
      document should include(sentence)
    }
  }

  it should "spell each concept one way, and the exceptions can only shrink" in {
    // The rule with teeth. Where two spellings of one idea are in use the shorter is the
    // convention, and the three names below are the corpus breaking it. They are **not** renamed
    // here: each is referred to from outside this repository, and a rename is worth doing once,
    // deliberately, with the references moved in the same change.
    //
    // What this buys until then is that the next lemma cannot add a fourth spelling, and that the
    // list goes red when one of these is finally renamed, which is how an exception list stops
    // being a place things are filed and forgotten.
    val longer: Map[String, String] = Map(
      "NONNEGATIVE" -> "NONNEG",
      "TRANSITIVE" -> "TRANS",
      "ANTISYMMETRIC" -> "ANTISYM"
    )

    val known = Set("SUM_NONNEGATIVE", "LT_TRANSITIVE", "LE_ANTISYMMETRIC")

    val offenders = library.entries
      .filterNot(_.development.endsWith("defined"))
      .map(_.name)
      .distinct
      .filter(name =>
      longer.keys.exists(spelling => name.endsWith(spelling))
    )

    withClue(s"a spelling the convention does not use: ${(offenders.toSet -- known).mkString(", ")}\n") {
      (offenders.toSet -- known) shouldBe empty
    }

    // And the list fails when a member stops being one, which is what keeps it honest.
    withClue(s"named as an exception and no longer in the library: ${(known -- offenders.toSet).mkString(", ")}\n") {
      (known -- offenders.toSet) shouldBe empty
    }
  }

  "What a proof rests on" should "name the held lemmas that took part, and not the ones that did not" in {
    // `0 < 1` is `ZERO_LT_ONE`, and it is proved rather than assumed: its own derivation reaches
    // axioms of the order and none of the lemmas below it, because there are none. What it must
    // NOT report is every lemma in the library, which is what a version comparing by axiom would
    // have done, and it must report itself, because a theorem rests on itself trivially and a
    // caller filtering that out can, while a caller wanting it back cannot.
    val zeroLessOne = chain.order.zeroLessOne.fold(error => fail(error.message), identity)
    val resting = library.restingOn(zeroLessOne).map(_.name).distinct

    resting should contain(Positivity.ZeroLessOne)
    resting should not contain Series.Telescoping
  }

  it should "separate what a proof used from what the theory permits" in {
    // The point of the whole function, as a comparison. `axiomsOf` answers what a proof is believed
    // on and is coarse by construction; this answers which named facts took part. A proof of a
    // numeral fact rests on many axioms and on few lemmas, and a report that could not tell those
    // apart would call every arithmetic proof equally unsurprising.
    val twelve = chain.order.positive(12).fold(error => fail(error.message), identity)

    val axioms = Real.spent(twelve).size
    val lemmas = library.restingOn(twelve).map(_.name).distinct.size

    withClue(s"$axioms axioms and $lemmas named lemmas\n") {
      axioms should be > 0
      lemmas should be < library.names.distinct.size
    }
  }

  "A goal that IS a held lemma" should "be found, applied, and owe nothing" in {
    // The claim `Prove`'s library lookup rests on, asserted where the library is rather than where
    // the prover is: `!x. 0 <= x * x` is `SQUARE_NONNEG`, and applying it to that goal must decide
    // every variable and leave no obligation. If this fails, the lookup in `Prove` cannot fire and
    // the refusal a caller gets is LINARITH's, which is what happened on the first run.
    val logic = force(chain.reals.logic.over(chain.reals.theory))
    val goal = force(chain.reals.proposition("!x:real. 0 <= x * x"))

    val found = library.instantiating(goal)
    withClue(s"the library holds ${library.entries.size} entries and none matches\n") {
      found.map(_.name) should contain(Order.SquareNonNegative)
    }

    val applied = force(Apply.to(logic, force(chain.order.squareNonNegative), goal))
    applied.obligations shouldBe empty

    // The goal's own quantifier came off before matching and goes back on here. `Apply` leaves that
    // to the caller on purpose: it cannot know whether the obligations are going to be discharged
    // first, and the obligations mention the variables the quantifier bound.
    applied.theorem.conclusion shouldBe force(chain.reals.proposition("0 <= x * x"))
    force(logic.rules.genAll(applied.theorem, applied.generalising.toList)).conclusion shouldBe goal
  }

  "A goal at an instance of a POLYMORPHIC lemma" should "be found and applied, at that instance" in {
    // The measurement the repair is for, asserted where the library is. `FST_PAIR` is
    // `!x:'a. !y:'b. FST (PAIR x y) = x` and the goal below is it at `num`; until 2026-09-12 the
    // lookup went through a matcher that compared `Const("FST", prod('a,'b) -> 'a)` with
    // `Const("FST", prod(num,num) -> num)` by identity, failed on the head before reaching an
    // argument, and reported `Unsettled` from a system holding the lemma that IS the goal.
    val logic = force(chain.widest.logic.over(chain.widest.theory))
    val goal = force(chain.widest.proposition("!x:num. !y:num. FST (PAIR x y) = x"))

    library.instantiating(goal).map(_.name) should contain(Product.FirstOfPair)

    val applied = force(Apply.to(logic, chain.product.facts(Product.FirstOfPair), goal))
    applied.obligations shouldBe empty

    // What it decided, both halves. The type substitution is the half that did not exist before,
    // and it is what makes the theorem below a theorem about `num` rather than about `'a`.
    val num = TyApp(Natural.TypeName, Nil)
    applied.instantiation.types shouldBe
      Map(Classical.TypeVariable -> num, Classical.CodomainVariable -> num)

    val proved = force(logic.rules.genAll(applied.theorem, applied.generalising.toList))
    proved.conclusion shouldBe goal
    proved.hypotheses shouldBe empty
  }

  "A lemma with premises, applied to itself" should "owe nothing, and owe its premises only where they were dropped" in {
    // `Apply` reads the whole body first and promises that a lemma matching the goal whole owes
    // nothing. Until 2026-10-02 it then counted every antecedent of the instance as an obligation,
    // so the promise held only for lemmas with no premises and the prover's scan turned away
    // `COS_INJECTIVE` asked verbatim (card 39429606). The second half is the control: the same lemma
    // applied to its bare conclusion must still owe the premise, or the first half would pass on an
    // `Apply` that had stopped owing anything at all.
    val logic = force(chain.widest.logic.over(chain.widest.theory))
    val lemma = chain.circle.facts(Circle.CosInjective)

    val whole = force(Apply.to(logic, lemma, lemma.conclusion))
    whole.obligations shouldBe empty
    force(logic.rules.genAll(whole.theorem, whole.generalising.toList)).conclusion shouldBe
      lemma.conclusion

    val bare = force(Apply.to(logic, lemma, force(chain.widest.proposition("!x:real. !y:real. x = y"))))
    bare.obligations.map(chain.widest.show) shouldBe
      Vector("0 <= x /\\ x <= pi /\\ 0 <= y /\\ y <= pi /\\ cos x = cos y")
  }

  "The listing" should "print in the signature's own notation, not the kernel's" in {
    // A lemma printed in the kernel's notation is a lemma about a claim the reader did not write.
    val page = library.listing(chain.series)

    page should include("## Order")
    page should include("## Series")
    page should include("## Real, derived")

    // The kernel's printer writes an application as `((< x) y)`. The theory's writes `x < y`. A
    // first version of this test looked for `BIT1` and failed on the DEFINITION of `BIT1`, which is
    // legitimately in the listing: the assertion was wrong, not the page.
    page should not include "((< "
    page should not include "((+ "
  }

  "A published fact" should "reach its consumers as a citation, from every development that publishes" in {
    // `docs/adr/0047` put the boundary where a development publishes, one line per development, and
    // a development that leaves the line out is invisible: its facts still prove, every proof above
    // it still checks, and every report on those proofs quietly walks the whole of it again. Two
    // did on the day the boundary landed, `CommutativeRing` and `Pigeonhole`, merged hours earlier
    // on another branch, and the rebase is what showed them. So both halves are asserted here.
    //
    // What the library collects, read at run time: every derived entry is a citation of its own
    // name. The axioms and definitions are what the library also holds under `assumed` and
    // `defined`, and those are records of an extension rather than facts anybody proved.
    val derived = library.entries.filterNot(entry =>
      entry.development.endsWith(", assumed") || entry.development.endsWith(", defined")
    )
    val uncited = derived.filterNot(entry => entry.theorem.derivation match {
      case Derivation.Citation(name, _) => name == entry.name
      case _ => false
    })

    derived.size should be > 100
    withClue(s"published without a citation: ${uncited.map(e => s"${e.development}.${e.name}").take(10)}\n") {
      uncited shouldBe empty
    }

    // And what the library does not collect, read off the sources: a development beside the chain
    // publishes too, and `Library.of` names only the chain. A field of that name and type is what a
    // consumer reads, so every one of them is the cited one.
    val declaration = raw"val facts: Map\[String, Kernel\.Thm\]([^\n]*)".r
    val sources = java.nio.file.Files
      .walk(java.nio.file.Paths.get("modules"))
      .iterator()
      .asScala
      .map(_.toString)
      .filter(path => path.endsWith(".scala") && path.contains("/src/main/"))
      .toVector
    val fields = sources.flatMap { path =>
      val text = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(path)), "UTF-8")
      declaration.findAllMatchIn(text).map(found => (path, found.group(1).trim)).toVector
    }
    val bare = fields.filterNot { case (_, rest) => rest.startsWith("= Published.cite(") }

    fields.size should be > 40
    withClue(s"a facts field that is not cited: ${bare.map(_._1)}\n") { bare shouldBe empty }
  }
}
