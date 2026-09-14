package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

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
      chain.reals.axioms.size + chain.reals.definitions.size +
      chain.ring.positivity.facts.size + chain.order.facts.size +
      chain.naturals.facts.size + chain.peano.facts.size + chain.series.facts.size +
      chain.divisibility.facts.size + chain.modular.facts.size +
      chain.product.facts.size + chain.word.facts.size + chain.matrix.facts.size +
      chain.rotation.facts.size + chain.magnitude.facts.size + chain.coding.facts.size +
      chain.numbering.facts.size + chain.language.facts.size +
      chain.provability.facts.size + chain.deduction.facts.size +
      chain.primes.facts.size

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
    library.entries.size shouldBe 398
    library.names.distinct.size shouldBe 395
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

    // One sentence rather than four loose figures, because four loose figures cannot fail. A bare
    // `6` occurs five times in that document for unrelated reasons, so a check that looked for each
    // number somewhere in the file would have passed whatever the definitional count really was.
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

    val axioms = Derivation.axiomsOf(twelve).size
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

  "The listing" should "print in the signature's own notation, not the kernel's" in {
    // A lemma printed in the kernel's notation is a lemma about a claim the reader did not write.
    val page = library.listing(chain.series)

    page should include("## Order")
    page should include("## Series")
    page should include("## Real, assumed")

    // The kernel's printer writes an application as `((< x) y)`. The theory's writes `x < y`. A
    // first version of this test looked for `BIT1` and failed on the DEFINITION of `BIT1`, which is
    // legitimately in the listing: the assertion was wrong, not the page.
    page should not include "((< "
    page should not include "((+ "
  }
}
