package garden.xeno.symbolum.theories

/**
 * The English a generated page needs that is not mathematics, which today is one function.
 *
 * == Why it is a file of its own, and why in this module ==
 *
 * It began as `Essay.count`, `private`, with three of its four call sites not using it, which is
 * why that page said "1 steps" and "1 inferences" until 2026-09-18. Repairing that found the same
 * shape at three more sites, in `Cost`, `Ledger` and `Argument`, and all three are in
 * `modules/tactics` where an object private to `theories` cannot be seen. Three roads were open and
 * the choice is the only thing here that is not obvious, so it is written down rather than left to
 * be reconstructed from the result.
 *
 * Writing a second copy in `tactics` was refused: two copies of one condition is the shape this
 * repository calls a fact written twice, and the two would then have to be kept saying the same
 * thing by nobody. Conditioning the seven call sites by hand was refused for the same reason
 * multiplied by seven. So the counter is published, and the question left is where.
 *
 * **Not on `Essay`, which is what publishing it in place would have meant.** `Cost.page` does not
 * produce an essay, so `Essay.count` read at a call site in `modules/tactics` would be a false
 * statement about what the caller is doing. `theories` is the lowest module both consumers see —
 * `tactics` depends on it, and `core` and `sat` depend on nothing at all and so are out of reach by
 * construction, which is the trust boundary working rather than an omission. `Essay` and
 * `Spellings` already put rendering in this module, so this is beside them rather than a new kind
 * of thing in it.
 *
 * A module of its own was considered and refused for lack of the measurement that would justify
 * one. `scan` is a module because six gates had each decided the same question separately and two
 * of the answers disagreed on three inputs; here there is one function, seven call sites and
 * nothing disagreeing.
 *
 * == What a site of this class looks like ==
 *
 * A count written into a message that also writes a word agreeing with it. The census of card
 * db67b658 looked for the noun right after the number, `$n steps`; card 601788d5 widened it to a
 * modifier in between, `$n named facts`, and found three more sites that reach one, in `RestsOn`,
 * in `Cnf` and in `Remedy`. Beside the last was a fourth that no census of a noun selects, because
 * what agrees is a demonstrative before the number, `these $n cannot`. A counter repairs the first
 * two shapes and not the third, which is written as two sentences instead. What neither census
 * reads is a count that is a constant, or one whose guard keeps it off one, such as `Mark`'s
 * `holes.length != 1`: those print a plural correctly and are left alone.
 */
object Prose {

  /**
   * A number and its noun, with the plural where the number needs one.
   *
   * **It appends an `s` and is not a rule about English.** That is right for `axiom`, `named fact`,
   * `step`, `inference`, `claim`, `point` and `idle citation`, which are all of today's callers,
   * and wrong for the first irregular noun anybody routes through it. A noun that does not take a
   * plain `s` wants its two forms written out, not this.
   *
   * Zero takes the plural, which is what English does and is worth saying because it is the case a
   * reader of the condition does not picture: "0 axioms" and never "0 axiom".
   */
  def count(howMany: Int, noun: String): String =
    if (howMany == 1) s"1 $noun" else s"$howMany ${noun}s"

  /**
   * The same with both forms written out, for a noun that does not take a plain `s`.
   *
   * The paragraph above says such a noun wants its two forms rather than the counter, and until
   * 2026-09-22 that sentence left the caller nowhere to put them: `Remedy` wrote
   * `${n} thing(s)` instead, which is a mechanism of its own and reads badly at every number.
   * The five per-module copies of this counter have taken both forms since 2026-09-20, for
   * `entry`/`entries` in `core`, so this is the shared one catching up with them rather than a
   * new idea.
   *
   * It is an overload and not a default argument, because a default would let a caller write
   * `count(n, "hypothesis")` and get `hypothesiss` from the one-argument body.
   */
  def count(howMany: Int, one: String, many: String): String =
    s"$howMany ${if (howMany == 1) one else many}"

  /**
   * The same where the count is a `BigInt`, and it is an overload rather than a conversion.
   *
   * `Value`'s search bound is `right / answer + 1` over big integers and reaches one exactly when
   * the answer is zero, so the site is in this class; `toInt` at the call would print a different
   * number for a bound past the machine word, which is a worse defect than the one being
   * repaired.
   */
  def count(howMany: BigInt, noun: String): String =
    if (howMany == 1) s"1 $noun" else s"$howMany ${noun}s"
}
