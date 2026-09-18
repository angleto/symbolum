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
}
