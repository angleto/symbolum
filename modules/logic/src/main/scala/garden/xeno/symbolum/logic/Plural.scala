package garden.xeno.symbolum.logic

/**
 * The English a message of this module needs that is not its subject, which today is one function.
 *
 * **A copy, one per module, and the copy is the price of the dependency graph rather than an
 * oversight.** The counter the rest of the repository uses is `Prose.count` in `modules/theories`,
 * which this module cannot see: `logic` sits below `theories` in the graph -- the connectives, the
 * derived rules and the parser are what `theories` is built on -- so the direction that makes the
 * chain a chain is what puts the shared counter out of reach. What is repeated here is a rule of
 * English rather than a fact about this system, so it cannot drift against any source of truth in
 * it, and a test in this module's own spec holds each site that uses it.
 *
 * **It takes BOTH forms where `Prose.count` appends an `s`**, and the reason is in `core`: the
 * noun there is `entry`/`entries`, and `Prose.count` says of itself that an irregular noun wants
 * its two forms written out rather than a counter that can only append.
 */
private[logic] object Plural {

  /** A number and its noun, with the singular at one. */
  def count(howMany: Int, one: String, many: String): String =
    s"$howMany ${if (howMany == 1) one else many}"
}
