package garden.xeno.symbolum.sat

/**
 * The English a message of this module needs that is not its subject, which today is one function.
 *
 * **A copy, one per module, and the copy is the price of the dependency graph rather than an
 * oversight.** The counter the rest of the repository uses is `Prose.count` in `modules/theories`,
 * which this module cannot see: `sat` depends on nothing, and a module that cannot see `kernel`
 * cannot construct a theorem whatever it does, which is what makes an untrusted search safe to
 * have. What is repeated here is a rule of English rather than a fact about this system, so it
 * cannot drift against any source of truth in it, and a test in this module's own spec holds each
 * site that uses it.
 *
 * **It takes BOTH forms where `Prose.count` appends an `s`**, and the reason is in `core`: the
 * noun there is `entry`/`entries`, and `Prose.count` says of itself that an irregular noun wants
 * its two forms written out rather than a counter that can only append.
 *
 * It is a file of its own rather than a private method beside the site that first needed one,
 * because two modules turned out to have two sites each and a second private copy inside one
 * module is the duplication this arrangement is paying to avoid, not the one it accepts.
 */
private[sat] object Plural {

  /** A number and its noun, with the singular at one. */
  def count(howMany: Int, one: String, many: String): String =
    s"$howMany ${if (howMany == 1) one else many}"
}
