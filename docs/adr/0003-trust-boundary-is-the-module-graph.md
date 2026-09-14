# 0003. The trust boundary is the module graph

- **Status:** accepted
- **Date:** 2026-09-03

## Context

The whole correctness argument of the system reduces to one claim: nothing except the kernel can
construct a theorem. Everything else, the rewriting, the decision procedures, the tactics, the
computer algebra system, may be arbitrarily wrong and cost at worst a failed proof attempt.

A claim of that shape maintained by convention decays. It decays quietly, because the import that
breaks it compiles, passes the tests, and looks like a small convenience at the call site.

The existing code makes the risk concrete rather than theoretical. The CAS lives entirely in one
package, `garden.xeno.symbolum`, and several of its rewrites are not valid as unconditional identities:
cancelling a common factor without a non-zero hypothesis, `exp(log x) → x` without positivity,
`(b^i)^o → b^(i·o)` which is false for `(x^2)^(1/2)`. These are reasonable heuristics for a
simplifier and inadmissible as proof steps, and package-private visibility would let any file in
that package reach the kernel.

## Decision

The boundary is a build dependency, not a naming convention. The repository is split into sbt
modules and the dependency direction is fixed:

```
kernel   -> (nothing)
logic    -> kernel
theories -> logic
tactics  -> theories, core
core     -> (nothing)
examples -> core
```

> Amended 2026-09-10. `checker -> kernel` joined the graph, a second reading of a proof that
> depends on the kernel for the data a theorem carries and reaches for none of its rules. It is not
> trusted and is not meant to be: it is a second opinion, and `docs/architecture.md` carries the
> current graph.

> Amended 2026-09-13. `examples -> core` became `examples -> tactics`. The decision this record is
> about is unchanged and so is every edge below `tactics`: what moved is the one edge above the
> boundary, so that a demonstration of the proof half has somewhere to live. The block above is
> kept as it was decided; `docs/architecture.md` carries the current graph.

`core` is the existing CAS, unchanged. It is invisible from `kernel`, `logic` and `theories`: an
import of it from the trusted base is a compile error, not a review finding.

`Thm` is an opaque type in `kernel` whose constructors are the primitive inference rules and
nothing else.

> Amended 2026-09-10, mechanism only. `Thm` is a final class with a constructor private to
> `object Kernel`. The property this decision asked for is the one above and is unchanged; what
> changed is that an opaque type could not carry it, because it erases to what it wraps and a cast
> from the underlying pair produced a theorem while the compile-time assertion about it passed. A
> class does not erase, and `TrustBoundaryTwinSpec` asserts the cast now raises.

`core` keeps the published coordinates the library already has, so the split is invisible to
anyone depending on it.

## Consequences

The trusted base is now something that can be pointed at rather than described: it is the source
of `kernel`, and its size is a number anyone can measure.

The CAS needs no correction to be used. Its invalid-as-identities rewrites become an oracle's
guesses: a tactic asks it for a candidate result and then has to prove that result through the
kernel, so a wrong guess costs a failed tactic and can never produce a theorem. This is what
makes the existing code reusable as it stands.

Sharing gets harder, and that is the price. Exact arithmetic will be wanted on both sides, by the
oracle to guess quickly and by the numeral rules to be certified, and it cannot be shared through
`core` because the trusted side may not see `core`. If sharing turns out to be worth it, it goes
in a leaf module that both sides may depend on, which is a decision to record then, not now.

What this does not cover, stated because a boundary invites the wrong inference: it bounds what
has to be reviewed. It says nothing about whether the code inside the boundary is correct. A bug
in the kernel is unbounded, and the only mitigations for that are the kernel's small size, direct
tests of its rules, and a check that the theory's axiom set is exactly the declared one.

## Alternatives rejected

**One module with package-private discipline.** No build changes, no restructuring. It loses on
the facts of the codebase: `private[symbolum]` is visible to the whole CAS, which is the code
the boundary exists to exclude. Making it work would mean renaming packages so that the CAS is
not a parent of the kernel, at which point the module split is the same work with an enforcement
mechanism attached.

**A separate repository for the kernel.** Real isolation, and the strongest version of this
decision. It loses because the kernel and the tactics that exercise it will be edited together
for the foreseeable future, and every such change would become a two-repository change with a
publication step in between. Reconsider once the kernel stops changing weekly.

**No boundary, review as the mechanism.** Rejected on the basis that this is a single-author
project. There is no second reader, so an enforcement mechanism that costs a compile error is
worth more here than in a team.
