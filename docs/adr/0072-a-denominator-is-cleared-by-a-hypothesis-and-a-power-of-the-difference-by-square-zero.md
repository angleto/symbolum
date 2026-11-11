# 0072. A denominator is cleared by a hypothesis, and a power of the difference by `SQUARE_ZERO`

- **Status:** accepted, takes up the first item `docs/adr/0071` left next
- **Date:** 2026-11-11

## Context

`docs/adr/0071` put the equations of a goal's hypotheses into an ideal and named what it left
behind. First on that list was `amc12_2000_p20`:

```
0 < x /\ 0 < y /\ 0 < z ==> x + 1/y = 4 ==> y + 1/z = 1 ==> z + 1/x = 7/3 ==> x * y * z = 1
```

which is out of reach for two reasons, and each is enough on its own. The quotients `1/y` are
atoms of the ideal, and nothing tied `inv y` to `y`. And once they are tied, `x * y * z - 1` is
still not in the ideal: the product of the three equations gives `t + 1/t = 2` for `t = x * y * z`,
so what the ideal holds is `(t - 1)^2`, and getting from there to `t = 1` is the step an ideal does
not take. Real numbers take it: a square is zero only at zero. That fact was not in the library
under any name, searched by shape on 2026-11-10.

## Decision

1. **A denominator joins the generators exactly when a hypothesis says it is not zero.** For an
   atom `inv r`, which `l / r` is read as a product with, the equation `r * inv r = 1` is added
   when some hypothesis states `~(r = 0)` or `0 < r`. It comes from `MUL_INVERSE` and, for the
   second form, from `NON_ZERO`, so it is a theorem resting on that hypothesis and enters the
   certificate like an assumed equation. A denominator nobody stated anything about stays an
   unknown.
2. **The radical is reached by squaring, and only by squaring.** When the difference `D` is not a
   member, the search asks for `D^2` and then `D^4`, at most `Ideal.Squarings` times. A member
   `D^(2^m)` is rebuilt as `H = 0` with `H` the term `D` squared `m` times, and `SQUARE_ZERO`
   applied `m` times gives `D = 0`, then one ring step gives `L = R`.
3. **`SQUARE_ZERO` is a lemma of the order: `!x:real. x * x = 0 ==> x = 0`.** Derived in
   `theories/Order.scala` by the three cases `squareNonNegative` uses, asserting nothing.
   `Ideal` is constructed over an `Order` from now on rather than over a `Ring`, because that is
   where this lemma and `NON_ZERO` live.
4. **A refusal after every squaring stays `OutsideTheIdeal`, and so stays unread.**

## Alternatives rejected

**Clearing every denominator.** `x = 1 / y ==> x * y = 1` is false at `y = 0`, where the reals
give `inv 0 = 0` and so `x * y = 0`. Without a hypothesis saying `y` is not zero, `MUL_INVERSE`
cannot be instantiated, so the equation `y * inv y = 1` could only enter by being asserted, which
nothing here does. Handing it to the search anyway would buy certificates that the kernel half
cannot then build, so the rule decides which equations the search sees at all. `IdealSpec` holds
that claim as a refusal.

**The general zero-product law, `x * y = 0 ==> x = 0 \/ y = 0`.** It would serve a radical whose
witness is a product of different factors, and none is asked for. It needs a case split on a
proposition and `MUL_INVERSE`, and `Order` has the trichotomy but no `Classical`; the square needs
only the trichotomy.

**Every power, not only the powers of two.** `D^k` in the ideal puts every larger power in it,
the next power of two included, so the powers of two lose no member up to the bound; what they
save is a root that is not a square root, which `SQUARE_ZERO` does not take back.

**A real radical.** The reals are not algebraically closed, and `x * x + y * y = 0 ==> x = 0` is
true with no power of `x` in that ideal. Deciding membership in the real radical is a
Positivstellensatz search, and it is a separate procedure. `IdealSpec` keeps that claim as a
refusal that must stay unread.

## Consequences

**Measured on 2026-11-11, `ReachSpec` in two whole-suite runs.** Before: Proved 26, Unsettled 13,
at `7711d5d9`. After: **Proved 27, Unsettled 12**, at `7711d5d9` with this change. The one that
moved is `amc12_2000_p20`. These are figures of one day; `ReachSpec` prints the live ones.

**`SQUARE_ZERO` moves seven pinned figures by one each**, which is the library's size and the
proposals made from it: `LibrarySpec` twice (entries and distinct names), `RediscoverySpec` twice
(weakenings and the mutable count) and `ProposeSpec` three times (proposals, decided false, and
decided false with a point), each with its line saying why, and `docs/naming.md` and `AGENTS.md`
where those counts are spelled. The last of the seven was not moved with the others and was read
off the next run.

**The bound is chosen, not measured.** `Ideal.Squarings` is two: the one statement asking for
the radical needs one squaring, and each squaring doubles the degree the search works at.
`IdealSpec` puts the line where it is, with a cube that needs two and a fifth power refused.

**What a proof costs.** `IdealSpec` prints it: `amc12_2000_p20` is 303866 inferences, more than
twice `mathd_algebra_338`, and took about six seconds in that suite.

**The kernel checks the descent.** `tools/verify/perturb-radical.sh` asks for no squaring, which
turns the three radical cases red as refusals, and skips one `SQUARE_ZERO` step, which turns them
red as `NotRebuilt` with no theorem.

**Still next**, from `docs/adr/0071`'s table: combining the ideal with the order through
`Linarith`, for the two statements that need a sign, `amc12b_2002_p19` and `amc12b_2002_p7`.
