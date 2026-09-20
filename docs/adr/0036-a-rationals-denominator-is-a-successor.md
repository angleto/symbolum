# 0036. A rational's denominator is a successor, so the carrier needs no carving

- **Status:** accepted
- **Date:** 2026-09-20

## Context

[`0033`](0033-the-integers-arrive-as-a-prerequisite-and-not-as-stage-four.md) landed `int` as
`Quotient.define` over pairs of naturals, and [`0016`](0016-what-the-construction-needs-in-front-of-it.md)
puts the rationals next. The obvious carrier is a pair of integers and **the obvious relation on it
is not an equivalence relation**, which is the whole subject of this record: the question the
rationals ask that the integers did not is what to do about the denominator.

On pairs of integers with `R (a, b) (c, d)` meaning `a * d = c * b`, transitivity fails, and it
fails at a pair a caller can write:

    (1, 1) R (0, 0)   because   1 * 0 = 0 * 1
    (0, 0) R (2, 3)   because   0 * 3 = 2 * 0
    (1, 1) R (2, 3)   is        1 * 3 = 2 * 1,   which is 3 = 2

The zero denominator relates everything to itself and nothing through itself. `Quotient.define`
asks for `|- !x y z. R x y ==> R y z ==> R x z` over the **whole** carrier, so this relation cannot
be handed to it, and that is a fact about the relation rather than a limitation of the builder.

## Decision

**The carrier is `prod(int, num)` and the denominator of `(a, d)` is `INT_OF_NUM (SUC d)`.**

The relation is then

    RAT_SAME p q  :=  FST p * INT_OF_NUM (SUC (SND q)) = FST q * INT_OF_NUM (SUC (SND p))

and it is an equivalence relation on every pair there is, with no subtype and no side condition:
reflexivity and symmetry are immediate, and transitivity cancels `INT_OF_NUM (SUC (SND q))`, which
is a factor that cannot be zero because it is a successor.

**What this buys is that no operation owes anything.** Written on this carrier,

    (a, d) + (a', d')  =  (a * SUC d' + a' * SUC d,  d * d' + d + d')
    (a, d) * (a', d')  =  (a * a',                   d * d' + d + d')
    -(a, d)            =  (-a,                       d)

and the new index is `d * d' + d + d'` because `SUC d * SUC d' = SUC (d * d' + d + d')`, which is
arithmetic on `num` with no subtraction in it. Every one of the three is a total function of the
representatives, so each is a `Quotient.liftUnary` or `liftBinary` against a respectfulness
obligation and nothing else.

## Alternatives rejected

**Carve the pairs with a non-zero second component and quotient that.** This is the faithful
translation of the textbook and it is refused on what it costs downstream rather than on what it
costs at the carving. `Kernel.defineType` would take the predicate happily; the price is that
**every operation then owes that its denominator is non-zero**, so the product of two non-zero
integers being non-zero has to be proved before multiplication can be lifted at all. `Integer`
publishes no such fact today, and it is not one line: it is the absence of zero divisors, which
over this construction of `int` goes through the pair representation and the cancellation law on
`num`. It would also add a second type operator and a second abstraction-representation pair to a
development that already has one.

**Take the junk class.** Making `R` relate all the zero-denominator pairs to each other and to
nothing else gives an equivalence relation on the whole of `prod(int, int)`, which `define` would
accept. What comes out is `rat` with **one extra element**, and every field fact afterwards is
either false of it or carries a hypothesis excluding it. The construction would then be paying for
the rest of its life for an element nobody wants, and `RealSpec`'s property that the sixteen keep
their printed forms — which [`0004`](0004-reals-axiomatised-not-constructed.md) preserved on
purpose — could not survive a carrier with a junk point in it.

**Define the rationals as a predicate on the reals, as HOL Light does.** That is a different
project: it presupposes the reals, and [`0007`](0007-the-reals-are-constructed.md) has the reals
arriving **after** the rationals. It is the right answer in a system whose reals are axiomatic and
the wrong one here, and the reason is the order of construction rather than the merits.

## Consequences

**One lemma is owed to `Integer` before `Rational` can be written**, and it is the one thing the
transitivity above cannot do without: cancelling a positive factor,

    INT_MUL_CANCEL_NUM   |- !x y d. x * INT_OF_NUM (SUC d) = y * INT_OF_NUM (SUC d) ==> x = y

It is the restricted form on purpose. The general law wants `~(c = 0) ==> x * c = y * c ==> x = y`,
which is the absence of zero divisors again; the restricted one goes through `INT_CASES` to the
pair representation, `INT_MUL_PAIRS` and `INT_EQ_PAIRS` to an equation on `num`, and
`Peano.NUM_MUL_CANCEL_LEFT`, which this library already holds. A development that later wants the
general law can prove it and this one will not need changing.

**The representation is not the one a reader expects, and the file has to say so.** `(a, d)`
denotes `a / (d + 1)`, so the pair `(3, 1)` is three halves and not three. Every published
statement about the carrier carries `SUC` where a reader expects a denominator, which is the same
trade `Integer` makes by writing `a + d = c + b` where a reader expects `a - b = c - d`, and for
the same reason: the shape that has no side condition is the shape that can be lifted.

**The order is again the one construct the builder does not reach.** `Quotient` lifts a unary
operation, a binary one and a predicate of one argument, and `INT_LE` had to be defined through
the chosen representatives directly for exactly that reason, which `0033` records. `RAT_LE` will
be the third time, and the respectfulness obligation is again an equation between propositions
rather than between elements. That is a known and measured cost rather than a surprise, and it is
the paragraph `0016` should be read against when the reals' cuts arrive.

**What this record does not decide** is the route after the rationals. `0016` leaves open whether
the reals are Dedekind cuts over the rationals or the completion of a positive cone, and the
measurement of 2026-09-19 on card `fa8737ad` found that the cost of the quotient builder does not
separate them: what separates them is the multiplication, on cuts or on the cone, and neither has
been measured. A signed rational is what both routes want under them, so nothing here narrows that
choice.
