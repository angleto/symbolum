# The mark

**EXCERPT — for anyone scanning the index:**
The project's mark, in the two forms it has: character art for a terminal and `logo.svg` for a
page. Both are the same figure, a lowercase sigma whose interior is the continuous flow of the
operators the notation actually uses. This file also records why those characters and not others,
why the figure is the size it is, and how to tell a correct copy of the art from a corrupted one.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## The art

```
                |-!?~/\\/==><                                                      =>
           =\->|-!?~/\\/==><=>=\->                                             |-!?~/
        \\/==><=>=\->|-!?~/\\/==><=>=\->|-!                                ?~/\\/==><
      =>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-                 !?~/\\/==><=>=\-
    >|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?
   ~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/=
  =><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>
 =\->|-!?~/\\/==>           <=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/
\\/==><=>=\->|-               !?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/
==><=>=\->|-!                   ?~/\\/==><=>=       \->|-!?~/\\/==><=
>=\->|-!?~/\\                   /==><=>=\->|-
!?~/\\/==><=>                   =\->|-!?~/\\/=
=><=>=\->|-!?                   ~/\\/==><=>=\
->|-!?~/\\/==                   ><=>=\->|-!?~
/\\/==><=>=\->|               -!?~/\\/==><=>=
 \->|-!?~/\\/==><           =>=\->|-!?~/\\/=
  =><=>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><
   =>=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><=
    >=\->|-!?~/\\/==><=>=\->|-!?~/\\/==><
      =>=\->|-!?~/\\/==><=>=\->|-!?~/\\
        /==><=>=\->|-!?~/\\/==><=>=\-
           >|-!?~/\\/==><=>=\->|-!
                ?~/\\/==><=>=
```

## Why these characters

They are not chosen by taste. Ten of them are what `modules/logic/.../Notation.scala` declares --
the two junctions, implication, equivalence, equality, negation, the two quantifiers, the lambda
and the function arrow -- and the eleventh is the turnstile `Show.scala` prints in front of a
theorem. In that order:

    |-   !   ?   ~   /\   \/   ==>   <=>   =   \   ->

concatenated into one nineteen-character stream, `|-!?~/\\/==><=>=\->`, which then runs through the
figure. A first pass used `⊢` and `σ`, which are the right symbols for a reader and the wrong ones
for this system, because this system does not read them. Being all ASCII also removes a caveat that
pass carried: those two glyphs are East Asian Ambiguous, so the alignment depended on how the
terminal chose to width them.

**The same argument is why the figure is not drawn in box-drawing characters or half blocks**,
which would buy smoother curves and twice the vertical resolution at a smaller size. Both stop the
interior being the operators this system reads, which is the whole idea, so the size was paid
instead.

## What makes a copy correct

**The stream is continuous and it advances only over the cells that are filled.** It does not
restart at each row, and it skips the hollow interior rather than counting it. That is what makes
the figure read as text poured into a letter rather than as a repeated motif, and it is also the
check: fill the visible cells in reading order with the stream above, and every one of the 947
cells must land on the character it already has. A single cell wrong anywhere and the last row
stops matching.

Run that check before trusting a copy that has been through an editor, a chat window or a
clipboard. Backslashes are what get eaten.

## Why it is this big, which is the decision rather than an accident

Twenty-three rows by eighty-five columns, so it does **not** fit an eighty-column terminal. That is
bought rather than overlooked, and what it buys is the tail.

The first version was eleven rows, and its tail was a two-row rectangle running dead level from the
ring to the right edge: a slab glued to a circle, not a letter. Bending it is where the size went.
At two rows of thickness the smallest wave a character grid can express moves the stroke by one
row, which is **half the stroke's own thickness**, and the result reads as a break rather than as a
bend. Four profiles were drawn at that size -- a rise halfway, a curl at the tip, a dip in the
middle, a dip with a lift -- and every one of them tore the stroke somewhere. Filleting the
transition columns to three rows did not save it either.

So the grid was doubled. The stroke is six rows, a two-row wave moves it by a third of its
thickness, and the figure holds together. Nothing about the profile fixes this at the old size;
only the resolution does.

## How the figure is built

A ring, and one stroke that leaves it.

The **ring** is an annulus: the cells inside an outer ellipse and outside an inner one. A terminal
cell is about twice as tall as it is wide, so every column radius is twice its row radius and the
result is a circle rather than an oval. The outer boundary is tested half a row and one column
wider than the radius it names, which is not decoration: sampling an ellipse cell by cell puts
exactly **one** cell in its topmost row, and that reads as a pimple on the top of the stroke.

The **stroke** starts at the ring's shoulder rather than at its apex, which is where a sigma starts
it, and that is what keeps the hole open. Starting it at the apex was tried first: the stroke's
band and the ring's arc then diverge as the arc falls away, the union fills the whole upper-right
quadrant, and the counter closes up. From the shoulder it runs right, sags by two rows over one
half-cosine so that it leaves and rejoins the level flat rather than at a corner, and lifts into
its terminal over the last third.

## Shapes drawn and rejected

Recorded so they are not re-proposed as new.

A **banded** interior, where each row restarts at `|-`: tidier, and colder. A **two-halves** one,
with `?` on the left of the ring and `|-` on the right, the half that proposes and the half that
certifies, which is `adr/0003` drawn; the detail that bites there is that the dividing column is
the centre of the **ring**, not of the image, so passing it as a constant fills the right flank
with the left glyph as soon as the size changes. A tail **rising** steadily instead of sagging,
which reads as a ramp: the mark looks like it is climbing rather than curling.

## `logo.svg`

The same grid, one `<text>` element per visible run, monospace. It is a transcription of the art
above rather than a redrawing: row *n* of the file is row *n* of the art, so the two cannot drift
without it being visible in a diff.

## The colour, which is the one thing a static file gets wrong

Rendered inside an `<img>`, as a README does, the file gets no colour from the page around it.
`fill="currentColor"` alone therefore resolves to black, and the mark is black on black on every
dark page; that is what it did on GitHub the day it landed. The attribute stays, because it is the
right answer when the file is inlined into a document that has a colour. What answers otherwise is
a stylesheet inside the file, and it has three values rather than two: a mid grey as the bare one,
because a preference query that does not resolve has to leave the mark legible on a white page and
on a black one, and the good light and dark values under their own queries.

The query is the **browser's** preference and not the site's. Somebody reading GitHub in dark mode
from a light desktop gets the grey, which is the reason the grey is not one of the extremes.

## What is not here

A size that fits a terminal. The eighty-column version is a separate mask and not a scaling of
this one: at under twenty rows the ring's top arc breaks up, which was measured rather than
guessed, so it wants drawing rather than shrinking. The SVG scales freely, so this is a
terminal-only gap.
