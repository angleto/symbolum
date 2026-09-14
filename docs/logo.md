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
                |-!?~/\\/==><                                              =>=
           \->|-!?~/\\/==><=>=\->|                                     -!?~/\\/
        ==><=>=\->|-!?~/\\/==><=>=\->                              |-!?~/\\/==><
      =>=\->|-!?~/\\/==><=>=\->|-!?~/\\                        /==><=>=\->|-
    !?~/\\/==><=>=\->|-!?~/\\/==><=>=\->|-                 !?~/\\/==><=>
   =\->|-!?~/\\/==         ><=>    =\->|-!?~/          \\/==><=>=\->
  |-!?~/\\/==>                <=>    =\->|-!?~/\   \/==><=>=\->|
 -!?~/\\/==>                    <=>=    \->|-!?~/\\/==><=>=\
->|-!?~/\\/                       ==><=    >=\->|-!?~/\\
/==><=>=\-                          >|-!?     ~/\\/=
=><=>=\->|                           -!?~/
\\/==><=>=                           \->|-!
?~/\\/==><                          =>=\->|-
!?~/\\/==>                         <=>=\->|-!
?~/\\/==><=                       >=\->|-!?~/
 \\/==><=>=\                     ->|-!?~/\\/
  ==><=>=\->|-                 !?~/\\/==><=
   >=\->|-!?~/\\/=         =><=>=\->|-!?~/
    \\/==><=>=\->|-!?~/\\/==><=>=\->|-!?~
      /\\/==><=>=\->|-!?~/\\/==><=>=\->
        |-!?~/\\/==><=>=\->|-!?~/\\/=
           =><=>=\->|-!?~/\\/==><=
                >=\->|-!?~/\\
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
restart at each row, and it skips the counter and the slot rather than counting them. That is what
makes the figure read as text poured into a letter rather than as a repeated motif, and it is also
the check: fill the visible cells in reading order with the stream above, and every one of the 654
cells must land on the character it already has. A single cell wrong anywhere and the last row
stops matching.

**Two further checks are about the shape rather than the text, and the stream cannot see either.**
The mark is **one** connected region, and it encloses **exactly one** empty region, the counter, of
269 cells. The slot that separates the folded tip from the bar's left arm is open at the bottom and
must stay open: when it closes it leaves sealed pockets of three and two cells, which read as dirt
rather than as drawing. That is not hypothetical. It is what the first hand-drawn version of this
figure did, and filling those five cells is the only edit made to it.

All three are asserted by `MarkSpec`, so they run on every `sbt test` rather than when somebody
remembers them. Run them by eye anyway on a copy that has been through an editor, a chat window or a
clipboard, because such a copy is usually not in this repository yet. Backslashes are what get
eaten.

## Why it is this big, which is the decision rather than an accident

Twenty-three rows by eighty columns, which is the widest a figure can be and still be pasted into
an eighty-column terminal. The last three columns were bought back rather than spent: the mark was
eighty-three columns when it was drawn, and the V's right arm is cut three columns shorter than it
was for no reason except that one. What the size itself buys has changed: it used to be the bend in
the tail, and it is now the closure.

The stroke is five rows where it is at full weight, and that is a measurement rather than an
intention: five cells at the top of the circle and five at the bottom, ten columns on the left
flank, a column being half a row. Where the stroke closes it thins to three columns, and the slot
between its tip and the bar's left arm is three columns at its narrowest. Halve the grid and both
go under one cell. The fold and the slot then disappear together and what is left is a ring with a
bar laid across it, which is precisely the figure this one replaced.

The size itself is inherited, and the reason it was paid is worth keeping. The first version was
eleven rows with a two-row stroke. At that thickness the smallest wave a character grid can express
moves the stroke by **half its own thickness**, and the result reads as a break rather than as a
bend; four profiles were drawn at that size and every one tore the stroke somewhere. Doubling the
grid is what fixed it, and nothing about the drawing could have.

## How the figure is built

One stroke for the circle, one for the bar, and a slot between them.

The **circle** is a band about a centre circle. A terminal cell is about twice as tall as it is
wide, so a column counts half a row and the figure comes out round rather than oval. Coming up the
right side the band does two things at once: it thins, and it leaves the outline. The last of it
therefore runs **inward** rather than along the circumference, and stops in a square cut at about
eleven o'clock, so the tip points at the centre. That is the whole difference between a stroke that
closes a circle and one that merely stops on it, and it is the only way the closure can be seen at
all: a closed annulus has no end to show.

The **bar** is bent into a V: a left arm out of the circle's shoulder going down to the right, a
vertex, and a longer arm rising to the top right and cut square. Both bends are corners, not arcs.

The **slot** between the folded tip and the left arm is what makes the fold legible. It is closed at
the top, where the circle's band and the arm meet, and open at the bottom. Close it and the tip
merges with the arm and the fold is invisible, which is what every earlier attempt at this closure
did.

The **terminal** is a straight band and not an arc, which is the one thing about the figure that
looks like a compromise and is not. At this resolution the last four cells of a curve and of a
straight line are the same four cells, and the straight one is two numbers where the curve was five.

**The figure is a description and the art is its rasterisation.** That was not true when it was
drawn: the mask was placed cell by cell, because a fold drawn as a spiral wants four to five times
the stroke's own width of clear counter to turn in and this one has two and a half, and six
parametric shapes tried at the time each hid the fold under the bar, opened the counter, or left
holes of one and two cells where the stroke pinched. What answered was the straight terminal above.
`Figure` in `modules/mark` is the description, in radii rather than in cells, and `Figure.at(rows)`
is the art at a size.

It reproduces the drawing **within four cells**: the terminal's run at row five and the bar's run at
row seven each sit one column further right in the hand-drawn version than in this one. Those four
are the price of having one source instead of two, and they are written here rather than absorbed
quietly, because somebody comparing this figure against the one in an older commit will find exactly
that difference and deserves to know it was paid on purpose.

**Not every size holds.** The slot is three columns at the reference and it is what a rasterisation
loses first, so the command refuses rather than writing a figure whose checks fail: at twenty-six
rows the counter leaks away entirely and at forty-six a pocket seals, while twenty, twenty-three and
thirty-three hold. `MarkSpec` asserts all five of those. `sbt "mark/runMain
garden.xeno.symbolum.mark.Mark 33"` prints a size and writes nothing, because another size is a
thing to look at before it is a thing to commit.

## Shapes drawn and rejected

Recorded so they are not re-proposed as new.

A **banded** interior, where each row restarts at `|-`: tidier, and colder. A **two-halves** one,
with `?` on the left of the circle and `|-` on the right, the half that proposes and the half that
certifies, which is `adr/0003` drawn; the detail that bites there is that the dividing column is
the centre of the **circle**, not of the image, so passing it as a constant fills the right flank
with the left glyph as soon as the size changes.

The figure this one replaced is itself on the list: a closed annulus of six rows with a tail that
left the shoulder, sagged over a half-cosine and lifted into a blunt terminal at the right edge. It
was rejected for what it could not say. A closed annulus has no end, so nothing about it closes;
the tail's terminal was a cut against the frame rather than a finish. Two repairs to it failed
before the figure was redrawn: a tail **tapering to a point**, which reads as pointing up and away
rather than inward, and the same taper with a **rounded** lift, which at this resolution is
indistinguishable from the sag it was meant to answer. The V is what a corner buys over an arc on a
character grid, which is that the eye can see where it is.

## `logo.svg`

The same grid, one `<text>` element per visible run, monospace. It is a transcription of the art
above rather than a redrawing: row *n* of the file is row *n* of the art.

**Both files are generated.** `sbt "mark/runMain garden.xeno.symbolum.mark.Mark"` writes the art
into the block above from the description, and this drawing from the art; `MarkSpec` fails when
either committed file is not what that command would write, naming the command. This paragraph used to end "so the two cannot drift without it being visible in a diff",
which was true and was not a check: a diff is something a person has to read, and the moment
somebody edits one cell of the art is the moment they have least appetite for finding out how the
drawing is produced. The predictable outcome is a hand-edited `<text>` element, and from there the
drawing stops being a transcription and becomes a copy that resembles one.

The generator refuses rather than writing when the art fails any of the three checks above. A
drawing of a broken figure would put the defect in two files instead of one, and the second is the
file nobody reads.

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

A way to know which sizes hold without drawing them. The description is resolution-independent and
the rasterisation is not: whether the slot survives a given grid is decided by where the cell centres
happen to fall, and the only instrument for that is the three checks above, run on the result. So the
command draws and then reports, and this document names the five sizes somebody has measured rather
than a rule.

This section used to say that no size but one existed at all, and before that that no size fitting a
terminal existed. Both are answered, and what replaced them is a smaller claim honestly: the mark has
sizes, and which ones is a question you ask by asking.
