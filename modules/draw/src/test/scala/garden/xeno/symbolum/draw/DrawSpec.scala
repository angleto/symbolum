package garden.xeno.symbolum.draw

import java.nio.file.Files
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The cells drawn, against simulations that share no code with the ones that drew them.
 *
 * Each reference below is written the way a reader would check the panel by hand rather than the
 * way `Evolution` computes it: Rule 30 as the formula `l XOR (c OR r)` over an array padded wide
 * enough that its edges never matter, instead of a bit of the number 30; the XOR rule from one cell
 * as Pascal's triangle modulo 2 by Lucas's theorem, with no evolution at all; and Gilbreath's table
 * as differences of a list of primes found by a sieve. Agreement with a reference built the same
 * way as the code would test nothing, which is the trap `MarkSpec` avoids for the logo by checking
 * the drawing against the art rather than against the code that drew it.
 */
class DrawSpec extends AnyFlatSpec with Matchers {

  private def force[A](result: Either[String, A]): A = result.fold(e => fail(e), identity)

  private lazy val panels: Vector[Panel] = force(Draw.Figures("gilbreath-vs-rule30"))
  private def named(prefix: String): Panel = panels.find(_.title.startsWith(prefix)).getOrElse(fail(prefix))

  /* ------------------------------------------------------------ the evolutions, against references */

  "Rule 30 from one cell" should "be l XOR (c OR r) at every cell of the panel" in {
    val panel = named("Rule 30")
    val steps = panel.steps.size
    val width = 2 * steps + 3
    // Position x sits at index x + steps + 1, so the light cone of 299 steps never reaches an edge.
    val reference = Vector.iterate(Vector.tabulate(width)(i => if (i == steps + 1) 1 else 0), steps) { row =>
      Vector.tabulate(width)(i =>
        if (i == 0 || i == width - 1) 0 else row(i - 1) ^ (row(i) | row(i + 1))
      )
    }
    val wrong = for {
      t <- panel.steps
      x <- panel.positions
      if panel.drawn(t, x) != reference(t)(x + steps + 1)
    } yield (t, x)
    wrong shouldBe empty
    // And the panel is not empty, which an all-zero drawing would also agree with nowhere.
    panel.steps.map(t => panel.positions.count(panel.drawn(t, _) == 1)).sum should be > 10000
  }

  "The XOR rule from one cell" should "be Pascal's triangle modulo 2, by Lucas's theorem" in {
    val panel = named("XOR rule from one")
    // C(t, k) is odd exactly when every bit of k is a bit of t, and position -k holds C(t, k).
    val wrong = for {
      t <- panel.steps
      x <- panel.positions
      expected = if (x <= 0 && -x <= t && ((t & -x) == -x)) 1 else 0
      if panel.drawn(t, x) != expected
    } yield (t, x)
    wrong shouldBe empty
  }

  "Gilbreath's table" should "be the iterated absolute differences of the primes a sieve finds" in {
    val panel = named("Absolute differences")
    val sieved = (2 to 5000).filter(n => (2 to math.sqrt(n.toDouble).toInt).forall(n % _ != 0)).take(601).toVector
    val table = Vector.iterate(sieved, 301)(r => r.zip(r.tail).map((a, b) => math.abs(b - a)))
    val wrong = for {
      k <- panel.steps
      i <- panel.positions
      if panel.drawn(k, i) != table(k)(i)
    } yield (k, i)
    wrong shouldBe empty
    // The column the conjecture is about, read off the drawing: 1 in every row from the first.
    panel.steps.map(panel.drawn(_, 0)).toSet shouldBe Set(1)
  }

  it should "start from the prime gaps, so the first row drawn is not the primes themselves" in {
    named("Absolute differences").steps.start shouldBe 1
    (0 until 6).map(named("Absolute differences").drawn(1, _)).toVector shouldBe Vector(1, 2, 2, 4, 2, 4)
  }

  "The XOR rule from a random row" should "draw the same row for the same seed and a different one for another" in {
    val (first, _) = Start.random(900, 30)
    Start.random(900, 30)._1 shouldBe first
    Start.random(900, 31)._1 should not be first
    // Not a test of randomness: a generator returning a constant would pass the two lines above.
    first.cells.count(_ == 1) should (be > 400 and be < 500)
  }

  it should "lose a cell on the right at each step, since nothing past the row is known" in {
    val panel = named("XOR rule from a random")
    panel.evolution.rows.map(_.cells.size).take(3) shouldBe Vector(900, 899, 898)
    panel.evolution.rows.map(_.first).toSet shouldBe Set(0)
  }

  /* ------------------------------------------------------------ the refusals */

  "An evolution" should "refuse an endless row under a rule that changes the zeros around it" in {
    // Rule 1 takes 000 to 1: the line outside the row turns on, which a finite row cannot hold.
    Evolution.of(force(Rule.elementary(1)), Edge.Endless, Start.Cell._1, 3).left.map(_.contains("zeros")) shouldBe
      Left(true)
    Evolution.of(force(Rule.elementary(1)), Edge.Finite, Start.Cell._1, 3).isRight shouldBe true
  }

  it should "refuse a rule on bits over a row holding other values" in {
    Evolution.of(Rule.Xor, Edge.Finite, Start.primes(5)._1, 2).left.map(_.contains("0 and 1")) shouldBe Left(true)
  }

  it should "refuse a rule number past 255 and a negative number of steps" in {
    Rule.elementary(256).isLeft shouldBe true
    Rule.elementary(-1).isLeft shouldBe true
    Evolution.of(Rule.Xor, Edge.Endless, Start.Cell._1, -1).isLeft shouldBe true
  }

  "A start" should "write a number's bits most significant first and refuse a negative one" in {
    force(Start.bits(BigInt(6)))._1 shouldBe Row(0, Vector(1, 1, 0))
    Start.bits(BigInt(-6)).isLeft shouldBe true
  }

  /* ------------------------------------------------------------ the document */

  "The SVG" should "hold every cell of every panel in its colour, read back from the document" in {
    val svg = force(Svg.render(panels, columns = 2))
    val group =
      """(?s)data-title="([^"]*)">.*?data-steps="(-?\d+):(-?\d+)" data-positions="(-?\d+):(-?\d+)" data-cell="(\d+)">(.*?)</g>""".r
    val path = """<path fill="([^"]+)" d="([^"]*)"/>""".r
    val rectangle = """M(\d+) (\d+)h(\d+)v\d+h-\d+z""".r

    // (title) -> (step, position) -> colour, for every cell some path covers.
    val read = group.findAllMatchIn(svg).map { g =>
      val (firstStep, firstPosition, cell) = (g.group(2).toInt, g.group(4).toInt, g.group(6).toInt)
      val cells = for {
        p <- path.findAllMatchIn(g.group(7)).toVector
        r <- rectangle.findAllMatchIn(p.group(2)).toVector
        offset <- 0 until r.group(3).toInt / cell
      } yield (firstStep + r.group(2).toInt / cell, firstPosition + r.group(1).toInt / cell + offset) -> p.group(1)
      // A cell covered twice would be drawn in whichever colour came last, so it is a defect too.
      cells.map(_._1).distinct.size shouldBe cells.size
      g.group(1) -> cells.toMap
    }.toMap

    read.keySet shouldBe panels.map(_.title).toSet
    val wrong = for {
      panel <- panels
      t <- panel.steps
      x <- panel.positions
      expected = panel.palette.colour(panel.drawn(t, x)).getOrElse(fail(s"no colour at ($t, $x)"))
      if read(panel.title).getOrElse((t, x), Palette.Surface) != expected
    } yield s"${panel.title} at ($t, $x)"
    wrong shouldBe empty
    // Not vacuous: the cells some path covers are most of the figure, not a handful.
    read.values.map(_.size).sum should be > 100000
  }

  it should "give each palette one named line of legend, since two of them colour 1 differently" in {
    val svg = force(Svg.render(panels, columns = 2))
    """data-palette="([^"]+)"""".r.findAllMatchIn(svg).map(_.group(1)).toVector shouldBe
      Vector("differences", "automaton")
  }

  it should "make each column as wide as its own widest panel, not the figure's" in {
    // The left column holds the table (300 positions) and Rule 30 (601), the right one the two XOR
    // panels (300 and 301): a layout taking the widest panel for every column would be 1234 wide.
    val svg = force(Svg.render(panels, columns = 2))
    val width = """<svg[^>]* width="(\d+)"""".r.findFirstMatchIn(svg).map(_.group(1).toInt).getOrElse(fail("no width"))
    width shouldBe 16 + (601 * Svg.Cell + 16) + (301 * Svg.Cell + 16)
  }

  it should "be small enough to attach to a note, which one rect per run was not" in {
    force(Svg.render(panels, columns = 2)).length should be < 3000000
  }

  it should "refuse a value its palette has no colour for, rather than draw it as the surface" in {
    val twos = Panel("twos", force(Evolution.of(Rule.AbsoluteDifference, Edge.Finite, Row(0, Vector(0, 2)), 0)),
      Palette.Binary, 0 until 1, 0 until 2)
    Svg.render(Vector(twos), 1).left.map(_.contains("no colour")) shouldBe Left(true)
  }

  it should "refuse a figure with no panel, and one with no column" in {
    Svg.render(Vector.empty, 1).isLeft shouldBe true
    Svg.render(Vector(named("Rule 30")), 0).left.map(_.contains("column")) shouldBe Left(true)
  }

  /* ------------------------------------------------------------ the command */

  "The command" should "write the named figure, and say what it wrote" in {
    val out = Files.createTempFile("draw", ".svg")
    try {
      val said = force(Draw.run(Vector(out.toString, "gilbreath-vs-rule30")))
      said should include("4 panel(s)")
      Files.readString(out) should startWith("<svg")
    } finally Files.deleteIfExists(out)
  }

  it should "draw panels described on the command line, separated by |" in {
    val described = force(Draw.figure(Vector("rule=30", "start=cell", "steps=4", "|", "rule=xor", "start=bits:5", "steps=2", "title=five")))
    described.map(_.title) shouldBe Vector("Rule 30, cell", "five")
    described(0).positions shouldBe (-4 until 5)
  }

  it should "say what is wrong with a panel it cannot read" in {
    Draw.figure(Vector("rule=30", "start=cell")).left.map(_.contains("steps=")) shouldBe Left(true)
    Draw.figure(Vector("rule=31", "start=cell", "steps=2", "colour=red")).left.map(_.contains("colour")) shouldBe Left(true)
    Draw.figure(Vector("rule=30", "start=nowhere", "steps=2")).left.map(_.contains("start=")) shouldBe Left(true)
    Draw.figure(Vector("rule=30", "start=cell", "steps=2", "rows=5:1")).left.map(_.contains("FROM:UNTIL")) shouldBe Left(true)
    Draw.figure(Vector("rule=30", "start=cell", "steps")).left.map(_.contains("key=value")) shouldBe Left(true)
    Draw.run(Vector("only-a-file.svg")).left.map(_.contains("usage")) shouldBe Left(true)
  }

  it should "refuse each word it cannot read as what its key wants, naming the word" in {
    // One case per reading, because each is a separate place a word is turned into a value and a
    // refusal reached by one says nothing about the others.
    Draw.figure(Vector("|", "|")).left.map(_.contains("gilbreath-vs-rule30")) shouldBe Left(true)
    Draw.figure(Vector("rule=thirty", "start=cell", "steps=2")).left.map(_.contains("rule=thirty")) shouldBe Left(true)
    Draw.figure(Vector("rule=30", "start=cell", "steps=-2")).left.map(_.contains("-2")) shouldBe Left(true)
    Draw.figure(Vector("rule=xor", "start=random:9:often", "steps=2")).left.map(_.contains("often")) shouldBe Left(true)
    Draw.figure(Vector("rule=xor", "start=bits:six", "steps=2")).left.map(_.contains("bits:six")) shouldBe Left(true)
  }

  it should "say it could not write the file rather than throw" in {
    // A path under a regular file cannot be created on any platform this runs on.
    val file = Files.createTempFile("draw", ".svg")
    try {
      Draw.run(Vector(file.resolve("under-a-file.svg").toString, "rule=30", "start=cell", "steps=2"))
        .left.map(_.contains("could not write")) shouldBe Left(true)
    } finally Files.deleteIfExists(file)
  }
}
