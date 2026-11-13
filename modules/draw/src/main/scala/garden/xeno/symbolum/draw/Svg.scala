package garden.xeno.symbolum.draw

/** A colour for one value, and what the legend calls it. */
final case class Swatch(value: Int, colour: String, label: String)

/**
 * Which colour each value is drawn in.
 *
 * `above` takes every value greater than the largest one listed, which is how a table of
 * differences shows "something other than 0, 1 or 2" without a colour per value. A value with no
 * swatch and nothing above is not drawn, and since the background is the colour of 0 in both
 * palettes here, a value nobody listed would read as 0: [[Svg.render]] refuses a figure holding one.
 */
final case class Palette(name: String, swatches: Vector[Swatch], above: Option[Swatch]) {

  /** The colour of a value, or nothing where this palette does not say. */
  def colour(value: Int): Option[String] =
    swatches.find(_.value == value).map(_.colour).orElse(
      above.filter(_ => swatches.nonEmpty && value > swatches.map(_.value).max).map(_.colour)
    )
}

object Palette {

  /** The surface every panel is drawn on, which is also the colour of 0. */
  val Surface: String = "#fcfcfb"

  /** On and off, for an automaton. */
  val Binary: Palette =
    Palette("automaton", Vector(Swatch(0, Surface, "off"), Swatch(1, "#2a78d6", "on")), None)

  /**
   * The colours of the note's figure for a table of differences: 1 is Gilbreath's column, 2 is
   * what most of the table is, and anything larger is the irregular strip near the top.
   */
  val Differences: Palette = Palette(
    "differences",
    Vector(
      Swatch(0, Surface, "0"),
      Swatch(1, "#eb6834", "1"),
      Swatch(2, "#2a78d6", "2")
    ),
    Some(Swatch(3, "#1baf7a", "greater than 2"))
  )
}

/**
 * One panel: an evolution seen through a window of steps and positions.
 *
 * `steps` and `positions` are half-open ranges of true coordinates. A cell the evolution does not
 * reach inside the window is left as the surface, which is the colour of 0, so a window wider than
 * the row reads as zeros around it; that is the reading the endless edge has anyway, and for a
 * finite row it is the blank the note's figure showed below its diagonal.
 */
final case class Panel(
  title: String,
  evolution: Evolution,
  palette: Palette,
  steps: Range,
  positions: Range
) {

  /** The value drawn at a step and a position of the window, the surface counting as 0. */
  def drawn(step: Int, position: Int): Int = evolution.at(step, position).getOrElse(0)
}

/** Writing panels as one SVG document. */
object Svg {

  /** The side of one cell, in pixels. */
  val Cell: Int = 2

  private val Margin = 16
  private val TitleHeight = 22
  private val LegendRow = 22
  private val LegendName = 110
  private val LegendEntry = 150
  private val LegendWidth = LegendName + 4 * LegendEntry
  private val Ink = "#1a1a19"

  /**
   * The document, or the first reason it cannot be drawn faithfully.
   *
   * Each row of a panel is written as runs, a maximal stretch of one colour, and the surface is not
   * written at all. All the runs of one colour in a panel are one `path`, in the window's own
   * coordinates, and the group holding them says which steps and positions the window starts at and
   * how wide a cell is. That is what lets a reader of the document, the spec among them, recover
   * every cell without reversing the layout. One `rect` per run, with its coordinates as
   * attributes, was the first version: the note's figure came to 9 184 372 characters that way.
   */
  def render(panels: Vector[Panel], columns: Int): Either[String, String] = {
    val unlisted = for {
      panel <- panels
      step <- panel.steps
      position <- panel.positions
      value = panel.drawn(step, position)
      if panel.palette.colour(value).isEmpty
    } yield s"${panel.title}: the value $value at step $step, position $position has no colour"

    if (panels.isEmpty) Left("a figure needs at least one panel")
    else if (columns < 1) Left(s"a figure has at least one column, and $columns is fewer")
    else if (unlisted.nonEmpty) Left(unlisted.head)
    else Right(document(panels, columns))
  }

  private def document(panels: Vector[Panel], columns: Int): String = {
    // Each column as wide as its widest panel and each row as tall as its tallest, so a narrow panel
    // beside a wide one does not leave the width of the wide one empty in every other column.
    val grid = panels.grouped(columns).toVector
    val widths = (0 until columns).map(c => grid.flatMap(_.lift(c)).map(_.positions.size * Cell + Margin).maxOption.getOrElse(0))
    val heights = grid.map(row => row.map(_.steps.size * Cell).max + TitleHeight + Margin)
    val lefts = widths.scanLeft(Margin)(_ + _)
    val tops = heights.scanLeft(Margin)(_ + _)
    val palettes = panels.map(_.palette).distinctBy(_.name)
    val width = math.max(lefts.last, Margin + LegendWidth)
    val height = tops.last + palettes.size * LegendRow + Margin

    val bodies = panels.zipWithIndex.map { case (panel, index) =>
      panelAt(panel, lefts(index % columns), tops(index / columns))
    }
    // One line per palette, named, because two palettes may give one value two colours: `1` is
    // Gilbreath's column in a table of differences and a live cell in an automaton.
    val legend = palettes.zipWithIndex.map { case (palette, line) =>
      val y = tops.last + line * LegendRow
      val entries = (palette.swatches ++ palette.above).zipWithIndex.map { case (swatch, index) =>
        val x = Margin + LegendName + index * LegendEntry
        s"""    <rect x="$x" y="$y" width="14" height="14" fill="${swatch.colour}" stroke="#c3c2b7"/>""" + "\n" +
          s"""    <text x="${x + 20}" y="${y + 12}" font-size="13" fill="$Ink">${escape(swatch.label)}</text>"""
      }
      (s"""  <g data-palette="${escape(palette.name)}">""" +: (s"""    <text x="$Margin" y="${y + 12}" font-size="13" fill="$Ink">${escape(palette.name)}</text>""" +: entries) :+ "  </g>").mkString("\n")
    }

    (Vector(
      s"""<svg xmlns="http://www.w3.org/2000/svg" width="$width" height="$height" viewBox="0 0 $width $height">""",
      s"""  <rect width="$width" height="$height" fill="${Palette.Surface}"/>"""
    ) ++ bodies ++ legend :+ "</svg>").mkString("", "\n", "\n")
  }

  private def panelAt(panel: Panel, left: Int, top: Int): String = {
    // Every run of one colour in the panel, as `(colour, row index, run)`.
    val runs = for {
      (step, row) <- panel.steps.zipWithIndex.toVector
      run <- runsOf(panel.positions.map(panel.drawn(step, _)).toVector)
      colour <- panel.palette.colour(run.value).filter(_ != Palette.Surface)
    } yield (colour, row, run)

    // One path per colour, each run a rectangle `M x y h w v cell h -w z` in the window's own
    // coordinates, so that what a reader of the document needs is the window and the cell size,
    // which the enclosing group states, and none of the layout around it.
    val paths = runs.groupBy(_._1).toVector.sortBy(_._1).map { case (colour, ofColour) =>
      val d = ofColour.map { case (_, row, run) =>
        s"M${run.start * Cell} ${row * Cell}h${run.count * Cell}v${Cell}h-${run.count * Cell}z"
      }.mkString
      s"""      <path fill="$colour" d="$d"/>"""
    }
    (Vector(
      s"""  <g transform="translate($left,$top)" data-title="${escape(panel.title)}">""",
      s"""    <text x="0" y="15" font-size="14" fill="$Ink">${escape(panel.title)}</text>""",
      s"""    <g transform="translate(0,$TitleHeight)" data-steps="${panel.steps.start}:${panel.steps.end}" """ +
        s"""data-positions="${panel.positions.start}:${panel.positions.end}" data-cell="$Cell">"""
    ) ++ paths ++ Vector("    </g>", "  </g>")).mkString("\n")
  }

  /** A maximal stretch of one value, by its index in the window's row. */
  private final case class Run(start: Int, count: Int, value: Int)

  private def runsOf(values: Vector[Int]): Vector[Run] =
    values.zipWithIndex.foldLeft(Vector.empty[Run]) { case (acc, (value, index)) =>
      acc.lastOption match {
        case Some(last) if last.value == value => acc.init :+ last.copy(count = last.count + 1)
        case _ => acc :+ Run(index, 1, value)
      }
    }

  private def escape(text: String): String =
    text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;")
}
