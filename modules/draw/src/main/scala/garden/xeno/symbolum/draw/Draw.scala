package garden.xeno.symbolum.draw

import java.nio.file.{Files, Path, Paths}

/**
 * Draws cellular automata and tables of differences as an SVG, panels side by side.
 *
 * {{{
 * tools/sbt "draw/runMain garden.xeno.symbolum.draw.Draw out.svg gilbreath-vs-rule30"
 * tools/sbt "draw/runMain garden.xeno.symbolum.draw.Draw out.svg rule=30 start=cell steps=100 | rule=xor start=cell steps=100"
 * }}}
 *
 * The first argument is the file written. What follows is either the name of a figure this file
 * holds, or panels separated by `|`, each a list of `key=value`:
 *
 *   - `rule`: a Wolfram number from 0 to 255, `xor` (the cell XOR its right neighbour) or
 *     `difference` (the absolute difference of the cell and its right neighbour).
 *   - `start`: `cell`, `random:WIDTH:SEED`, `primes:COUNT` or `bits:N`. The start decides the edge,
 *     because it decides what lies past the row: a single cell and a number's bits sit on an
 *     endless line of zeros, and a random row and the primes are prefixes of something unknown.
 *   - `steps`: how many rows after the start are computed.
 *   - `rows` and `columns`: the window, as `FROM:UNTIL` in true coordinates, half open. By default
 *     every row, and the positions the evolution ever reaches.
 *   - `title`: the panel's title, with `_` for a space since the shell has already split on spaces.
 *
 * A figure drawn here proves nothing and is not meant to: this module depends on nothing and sits
 * outside the graph whose direction is the correctness argument, for the reason `mark` does.
 */
object Draw {

  /** How the command is called, written once so the usage message and the docstring agree. */
  val Command: String = "tools/sbt \"draw/runMain garden.xeno.symbolum.draw.Draw OUT.svg (FIGURE | PANEL [| PANEL]...)\""

  def main(args: Array[String]): Unit =
    run(args.toVector) match {
      case Right(message) => println(message)
      case Left(refusal) =>
        System.err.println(s"draw: $refusal")
        sys.exit(1)
    }

  /** The command without the process: what it wrote, or why it wrote nothing. */
  def run(args: Vector[String]): Either[String, String] =
    args match {
      case out +: rest if rest.nonEmpty =>
        for {
          panels <- figure(rest)
          svg <- Svg.render(panels, columns = math.min(panels.size, 2))
          path <- write(Paths.get(out), svg)
        } yield s"wrote $path: ${panels.size} panel(s), ${svg.length} characters"
      case _ => Left(s"usage: $Command")
    }

  private def write(path: Path, svg: String): Either[String, Path] =
    scala.util.Try(Files.writeString(path, svg)).toEither.left.map(e => s"could not write $path: ${e.getMessage}")

  /** The panels the arguments after the file name describe. */
  def figure(words: Vector[String]): Either[String, Vector[Panel]] =
    words match {
      case Vector(name) if Figures.contains(name) => Figures(name)
      case _ =>
        val specs = words.mkString(" ").split('|').toVector.map(_.trim).filter(_.nonEmpty)
        if (specs.isEmpty) Left(s"no panel described; the figures here are ${Figures.keys.toVector.sorted.mkString(", ")}")
        else sequence(specs.map(panel))
    }

  /** One panel from its `key=value` words. */
  def panel(spec: String): Either[String, Panel] = {
    val pairs = spec.split("\\s+").toVector.filter(_.nonEmpty).map(_.split("=", 2).toVector)
    pairs.find(_.size != 2) match {
      case Some(word) => Left(s"`${word.mkString}` is not key=value")
      case None =>
        val written = pairs.map(p => p(0) -> p(1)).toMap
        val unknown = written.keySet -- Keys
        if (unknown.nonEmpty) Left(s"unknown key(s) ${unknown.toVector.sorted.mkString(", ")}; the keys are ${Keys.toVector.sorted.mkString(", ")}")
        else
          for {
            ruleText <- written.get("rule").toRight("a panel needs rule=")
            rule <- ruleNamed(ruleText)
            startText <- written.get("start").toRight("a panel needs start=")
            start <- startNamed(startText)
            steps <- written.get("steps").toRight("a panel needs steps=").flatMap(number("steps", _))
            evolution <- Evolution.of(rule, start._2, start._1, steps)
            rows <- written.get("rows").map(range("rows", _)).getOrElse(Right(0 until steps + 1))
            columns <- written.get("columns").map(range("columns", _)).getOrElse(Right(reach(evolution)))
          } yield Panel(
            written.get("title").map(_.replace('_', ' ')).getOrElse(s"${rule.name}, $startText"),
            evolution,
            if (rule.bits) Palette.Binary else Palette.Differences,
            rows,
            columns
          )
    }
  }

  private val Keys = Set("rule", "start", "steps", "rows", "columns", "title")

  private def ruleNamed(text: String): Either[String, Rule] =
    text match {
      case "xor" => Right(Rule.Xor)
      case "difference" => Right(Rule.AbsoluteDifference)
      case _ =>
        text.toIntOption.toRight(s"rule=$text is not a number from 0 to 255, xor or difference").flatMap(Rule.elementary)
    }

  private def startNamed(text: String): Either[String, (Row, Edge)] =
    text.split(':').toVector match {
      case Vector("cell") => Right(Start.Cell)
      case Vector("random", width, seed) =>
        for {
          w <- number("random's width", width)
          s <- seed.toLongOption.toRight(s"random's seed $seed is not a number")
        } yield Start.random(w, s)
      case Vector("primes", count) => number("primes' count", count).map(Start.primes)
      case Vector("bits", n) =>
        scala.util.Try(BigInt(n)).toOption.toRight(s"bits:$n is not a number").flatMap(Start.bits)
      case _ => Left(s"start=$text is not cell, random:WIDTH:SEED, primes:COUNT or bits:N")
    }

  private def number(what: String, text: String): Either[String, Int] =
    text.toIntOption.filter(_ >= 0).toRight(s"$what wants a whole number that is not negative, and $text is not one")

  private def range(what: String, text: String): Either[String, Range] =
    text.split(':').toVector.map(_.toIntOption) match {
      case Vector(Some(from), Some(until)) if from < until => Right(from until until)
      case _ => Left(s"$what=$text is not FROM:UNTIL with FROM below UNTIL")
    }

  /** Every position some row of the evolution holds. */
  def reach(evolution: Evolution): Range =
    evolution.rows.map(_.first).min until evolution.rows.map(_.end).max

  private def sequence[A](items: Vector[Either[String, A]]): Either[String, Vector[A]] =
    items.foldLeft(Right(Vector.empty): Either[String, Vector[A]])((acc, item) => acc.flatMap(xs => item.map(xs :+ _)))

  /**
   * The figures this file holds by name.
   *
   * `gilbreath-vs-rule30` is the figure of Mycelium note `917b3939`, drawn there by a Python script
   * outside this repository: Gilbreath's table over the primes, rows 1 to 300 and the first 300
   * positions, beside the XOR rule from a random row, Rule 30 from one cell and the XOR rule from
   * one cell. It is here so the note's figure can be drawn again from this repository, and the four
   * panels are what `DrawSpec` checks against independent simulations.
   */
  val Figures: Map[String, Either[String, Vector[Panel]]] = Map(
    "gilbreath-vs-rule30" -> sequence(
      Vector(
        "rule=difference start=primes:601 steps=300 rows=1:301 columns=0:300 title=Absolute_differences_of_the_primes,_rows_1_to_300",
        "rule=xor start=random:900:30 steps=299 columns=0:300 title=XOR_rule_from_a_random_row",
        "rule=30 start=cell steps=299 columns=-300:301 title=Rule_30_from_one_cell",
        "rule=xor start=cell steps=299 columns=-300:1 title=XOR_rule_from_one_cell_(Pascal's_triangle_modulo_2)"
      ).map(panel)
    )
  )
}
