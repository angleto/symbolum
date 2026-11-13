package garden.xeno.symbolum.draw

/**
 * A row of cells at true coordinates: `cells(i)` sits at position `first + i`.
 *
 * The coordinate travels with the row rather than being recovered at drawing time, and that is the
 * whole of what the figure of Mycelium note `917b3939` had to undo by hand. There the frame was a
 * Python list that lost a cell on the right at every step and was padded with zeros to keep its
 * length, so position `i` at step `t` meant `i + t - 2N` for Rule 30 and `i - 2N` for the XOR rule,
 * and the script carried an `unskew` with a different slope per panel. A row that knows where it
 * starts has nothing to unskew.
 */
final case class Row(first: Int, cells: Vector[Int]) {

  /** One past the last position this row holds. */
  def end: Int = first + cells.size

  /** The value at a position, or nothing where the row does not reach. */
  def at(position: Int): Option[Int] =
    if (position < first || position >= end) None else Some(cells(position - first))
}

/**
 * A rule taking a row to the next one: each new cell is `cell` applied to the old cells at
 * `offsets` from its own position.
 *
 * `bits` says the rule is defined on 0 and 1 only. An elementary automaton reads its neighbours as
 * the bits of an index into its number, and a value of 2 in that position would index a bit the
 * rule never assigned, which is an answer and not an error. So the evolution refuses such a row
 * instead of drawing it.
 */
final case class Rule(name: String, offsets: Vector[Int], bits: Boolean, cell: Vector[Int] => Int) {

  /** The value of the new cell over a neighbourhood of zeros, which decides what an endless row means. */
  def quiescent: Int = cell(offsets.map(_ => 0))
}

object Rule {

  /**
   * Wolfram's elementary automaton by number: the new cell is bit `4 l + 2 c + r` of `number`, over
   * the left neighbour, the cell and the right neighbour.
   */
  def elementary(number: Int): Either[String, Rule] =
    if (number < 0 || number > 255)
      Left(s"an elementary rule is numbered 0 to 255, and $number is not")
    else
      Right(
        Rule(
          s"Rule $number",
          Vector(-1, 0, 1),
          bits = true,
          n => (number >> (4 * n(0) + 2 * n(1) + n(2))) & 1
        )
      )

  /** The cell XOR its right neighbour, which from one cell is Pascal's triangle modulo 2. */
  val Xor: Rule = Rule("centre XOR right", Vector(0, 1), bits = true, n => n(0) ^ n(1))

  /**
   * The absolute difference of a cell and its right neighbour: Gilbreath's table, one row from the
   * next. On values 0 and 2 it is twice the XOR rule, which is why the two panels of the note look
   * alike.
   */
  val AbsoluteDifference: Rule =
    Rule("|right - centre|", Vector(0, 1), bits = false, n => math.abs(n(1) - n(0)))
}

/**
 * What lies beyond the cells a row holds.
 *
 * Two answers and not a default, because the figure needs both and they disagree on every panel.
 * A row of primes is a prefix of something that goes on, and nothing about the cells past its end
 * is known, so a cell whose neighbourhood leaves the row is not computed: the table shrinks by one
 * per step, as Gilbreath's does. A single cell on an endless line of zeros is the other reading,
 * and there the row grows by the rule's reach on each side.
 */
enum Edge {

  /** Only what the row holds is known, so the next row is computed where every neighbour exists. */
  case Finite

  /**
   * The row is the support of an endless line of zeros. Correct only for a rule taking a
   * neighbourhood of zeros to zero, because otherwise the line outside would change too and a
   * finite row could not say so; [[Evolution.of]] refuses the other rules here.
   */
  case Endless
}

/** The rows of an evolution, the first being the start. */
final case class Evolution(rule: Rule, edge: Edge, rows: Vector[Row]) {

  /** The value at a step and a position, or nothing where that row does not reach. */
  def at(step: Int, position: Int): Option[Int] = rows.lift(step).flatMap(_.at(position))
}

object Evolution {

  /** `steps` rows after `start`, so `steps + 1` rows in all, or the reason there are none. */
  def of(rule: Rule, edge: Edge, start: Row, steps: Int): Either[String, Evolution] =
    if (steps < 0) Left(s"a number of steps is not negative, and $steps is")
    else if (rule.bits && start.cells.exists(v => v != 0 && v != 1))
      Left(s"${rule.name} is defined on 0 and 1, and the starting row holds other values")
    else if (edge == Edge.Endless && rule.quiescent != 0)
      Left(
        s"${rule.name} takes a neighbourhood of zeros to ${rule.quiescent}, so the line outside the " +
          "row changes too and an endless row cannot be drawn from a finite one"
      )
    else Right(Evolution(rule, edge, Vector.iterate(start, steps + 1)(next(rule, edge, _))))

  /** One step. */
  def next(rule: Rule, edge: Edge, row: Row): Row = {
    val low = rule.offsets.min
    val high = rule.offsets.max
    // A new cell at `x` reads `x + low` to `x + high`. Where every one of those must be held, `x`
    // runs from `first - low` to `end - 1 - high`; where the outside reads zero, from the first
    // position whose neighbourhood reaches the row to the last.
    val (from, until) = edge match {
      case Edge.Finite => (row.first - low, row.end - high)
      case Edge.Endless => (row.first - high, row.end - low)
    }
    def read(position: Int): Int = row.at(position).getOrElse(0)
    Row(from, Vector.tabulate(math.max(0, until - from))(i => rule.cell(rule.offsets.map(o => read(from + i + o)))))
  }
}
