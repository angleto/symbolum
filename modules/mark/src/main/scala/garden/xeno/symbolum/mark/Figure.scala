package garden.xeno.symbolum.mark

/**
 * The mark as a shape rather than as a mask: a description in continuous coordinates, from which
 * the character art at any number of rows is a rasterisation.
 *
 * Until this existed the art was placed cell by cell and the figure had exactly one size. That was
 * defensible while it was true that no formula reproduced the drawing, and it stopped being true
 * here: the description below rasterises at twenty-three rows to the drawing that was approved,
 * **within four cells**, and those four are recorded in `docs/logo.md` because they are the price
 * of having one source instead of two.
 *
 * == The units ==
 *
 * Everything is in radii: a length of 1 is the circle's outer radius, an angle is degrees
 * counterclockwise from three o'clock, and a point is given as how far right of the centre and how
 * far above it. A column is half a row wide, which is where every factor of two below comes from,
 * so the figure is round on a terminal rather than oval. Nothing here carries a number of cells,
 * which is what lets the same description answer at another size.
 *
 * == The three strokes ==
 *
 *   - The **circle**, a band whose centre radius and half-width are both piecewise linear in the
 *     angle. Constant until the closing run, where the width falls and the centre radius falls with
 *     it: the stroke thins **and** leaves the outline, which is what puts its end inside the figure
 *     rather than on the circumference.
 *   - The **terminal**, a straight band of falling width from where the circle's run stops to the
 *     tip, cut square. It is straight and not an arc because the drawing it reproduces is: at this
 *     resolution the last four cells of a curve and of a straight line are the same four cells, and
 *     the straight one has two numbers where the curve had five.
 *   - The **bar**, a polyline of constant weight bent into a V, mitred at the vertex and cut square
 *     at both ends, with the far cap free to lean. It leans by ten degrees, which is one cell at the
 *     reference size and is the difference between the drawn tip and a square one.
 *
 * == What a size costs ==
 *
 * Not every size holds together. The slot between the terminal and the bar's left arm is three
 * columns at the reference, and a rasterisation that closes it seals a pocket; a rasterisation that
 * opens the counter loses the closure. `Mark` refuses to write a figure whose checks fail, and
 * `MarkSpec` records which sizes pass.
 */
object Figure {

  /** The size the committed art is drawn at, in rows. */
  val Reference: Int = 23

  /** The stroke, in radii. Five rows against a radius of eleven and a half. */
  private val Thickness = 5.0 / 11.5

  /** Where the circle's band starts, as a radial cut the bar's left arm covers. */
  private val Start = 56.0

  /** Where it stops and the terminal takes over. Past 360, because the pen has gone round once. */
  private val Join = 375.0

  /**
   * The centre radius, by angle. Constant while the stroke is at full weight, then falling: this is
   * the stroke leaving the outline, and it is what the closure is made of.
   */
  private val Radius: Vector[(Double, Double)] =
    Vector(330.0 -> Double.NaN, 350.0 -> 0.78261, 365.0 -> 0.74783, 375.0 -> 0.71304)

  /** The half-width, by angle, over the same run. */
  private val HalfWidth: Vector[(Double, Double)] =
    Vector(325.0 -> Double.NaN, 340.0 -> 0.22609, 354.0 -> 0.18261, 360.0 -> 0.13913, 375.0 -> 0.08696)

  private val TerminalTip = (0.33043, 0.47826)
  private val TerminalHalfWidth = 0.02609

  private val Bar = Vector((0.43478, 0.74783), (1.13043, 0.24348), (2.43913, 0.89565))
  private val BarWeight = 0.26087
  private val BarCapLean = -10.0

  /**
   * The full-weight values, computed rather than written.
   *
   * They are `1 - t/2` and `t/2` exactly, and writing them out to five decimals instead put four
   * cells of the left flank on the wrong side of a comparison: at the reference the inner edge falls
   * exactly on a cell centre, so a rounded parameter decides it. Anything that lands on a boundary
   * has to be derived from the same arithmetic on both sides.
   */
  private def fullRadius: Double = 1.0 - Thickness / 2.0
  private def fullHalfWidth: Double = Thickness / 2.0

  private def interpolate(knots: Vector[(Double, Double)], full: Double, x: Double): Double = {
    val resolved = knots.map { case (a, v) => (a, if (v.isNaN) full else v) }
    val first = resolved.head
    val last = resolved.last
    if (x <= first._1) full
    else if (x >= last._1) last._2
    else
      resolved
        .zip(resolved.tail)
        .collectFirst {
          case ((a, va), (b, vb)) if a <= x && x <= b => va + (vb - va) * (x - a) / (b - a)
        }
        .getOrElse(last._2)
  }

  private final case class Frame(rows: Int, cols: Int, radius: Double) {
    val yc: Double = radius - 0.5
    val xc: Double = 2 * radius - 1
    def point(right: Double, up: Double): (Double, Double) = (xc + 2 * right * radius, yc - up * radius)
    def polar(angle: Double, r: Double): (Double, Double) = {
      val a = math.toRadians(angle)
      (xc + 2 * r * math.cos(a), yc - r * math.sin(a))
    }
  }

  /**
   * The angle of a cell, wound forward until it is past where the band starts.
   *
   * Written as repeated addition rather than as `Start + ((phi - Start) % 360 + 360) % 360`, which
   * is the same number and not the same arithmetic. The paragraph on the full-weight values above
   * is the reason: at the reference size the inner edge of the flank falls on a cell centre, so a
   * comparison is decided by the last bit of its operands, and a remainder is a different float
   * operation from an addition. `atan2` answers in `(-180, 180]` and `Start` is 56, so this turns
   * at most once on every cell the caller has.
   *
   * The condition is `phi < Start` and not `phi >= Start` negated, which is the same test on every
   * number and not on a NaN: `NaN < Start` is false and so is `NaN >= Start`, so the first stops
   * and the second would call itself for ever. Nothing here produces one, the frame being finite
   * in both coordinates, and a tail recursion that diverges where the loop it replaces returned is
   * not a difference to leave to a reader to notice.
   */
  @annotation.tailrec
  private def wound(phi: Double): Double = if (phi < Start) wound(phi + 360.0) else phi

  private def circle(f: Frame): Set[(Int, Int)] =
    (for {
      r <- 0 until f.rows
      c <- 0 until f.cols
      dy = f.yc - r
      dx = (c - f.xc) / 2.0
      phi = wound(math.toDegrees(math.atan2(dy, dx)))
      if phi <= Join
      rho = interpolate(Radius, fullRadius, phi) * f.radius
      w = interpolate(HalfWidth, fullHalfWidth, phi) * f.radius
      if math.abs(math.hypot(dx, dy) - rho) <= w
    } yield (r, c)).toSet

  /**
   * The even-odd test: a point is inside where a ray from it crosses the outline an odd number of
   * times.
   *
   * Counting the crossings and reading the parity, rather than flipping a flag at each one, because
   * they are the same statement: a flag starting false and flipped n times ends true exactly when n
   * is odd. Each crossing is decided by the same two comparisons in the same order as before.
   */
  private def inside(poly: Vector[(Double, Double)], x: Double, y: Double): Boolean =
    poly.indices.count { i =>
      val (x0, y0) = poly(i)
      val (x1, y1) = poly((i + 1) % poly.length)
      (y0 > y) != (y1 > y) && x < (x1 - x0) * (y - y0) / (y1 - y0) + x0
    } % 2 == 1

  private def fill(f: Frame, poly: Vector[(Double, Double)]): Set[(Int, Int)] =
    (for {
      r <- 0 until f.rows
      c <- 0 until f.cols
      if inside(poly, c / 2.0, r)
    } yield (r, c)).toSet

  /** A straight band with square ends whose half-width runs from one value to the other. */
  private def terminal(f: Frame): Set[(Int, Int)] = {
    val (jx, jy) = f.polar(Join, interpolate(Radius, fullRadius, Join) * f.radius)
    val (tx, ty) = f.point(TerminalTip._1, TerminalTip._2)
    val w0 = interpolate(HalfWidth, fullHalfWidth, Join) * f.radius
    val w1 = TerminalHalfWidth * f.radius
    val (ax, ay) = (jx / 2.0, jy)
    val (bx, by) = (tx / 2.0, ty)
    val len = math.hypot(bx - ax, by - ay)
    val (ux, uy) = ((bx - ax) / len, (by - ay) / len)
    val (nx, ny) = (-uy, ux)
    fill(f, Vector((ax + nx * w0, ay + ny * w0), (bx + nx * w1, by + ny * w1),
      (bx - nx * w1, by - ny * w1), (ax - nx * w0, ay - ny * w0)))
  }

  private def bar(f: Frame): Set[(Int, Int)] = {
    val pts = Bar.map { case (a, b) => f.point(a, b) }
    val q = pts.map { case (x, y) => (x / 2.0, y) }
    val h = BarWeight * f.radius / 2.0
    val dirs = q.zip(q.tail).map { case ((x0, y0), (x1, y1)) =>
      val l = math.hypot(x1 - x0, y1 - y0)
      ((x1 - x0) / l, (y1 - y0) / l)
    }
    val lean = math.toRadians(BarCapLean)
    def side(sign: Double): Vector[(Double, Double)] = {
      val start = {
        val (dx, dy) = dirs.head
        (q.head._1 - dy * sign * h, q.head._2 + dx * sign * h)
      }
      val joints = dirs.zip(dirs.tail).zipWithIndex.map { case (((d1x, d1y), (d2x, d2y)), i) =>
        val p = q(i + 1)
        val a = (p._1 - d1y * sign * h, p._2 + d1x * sign * h)
        val b = (p._1 - d2y * sign * h, p._2 + d2x * sign * h)
        val den = d1x * d2y - d1y * d2x
        val t = ((b._1 - a._1) * d2y - (b._2 - a._2) * d2x) / den
        (a._1 + d1x * t, a._2 + d1y * t)
      }
      val end = {
        val (dx, dy) = dirs.last
        val p = q.last
        val (ex, ey) = (-dy * sign * h, dx * sign * h)
        (p._1 + ex * math.cos(lean) - ey * math.sin(lean), p._2 + ex * math.sin(lean) + ey * math.cos(lean))
      }
      (start +: joints) :+ end
    }
    fill(f, side(1.0) ++ side(-1.0).reverse)
  }

  /** The mask at a size, cropped to what it draws. */
  def cells(rows: Int): (Set[(Int, Int)], Int, Int) = {
    val radius = rows / 2.0
    val f = Frame(rows, (math.round(2 * radius * 3.8) + 8).toInt, radius)
    val drawn = circle(f) | terminal(f) | bar(f)
    val r0 = drawn.map(_._1).min
    val c0 = drawn.map(_._2).min
    val moved = drawn.map { case (r, c) => (r - r0, c - c0) }
    (moved, moved.map(_._1).max + 1, moved.map(_._2).max + 1)
  }

  /**
   * The character art at a size: the operator stream poured into the mask.
   *
   * The stream advances only over filled cells and does not restart at a row, so the character a
   * cell gets is fixed by how many filled cells precede it in reading order. That number is what a
   * running counter was standing for, and sorting the mask gives it directly: `(Int, Int)` orders
   * lexicographically, which is reading order, so the position in the sorted sequence IS the count.
   */
  def at(rows: Int): Vector[String] = {
    val (mask, h, w) = cells(rows)
    val order = mask.toVector.sorted.zipWithIndex.toMap
    (0 until h).toVector.map { r =>
      (0 until w)
        .map(c => order.get((r, c)).fold(' ')(k => Mark.Stream(k % Mark.Stream.length)))
        .mkString
        .replaceAll("\\s+$", "")
    }
  }
}
