package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*

/**
 * A quadratic form as a weighted sum of squares of linear forms, found in exact arithmetic.
 *
 * The second source of facts behind `Linarith`'s squares, which `docs/adr/0032` point 3 deferred and
 * `docs/adr/0056` decides. The first source completes a square over one unknown; this one reaches the
 * cross terms: `x * x + y * y - 2 * (x * y)` is `(x - y) * (x - y)`, and no completion over `x` or
 * `y` alone reaches the atom `x * y`.
 *
 * == Why no semidefinite program ==
 *
 * The general sum-of-squares search is a semidefinite program, because a polynomial of degree `2d`
 * has many Gram matrices and the search is for a positive semidefinite one among them. **Over the
 * monomials of degree at most one the Gram matrix is unique**: every entry is read off one
 * coefficient, the constant, a linear coefficient halved, a square's coefficient or a cross term's
 * halved. So there is nothing to search for. The quadratic is non-negative everywhere exactly when
 * that one matrix is positive semidefinite, and a symmetric decomposition `L D L^T` over the
 * rationals says whether it is and produces the squares when it is. Pivoting on the unknowns first
 * and the constant last is what makes the decomposition a sequence of completed squares, which is
 * the first source's construction applied one unknown at a time.
 *
 * == Untrusted, like the forms it reads ==
 *
 * What comes back is a set of **candidates**. `Linarith` turns each base into a term, instantiates
 * `Order.SQUARE_NONNEG` at it, and hands the fact to the certificate search with the hypotheses;
 * `Ring` checks whatever that search returns. A wrong decomposition costs a proof and cannot produce
 * one. The weights are what the certificate search is expected to find again, and they are returned
 * so that a test can check the identity rather than trust the search to reproduce it.
 *
 * == What it declines ==
 *
 * A form with an atom of more than two factors is outside the unique-Gram case and gets no squares:
 * over monomials of degree two the Gram matrix is no longer unique, and choosing among them is the
 * semidefinite search this does not do. A form with no product atom has nothing quadratic to
 * decompose. A pivot that is zero or negative is skipped rather than reported, since a matrix that is
 * not semidefinite has no decomposition and the squares already found may still be what a
 * combination with the hypotheses needs.
 */
object SumOfSquares {

  /** `weight * base * base`, with `weight` positive and the pivot's coefficient in `base` one. */
  final case class Square(weight: Rational, base: LinearForm)

  /**
   * The squares of the positive pivots, in the order the unknowns were pivoted on.
   *
   * `factors` flattens a product atom and `atom` keys the product of two unknowns, which are
   * `LinearForm.factorsOf` and `LinearForm.productAtom` for a caller with a theory. They are asked
   * for rather than assumed for the reason `LinearForm.times` asks for its key: this object never
   * builds a term, and the caller is the one that knows how its atoms are spelt.
   */
  def of(form: LinearForm, factors: Term => Vector[Term]): Vector[Square] = {
    val split = form.atoms.toVector.map(atom => atom -> factors(atom))

    if (split.exists(_._2.length > 2) || !split.exists(_._2.length == 2)) Vector.empty
    else {
      val unknowns = split.flatMap(_._2).distinct.sorted(using Term.ordering)
      val index = unknowns.zipWithIndex.toMap
      val size = unknowns.length
      val constant = size
      val half = Rational.of(BigInt(1), BigInt(2))
      val gram = Array.fill(size + 1, size + 1)(Rational.zero)

      def add(row: Int, column: Int, value: Rational): Unit =
        if (row == column) gram(row)(column) = gram(row)(column) + value
        else {
          gram(row)(column) = gram(row)(column) + value * half
          gram(column)(row) = gram(column)(row) + value * half
        }

      split.foreach { case (atom, parts) =>
        val value = form.at(atom)
        parts match {
          case Vector(unknown) => add(index(unknown), constant, value)
          case Vector(left, right) => add(index(left), index(right), value)
          case _ => ()
        }
      }
      gram(constant)(constant) = form.constant

      // The constant is never a pivot: whatever is left of it once the unknowns are eliminated is a
      // non-negative number the certificate search adds on its own, or a negative one no square
      // can repair.
      (0 until size).toVector.flatMap { pivot =>
        val weight = gram(pivot)(pivot)
        if (!weight.isPositive) None
        else {
          val row = (pivot to size).map(column => column -> gram(pivot)(column) / weight)
          for {
            (i, left) <- row
            (j, right) <- row
          } gram(i)(j) = gram(i)(j) - weight * left * right

          val base = row.foldLeft(LinearForm.zero) { case (acc, (column, value)) =>
            if (column == constant) acc + LinearForm.number(value)
            else acc + LinearForm.atom(unknowns(column)).scaled(value)
          }
          Some(Square(weight, base))
        }
      }
    }
  }
}
