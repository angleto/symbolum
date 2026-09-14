package garden.xeno.symbolum

import breeze.linalg.{DenseMatrix, DenseVector, NotConvergedException, eig}

/**
 * The dominant eigenvalue of a matrix with no negative entry, and the vector that goes with it.
 *
 * Perron and Frobenius: a square matrix with no negative entry has its spectral radius among its
 * eigenvalues, and at least one eigenvector belonging to it has no negative entry. That is what
 * makes the growth rate of a transfer operator a number one can ask for at all, and it is the
 * number this returns.
 *
 * The theorem is the reason the non-negativity is checked and not assumed. A matrix with a negative
 * entry has a largest-modulus eigenvalue too, and it can be complex, and its eigenvector can have
 * mixed signs; everything below would still return a number, and the number would not be a Perron
 * root. [[Unusable]] refuses that matrix by name rather than answering it.
 *
 * == Why a library, and which one ==
 *
 * Nothing here is written. `breeze.linalg.eig` is LAPACK's `dgeev` underneath: balancing, a
 * Hessenberg reduction, and the shifted QR iteration, which is forty years of edge cases nobody
 * should reimplement to own a copy. Power iteration is the other answer, it is twenty lines, and it
 * is worse in the case this exists for: it converges at the rate `|lambda_2| / |lambda_1|`, which
 * is where a nearly-periodic transfer matrix lives, and it cannot tell slow convergence from no
 * convergence. The full decomposition costs `O(n^3)` and answers the question the caller asked
 * along with [[Dominant.subdominant]], which is the number that says how badly power iteration
 * would have done.
 *
 * The decision is recorded in `build.sbt` beside the dependency. `Farkas`, in `modules/theories`,
 * is **not** moved onto this and must not be: it searches for a certificate by pivoting, and a
 * certificate that is nearly a certificate is refused by the ring step afterwards, so the exact
 * rationals there are the thing that makes it work rather than an affectation.
 *
 * == This is a measurement, and it is never a proof ==
 *
 * An eigenvalue out of `dgeev` is correct to a few units in the last place **of a nearby matrix**,
 * which is the only guarantee a backward-stable algorithm gives, and for a badly conditioned
 * eigenvalue that nearby matrix can be far enough away to matter. [[Dominant.residual]] is what
 * this can say about it: the largest entry of `A v - lambda v`, which is a number and is reported
 * as a number. Agreement with an expected value to twelve digits is agreement to twelve digits, and
 * this module is on the untrusted side of the wall where that is all it can ever be.
 * `NumericIsolationSpec` asserts that no module on the proof side can reach any of it.
 *
 * == Zero is an answer ==
 *
 * A strictly upper triangular matrix with non-negative entries has spectral radius exactly zero,
 * and so does the zero matrix. Those come back as [[Dominant]] with an eigenvalue of `0.0`, which
 * is a computation that succeeded and said the growth rate is nothing. It is a different outcome
 * from [[NotConverged]] and from [[Undecided]], and a caller that folds "the answer is zero" into
 * "there was no answer" has lost the distinction this whole file is arranged around.
 *
 * == Why `Vector` here and `IArray` in `Spectrum` ==
 *
 * The matrix is `n^2` numbers and the work on it is `O(n^3)`, so what the representation costs is
 * a vanishing share of what the decomposition costs, and an immutable nested `Vector` reads as what
 * it is at the call site. The measurement that made `Spectrum` choose otherwise was at four million
 * entries, which is not a size any dense eigensolver is going to be handed: `Perron.of` at `n = 512`
 * is already a quarter of a million entries and a hundred and thirty million multiplications.
 */
object Perron {

  /**
   * How far from an eigenvector a vector is allowed to be, per unit of `||A||`.
   *
   * `dgeev` is backward stable, so `||A v - lambda v||` sits at a small multiple of the machine
   * epsilon times `||A||` times the dimension, and the scale everything below is measured against
   * is the matrix's infinity norm rather than the eigenvalue. The two are close for a non-negative
   * matrix, since the spectral radius lies between the smallest and the largest row sum, but they
   * are not the same number when the mass is off the dominant direction and the norm is the one the
   * error actually follows.
   *
   * Measured over `PerronSpec`'s matrices on 2026-09-12. The worst residual seen was the all-ones
   * matrix at `n = 64`, `1.30e-13` absolutely against a norm of `64`, so `2.03e-15` relatively;
   * nothing else in that file exceeded `1e-14` even absolutely.
   *
   * `1e-9` is six orders of magnitude above the worst of them, and the margin is that wide on
   * purpose, because this gate is not looking for a slightly inaccurate answer. It is looking for a
   * **wrong vector**. The eigenvector columns arrive in LAPACK's packed layout, where the two
   * columns belonging to a complex pair are a real part and an imaginary part rather than two
   * eigenvectors, and a misread of that layout fails here by orders of magnitude rather than by a
   * digit. A tighter threshold would buy nothing and would start failing on hard matrices.
   */
  val Residual: Double = 1e-9

  /**
   * How negative an entry of the eigenvector may be before the vector is not a Perron vector.
   *
   * The vector is scaled to unit length before this is applied, so the threshold is absolute and
   * its unit is "a fraction of the vector's own size". The theorem says the entries are all of one
   * sign, so after the sign is fixed the only negative entries should be rounding noise about zero.
   * `1e-9` leaves the same wide margin [[Residual]] does and for the same reason: it is a check on
   * whether the right vector came back, not on how many digits it has.
   *
   * The same number serves as the relative slack on "is this eigenvalue real" and on "is the
   * largest real eigenvalue also the largest in modulus", both measured against `||A||`, and for
   * the same reason again: those are questions about which eigenvalue came back rather than about
   * its last digits.
   */
  val Negative: Double = 1e-9

  /** What the decomposition established, or why it established nothing. */
  sealed trait Outcome

  /**
   * The spectral radius, its eigenvector, and two numbers that say how much to believe them.
   *
   * `eigenvector` is scaled to unit Euclidean length, with the sign fixed so that the entry of
   * largest magnitude is positive. That leaves it determined up to the scale, which is all an
   * eigenvector ever is; a caller that wants it to sum to one divides.
   *
   * `subdominant` is the largest modulus among the **other** eigenvalues, absolutely rather than as
   * a ratio, because the ratio is what a caller wants and `0 / 0` is what the nilpotent case would
   * make of it. `subdominant` equal to `eigenvalue` is a real and common situation, not a failure:
   * a permutation matrix has eigenvalues on the whole unit circle and its Perron root is still one.
   * What it costs is uniqueness of the eigenvector, so a caller who needs the vector rather than
   * the number should read this.
   *
   * `residual` is `max |(A v - lambda v)_i|`, the thing a reader checks by eye. It is an
   * observation about how well these numbers satisfy the equation, and observing that is not
   * proving it.
   */
  final case class Dominant(
    eigenvalue: Double,
    eigenvector: Vector[Double],
    subdominant: Double,
    residual: Double
  ) extends Outcome

  /**
   * The decomposition ran and what came back is not a Perron root.
   *
   * Which, for a matrix with no negative entry, means something went wrong in the arithmetic rather
   * than in the mathematics: the theorem says the spectral radius is a real non-negative eigenvalue
   * with a sign-definite eigenvector, so the largest modulus being attained only by a complex pair,
   * or the vector failing [[Residual]] or [[Negative]], is a contradiction with the input rather
   * than a property of it.
   *
   * **Not** a small answer and **not** a missing one: it is a computation that produced something
   * incoherent, and reporting it as either of the other two is how the machinery would mislead.
   * `why` names which of the three checks failed and by how much.
   */
  final case class Undecided(why: String) extends Outcome

  /**
   * The QR iteration did not converge, which is `dgeev` giving up.
   *
   * Its own outcome, distinct from [[Undecided]], because the move is different: this one is about
   * the matrix being hard, and a caller has balancing, a similarity transform, or a different
   * method to try. `why` carries what LAPACK said.
   */
  final case class NotConverged(why: String) extends Outcome

  /**
   * The question could not be put: not square, empty, ragged, non-finite, or somewhere negative.
   *
   * The last of those is the one that is easy to read as pedantry and is not. Perron-Frobenius is
   * a theorem about non-negative matrices; run on a matrix with a negative entry, everything below
   * still returns a number, and that number is the largest-modulus eigenvalue rather than a growth
   * rate, with an eigenvector that can be anything. Answering would be worse than refusing.
   */
  final case class Unusable(why: String) extends Outcome

  /** The Perron root of `matrix`, given row by row. */
  def of(matrix: Vector[Vector[Double]]): Outcome =
    refuse(matrix).getOrElse {
      val size = matrix.length
      val dense = DenseMatrix.tabulate(size, size)((row, column) => matrix(row)(column))

      // The infinity norm, which is the largest row sum because no entry is negative. It is the
      // scale every tolerance below is measured in, and it is at least one so that a matrix of tiny
      // entries does not get tolerances tighter than the arithmetic can meet.
      val scale = math.max(1.0, matrix.map(_.sum).max)

      /*
       * A catch of one named exception rather than `Try`, and the difference matters here.
       *
       * `Try` collects everything non-fatal, and there is no honest outcome to map a defect onto:
       * `refuse` has already thrown out every matrix `dgeev` documents an argument error for, so
       * anything other than a failure to converge is a mistake in this file, and turning it into
       * `NotConverged` or `Undecided` would be merging a defect with a refusal, which is the one
       * thing the outcomes here exist to prevent. Named this way, a defect propagates and gets
       * fixed.
       */
      val decomposition =
        try Right(eig(dense))
        catch { case failure: NotConvergedException => Left(failure) }

      decomposition match {
        case Left(failure) =>
          NotConverged(
            s"the eigenvalue iteration did not converge on a $size by $size matrix: " +
              Option(failure.getMessage).filter(_.nonEmpty).getOrElse(failure.reason.toString))

        case Right(found) =>
          settle(
            transform = v => (dense * DenseVector(v.toArray)).toArray.toVector,
            real = found.eigenvalues.toArray.toVector,
            imaginary = found.eigenvaluesComplex.toArray.toVector,
            vector = index => found.eigenvectors(::, index).toArray.toVector,
            scale = scale)
      }
    }

  /* ------------------------------------------------- reading the decomposition back */

  /**
   * Pick the eigenvalue the theorem promises, then check that it is the one that came back.
   *
   * The candidate is the largest real eigenvalue, real meaning an imaginary part that is nothing
   * beside `||A||`. The theorem says that candidate **is** the spectral radius, so comparing it
   * against the largest modulus over all the eigenvalues is a check rather than a selection: if
   * they differ, the arithmetic disagrees with Perron-Frobenius about an input that satisfies its
   * hypotheses, and the honest answer is [[Undecided]] rather than either number.
   *
   * == Why this is visible to the tests ==
   *
   * Every [[Undecided]] below is unreachable through [[of]], and deliberately so: [[refuse]] has
   * already thrown out the matrices the theorem does not cover, so an input that gets this far and
   * fails one of these gates means LAPACK contradicted Perron-Frobenius. A branch nothing can reach
   * is a branch nothing checks, which this repository says out loud in `Relation.reduce` and
   * resolves there by leaving the guard out. Leaving these out is not the same trade: they catch a
   * **misread of the decomposition**, which is a live defect rather than an impossible input,
   * because the eigenvector columns arrive in LAPACK's packed layout where a complex pair occupies
   * two columns as a real part and an imaginary part. So the seam is opened instead, and
   * `PerronSpec` drives it with decompositions it makes up.
   *
   * The matrix arrives as `transform`, the linear map it is, rather than as a matrix type, so that
   * nothing in this signature or in [[check]] mentions the numeric library. A test supplies a
   * function; `of` supplies one closed over a `DenseMatrix`.
   */
  private[symbolum] def settle(
    transform: Vector[Double] => Vector[Double],
    real: Vector[Double],
    imaginary: Vector[Double],
    vector: Int => Vector[Double],
    scale: Double
  ): Outcome = {
    val moduli = real.lazyZip(imaginary).map((re, im) => math.hypot(re, im))
    val largest = moduli.max
    val realIndices = real.indices.filter(i => math.abs(imaginary(i)) <= Negative * scale)

    if (realIndices.isEmpty)
      Undecided(
        "every eigenvalue came back with an imaginary part, the smallest of them " +
          f"${imaginary.map(math.abs).min}%.3e, and Perron-Frobenius says a matrix with no " +
          "negative entry has a real one at its spectral radius")
    else {
      val best = realIndices.maxBy(real)
      val candidate = real(best)

      if (math.abs(candidate - largest) > Negative * scale)
        Undecided(
          f"the largest real eigenvalue is $candidate%.17g and the largest modulus over all of them " +
            f"is $largest%.17g; for a matrix with no negative entry those are the same number, so " +
            "the decomposition disagrees with Perron-Frobenius rather than with a tolerance")
      else {
        val others = moduli.indices.filter(_ != best).map(moduli)
        check(transform, candidate, vector(best), others.maxOption.getOrElse(0.0), scale)
      }
    }
  }

  /**
   * Normalise the eigenvector, then make it earn the name.
   *
   * Two gates, and each says what it failed by. The residual catches a vector that is not an
   * eigenvector at all, which is what a misread of LAPACK's packed complex columns produces. The
   * sign catches a vector that is an eigenvector and is not the Perron one, which is what a
   * degenerate spectral radius can produce. Visible to the tests for the reason [[settle]] gives.
   */
  private[symbolum] def check(
    transform: Vector[Double] => Vector[Double],
    eigenvalue: Double,
    raw: Vector[Double],
    subdominant: Double,
    scale: Double
  ): Outcome = {
    val length = math.sqrt(raw.map(entry => entry * entry).sum)

    if (length == 0.0 || length.isNaN)
      Undecided("the eigenvector came back as the zero vector, which is not an eigenvector")
    else {
      // The sign is free in an eigenvector, so fix it rather than test it: put the entry of largest
      // magnitude on the positive side, and any entry still negative afterwards is a real sign
      // change rather than a convention.
      val orientation = if (raw.maxBy(entry => math.abs(entry)) < 0) -1.0 else 1.0
      val unit = raw.map(entry => orientation * entry / length)

      val applied = transform(unit)
      val residual =
        applied.lazyZip(unit).map((image, entry) => math.abs(image - eigenvalue * entry)).max

      if (residual > Residual * scale)
        Undecided(
          f"the vector for eigenvalue $eigenvalue%.17g leaves a residual of $residual%.3e, which is " +
            f"past ${Residual * scale}%.3e, so it is not an eigenvector of this matrix")
      else if (unit.min < -Negative)
        Undecided(
          f"the eigenvector has an entry at ${unit.min}%.3e after its sign was fixed, and " +
            "Perron-Frobenius gives the spectral radius an eigenvector of one sign, so this is not " +
            "the Perron vector")
      else
        Dominant(eigenvalue, unit, subdominant, residual)
    }
  }

  /* ---------------------------------------------------------------- the refusals */

  /** Everything about the input that stops the question being asked, or nothing. */
  private def refuse(matrix: Vector[Vector[Double]]): Option[Outcome] =
    if (matrix.isEmpty) Some(Unusable("an eigenvalue wants a matrix and was given no rows"))
    else {
      val size = matrix.length

      matrix.indexWhere(_.length != size) match {
        case ragged if ragged >= 0 =>
          Some(
            Unusable(
              s"row $ragged has ${matrix(ragged).length} entries in a matrix of $size rows, and an " +
                "eigenvalue is only defined for a square one"))

        case _ =>
          // An iterator rather than a comprehension over the whole grid, so that a matrix of a
          // million entries with a bad one at the top left stops at the top left.
          matrix.indices.iterator
            .flatMap(row => matrix.indices.iterator.map(column => (row, column)))
            .find { case (row, column) =>
              val entry = matrix(row)(column)
              entry.isNaN || entry.isInfinite || entry < 0.0
            }
            .map { case (row, column) =>
              val entry = matrix(row)(column)
              if (entry.isNaN || entry.isInfinite)
                Unusable(
                  s"entry ($row, $column) is $entry, and every eigenvalue would come back $entry")
              else
                Unusable(
                  s"entry ($row, $column) is $entry; Perron-Frobenius is a theorem about matrices " +
                    "with no negative entry, and on this one a largest-modulus eigenvalue would " +
                    "not be a growth rate")
            }
      }
    }
}
