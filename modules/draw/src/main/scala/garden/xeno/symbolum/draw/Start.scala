package garden.xeno.symbolum.draw

/** Starting rows, each with the edge its meaning asks for. */
object Start {

  /** One live cell at position 0 on an endless line of zeros. */
  val Cell: (Row, Edge) = (Row(0, Vector(1)), Edge.Endless)

  /**
   * `width` random bits from position 0, the same for the same seed on every machine.
   *
   * Finite, because a random row is a sample of something that goes on and nothing past its end is
   * known. The generator is SplitMix64 written out rather than `java.util.Random`, so that a figure
   * names its seed and anybody can draw it again without depending on which JDK draws it.
   */
  def random(width: Int, seed: Long): (Row, Edge) = {
    val states = Iterator.iterate(seed)(_ + 0x9e3779b97f4a7c15L).drop(1).take(width)
    (Row(0, states.map(mix(_) >>> 63).map(_.toInt).toVector), Edge.Finite)
  }

  /** SplitMix64's output function, which turns consecutive states into independent-looking words. */
  private def mix(state: Long): Long = {
    val a = (state ^ (state >>> 30)) * 0xbf58476d1ce4e5b9L
    val b = (a ^ (a >>> 27)) * 0x94d049bb133111ebL
    b ^ (b >>> 31)
  }

  /**
   * The first `count` primes from position 0. Finite, because they go on and the row does not: this
   * is the row Gilbreath's table starts from, and the table shrinks by one per step.
   */
  def primes(count: Int): (Row, Edge) = (Row(0, Primes.take(count).toVector), Edge.Finite)

  /** The primes, by trial division by the primes before them. */
  private lazy val Primes: LazyList[Int] =
    2 #:: LazyList.from(3, 2).filter(n => Primes.takeWhile(p => p * p <= n).forall(p => n % p != 0))

  /**
   * The binary digits of `n`, most significant at position 0, on an endless line of zeros. A
   * negative number has no digits here, and is refused rather than drawn as its magnitude.
   */
  def bits(n: BigInt): Either[String, (Row, Edge)] =
    if (n < 0) Left(s"the bits of a negative number are not drawn here, and $n is negative")
    else Right((Row(0, n.toString(2).map(_ - '0').toVector), Edge.Endless))
}
