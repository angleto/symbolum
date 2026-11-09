package garden.xeno.symbolum.kernel

import java.lang.ref.WeakReference
import java.util.concurrent.{Callable, Executors, TimeUnit}
import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * One instance per term, which is what `docs/adr/0069` spends lines of the trusted base on.
 *
 * As in `TypeInterningSpec`, what is asserted is identity, `eq`, and never equality: equality was
 * structural before the change and still is, so `==` would pass on the kernel this replaced.
 *
 * What it does not reach is memory. The table is what took a chain from 663 MB to the figure the
 * record gives, and no assertion here says so.
 */
class TermInterningSpec extends AnyFlatSpec with Matchers {

  private val real = TyApp("real", Nil)
  private val x = Term.variable("x", real)
  private val y = Term.variable("y", real)
  private val theory = Theory.primitive
    .declareTypeOperator("real", 0)
    .flatMap(_.declareConstant("zero", real))
    .fold(error => fail(s"unexpected refusal: $error"), identity)

  private def right[A](result: Either[KernelError, A]): A =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  "Two terms spelled alike" should "be one instance however each was built" in {
    (Term.variable("x", real) eq x) shouldBe true
    (right(Term.eq(x, y)) eq right(Term.eq(x, y))) shouldBe true
    // The same equation reached through a substitution rather than built directly.
    val schema = right(Term.eq(x, Term.variable("z", real)))
    (right(Term.substitute(Map(Term.variable("z", real) -> y), schema)) eq right(Term.eq(x, y))) shouldBe true
  }

  it should "be one instance when one of them comes back from a beta step" in {
    val lambda = right(Term.abs(x, right(Term.eq(x, y))))
    val reduced = Term.betaReduce(right(Term.app(lambda, x))).getOrElse(fail("not a redex"))
    (reduced eq right(Term.eq(x, y))) shouldBe true
  }

  "A constant" should "be one instance for every asking of the theory, and its equality too" in {
    (right(theory.constant("zero", real)) eq right(theory.constant("zero", real))) shouldBe true
    (Term.equalityAt(real) eq Term.equalityAt(real)) shouldBe true
  }

  "Terms built on several threads at once" should "still come back as one instance" in {
    // A term none of the threads saw before, so they race on the first insertion. As in the types'
    // spec, a green is evidence about this run; the atomicity is `putIfAbsent`'s.
    val raced = Term.variable("raced", real)
    val pool = Executors.newFixedThreadPool(16)
    try {
      val built = pool
        .invokeAll(List.fill(64)((() => right(Term.eq(raced, x))): Callable[Term]).asJava)
        .asScala
        .map(_.get(30, TimeUnit.SECONDS))
      built.forall(_ eq built.head) shouldBe true
    } finally pool.shutdown()
  }

  "A term nothing holds" should "not be kept alive by the table" in {
    // The reason the table is weak: a strong one holds every term a process ever spelt, across
    // every chain it builds. Built in a method so that no local of this frame holds it.
    def unheld(): WeakReference[Term] =
      new WeakReference(right(Term.eq(Term.variable("transient", real), y)))
    val reference = unheld()
    val cleared = (1 to 50).exists { _ =>
      System.gc()
      Thread.sleep(20)
      reference.get() == null
    }
    cleared shouldBe true
    // And a term built again afterwards is built, not refused, which is the stale entry's path.
    right(Term.eq(Term.variable("transient", real), y)) shouldBe right(Term.eq(Term.variable("transient", real), y))
  }

  "A term built through the case class's mirror" should "be refused, since nothing checks it there" in {
    // Measured on 2026-11-09 at `0fa92517`, before this change: from outside this package
    // `App.fromProduct((p, x))` built `p x` with `p : bool`, which `Term.app` refuses, and
    // `Abs.fromProduct` built an abstraction over a loose index. Scala 3 makes `fromProduct` public
    // whatever the constructor is, and the compiler refuses a narrower one. `TrustBoundarySpec`
    // asks the same from outside.
    val p = Term.variable("p", Type.Bool)
    an[UnsupportedOperationException] should be thrownBy App.fromProduct((p, x))
    an[UnsupportedOperationException] should be thrownBy Abs.fromProduct((Type.Bool, p))
    an[UnsupportedOperationException] should be thrownBy BVar.fromProduct(Tuple1(0))
    an[UnsupportedOperationException] should be thrownBy
      summon[scala.deriving.Mirror.ProductOf[App]].fromProduct((p, x))
    // A free variable may be built by anyone, through `Term.variable`, and not through this either.
    an[UnsupportedOperationException] should be thrownBy FVar.fromProduct(("x", real))
  }
}
