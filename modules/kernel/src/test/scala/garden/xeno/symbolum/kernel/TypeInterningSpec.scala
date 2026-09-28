package garden.xeno.symbolum.kernel

import java.util.concurrent.{Callable, Executors, TimeUnit}
import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * One instance per type, which is what `docs/adr/0058` spends sixteen lines of the trusted base on.
 *
 * What is asserted is identity, `eq`, and never equality: equality was structural before the
 * change and still is, so a test of `==` would pass on the kernel this replaced and would guard
 * nothing. Seen red on that kernel, 2026-09-27: with `Type.scala` put back as it was at `cf853ffa`
 * and nothing else changed, all four below failed on `eq`, and with the change all four passed.
 *
 * What it does not reach is memory. The table is what took a chain from 701 MB to 429 MB, and no
 * assertion here says so; the record has the measurement and how it was taken.
 */
class TypeInterningSpec extends AnyFlatSpec with Matchers {

  private val real = TyApp("real", Nil)

  "Two types spelled alike" should "be one instance however each was built" in {
    val direct = TyApp("fun", List(TyApp("real", Nil), TyApp("bool", Nil)))
    val throughFun = Type.fun(real, Type.Bool)
    (direct eq throughFun) shouldBe true
    (Type.Bool eq TyApp("bool", Nil)) shouldBe true
  }

  it should "be one instance when one of them is the result of an instantiation" in {
    val schema = Type.fun(TyVar("A"), Type.fun(TyVar("A"), Type.Bool))
    val instance = Type.substitute(Map("A" -> real), schema)
    (instance eq Type.fun(real, Type.fun(real, Type.Bool))) shouldBe true
  }

  "The type inside a constant built at an instance" should "be the one every other use holds" in {
    // The case that produced most of the copies: every equation a rule builds carries `=` at
    // `ty -> ty -> bool`, and that type was a fresh object each time.
    val a = Term.variable("a", real)
    val equation = Term.eq(a, a).fold(error => fail(s"unexpected refusal: $error"), identity)
    val equality = equation match {
      case App(App(constant: Const, _), _) => constant
      case other => fail(s"not an equation: $other")
    }
    (equality.ty eq Type.fun(real, Type.fun(real, Type.Bool))) shouldBe true
  }

  "Types built on several threads at once" should "still come back as one instance" in {
    // Sixteen threads and a type none of them saw before, so they race on the first insertion
    // rather than reading one somebody already made. `putIfAbsent` is what makes that race safe. A
    // table read and then written in two steps could lose it, but a race is not reproduced on
    // demand, so a green here is evidence about this run and not a proof that the table is atomic;
    // the atomicity is `ConcurrentHashMap`'s, and the red on the old kernel is only the control.
    val pool = Executors.newFixedThreadPool(16)
    try {
      val built = pool
        .invokeAll(List.fill(64)((() => TyApp("raced", List(real, TyVar("R")))): Callable[TyApp]).asJava)
        .asScala
        .map(_.get(30, TimeUnit.SECONDS))
      built.forall(_ eq built.head) shouldBe true
    } finally pool.shutdown()
  }

  "A type built through the case class's mirror" should "be the one instance as well" in {
    // Verification of card `78c1381d`, 2026-09-28 at `4756739d`: the constructor is private and the
    // copy method with it, but Scala 3 synthesises a public `fromProduct` on the companion that
    // calls `new` directly. Seen from source through scala-cli before this test was written:
    // `TyApp.fromProduct(("bool", Nil))` is `==` to `Type.Bool` and not `eq` to it. Nothing in the
    // repository calls it and no equality depends on the instance, so this is the docstring's
    // "Built only by TyApp.apply" and the title above being false, not a question of soundness.
    val mirrored = TyApp.fromProduct(("bool", Nil))
    (mirrored == Type.Bool) shouldBe true
    (mirrored eq Type.Bool) shouldBe true
  }
}
