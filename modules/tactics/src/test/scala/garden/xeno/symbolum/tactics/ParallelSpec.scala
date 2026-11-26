package garden.xeno.symbolum.tactics

import java.util.concurrent.ConcurrentHashMap
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The map the corpus passes run their readings through: what it promises a caller that writes the
 * answers down, and what it does with an error.
 *
 * What would make these vacuous is a map that never left the caller's thread, which keeps every
 * promise below trivially; so the first test asserts that the work did run on more than one
 * thread, and finished out of order, before it asserts the order of what came back.
 */
class ParallelSpec extends AnyFlatSpec with Matchers {

  "A parallel map" should "answer in the order it was asked, whatever order the work finished in" in {
    val items = (1 to 64).toVector
    val threadsSeen = ConcurrentHashMap.newKeySet[String]()
    val finished = new java.util.concurrent.ConcurrentLinkedQueue[Int]()
    val answers = Parallel.map(items, threads = 8) { item =>
      threadsSeen.add(Thread.currentThread.getName)
      // the early items take longest, so they finish after the late ones
      Thread.sleep((65 - item).toLong)
      finished.add(item)
      item * item
    }
    answers shouldBe items.map(item => item * item)
    threadsSeen.size should be > 1
    finished.toArray.toVector should not be items
  }

  it should "rethrow an error as itself, the first in the order asked" in {
    val thrown = intercept[StackOverflowError] {
      Parallel.map((1 to 16).toVector, threads = 4) { item =>
        if (item == 5) throw new StackOverflowError("five")
        if (item == 9) throw new IllegalStateException("nine")
        item
      }
    }
    thrown.getMessage shouldBe "five"
  }

  it should "be the plain map on the caller's thread with one thread" in {
    val caller = Thread.currentThread.getName
    Parallel.map(Vector(1, 2, 3), threads = 1)(_ => Thread.currentThread.getName) shouldBe
      Vector(caller, caller, caller)
  }
}
