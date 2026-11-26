package garden.xeno.symbolum.tactics

import java.util.concurrent.{Callable, ExecutionException, Executors, ThreadFactory, TimeUnit}
import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters.*

/**
 * Independent questions put to the prover at once, inside one JVM, and how many at once.
 *
 * A pass over the library's proposals is a map whose items share nothing but the chain, and the
 * chain is the one thing it is cheap to share: every term and type is interned in a concurrent
 * table, the reflexivity cache in `Conv` is one too, and the solver and the propositional encoding
 * are built per call. Threads in one JVM read one copy of it, where a fork per slice of the work
 * would build the chain once per fork and hold it once per fork; that is why the parallelism is
 * here and not in the build.
 *
 * **What decided it, measured on 2026-11-26** over 120 proposals spread across the 1323 the
 * standard library yields, at 8 threads: the readings came back identical to a sequential pass's,
 * proposal by proposal, in four parallel passes at 1 GB and 3 GB of heap, and the collector paused
 * for 2.6 s in all over a whole run at 1 GB, so the test fork's heap is not what limits it. The
 * speed-up read 1.2 to 3.0 and is not quoted as a figure: the machine's load average was 40 to 46
 * on 8 cores throughout, other sessions' work, and a figure taken there is a figure about them.
 *
 * **The order of the answers is the order of the questions**, whatever order the threads finish
 * in, so a caller that writes the answers down writes them as a sequential pass would.
 */
object Parallel {

  /** The system property that sets how many questions run at once. */
  val ThreadsProperty: String = "symbolum.threads"

  /**
   * How many at once: [[ThreadsProperty]] when it is set, otherwise every processor the JVM sees.
   *
   * The JVM's count already follows a container's limit. A value that is not a positive whole
   * number is refused by name rather than read as the default, since a typo that silently ran one
   * thread would look like a slow machine.
   */
  lazy val threads: Int =
    Option(System.getProperty(ThreadsProperty)) match {
      case None => Runtime.getRuntime.availableProcessors
      case Some(text) =>
        text.trim.toIntOption.filter(_ > 0).getOrElse(
          throw new IllegalArgumentException(
            s"$ThreadsProperty is '$text', and it has to be a positive whole number"))
    }

  /**
   * `items.map(f)`, with up to `threads` of them at once, in the order of `items`.
   *
   * One item or one thread is the plain map, on the caller's thread. An error thrown by `f` is
   * rethrown as itself rather than wrapped, so a `StackOverflowError` in the prover reads the same
   * here as it would sequentially. Every item still runs before it is, `invokeAll` waiting for all
   * of them, and the error rethrown is the first in the order of `items`.
   */
  def map[A, B](items: Vector[A], threads: Int = threads)(f: A => B): Vector[B] =
    if (items.size <= 1 || threads <= 1) items.map(f)
    else {
      val pool = Executors.newFixedThreadPool(math.min(threads, items.size), Daemons)
      try {
        val pending = pool.invokeAll(items.map(item => (() => f(item)): Callable[B]).asJava)
        pending.asScala.toVector.map { future =>
          try future.get
          catch { case failed: ExecutionException => throw failed.getCause }
        }
      } finally {
        pool.shutdownNow()
        pool.awaitTermination(1, TimeUnit.MINUTES)
      }
    }

  /**
   * Daemon threads, so a pass abandoned by an exception cannot keep a JVM alive; their stack is
   * the JVM's default for a new thread, which `-Xss` sets, as it sets the caller's.
   */
  private object Daemons extends ThreadFactory {
    private val count = new AtomicInteger
    def newThread(work: Runnable): Thread = {
      val thread = new Thread(work, s"symbolum-parallel-${count.incrementAndGet()}")
      thread.setDaemon(true)
      thread
    }
  }
}
