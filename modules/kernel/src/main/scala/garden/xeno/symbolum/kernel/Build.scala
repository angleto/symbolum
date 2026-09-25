package garden.xeno.symbolum.kernel

import java.util.Properties

import scala.jdk.CollectionConverters.*
import scala.util.Using

/**
 * What the classes on this classpath were built from, read from the classes rather than from a
 * checkout.
 *
 * A certificate produced against this prover says which kernel checked it, and that claim is worth
 * exactly as much as where it was read. Read from the checkout, it describes a tree that may have
 * moved since the classes were compiled, or classes that were compiled with a coverage plugin
 * rewriting them. Read from here, it describes the classes that are running. The build writes
 * `META-INF/symbolum/build.properties` into every module, and `build.sbt` carries the argument for
 * what each field counts.
 *
 * == It is not part of the trusted base ==
 *
 * Nothing here can construct a theorem, and a defect here is a wrong provenance line and never a
 * false theorem. It is in this module because every other module of the proof side can see it and
 * because the question it answers is which kernel, not because it is believed.
 *
 * == What it does not establish ==
 *
 * That the classes beside a resource were all compiled by the build that wrote it. An incremental
 * build rewrites the resource from the tree as it is and recompiles only what changed, so a class
 * left from an earlier tree can sit under an identity naming this one. A run whose output is going
 * to be certified is a run in a checkout that has not been built before.
 */
object Build {

  /** The name every module's identity is written under, which is how a reader finds them all. */
  val ResourceName: String = "META-INF/symbolum/build.properties"

  /**
   * One module's record of the build that produced it.
   *
   * @param commit
   *   the forty hexadecimal digits of the commit the tree was at, or `None` where the tree had no
   *   git to ask, which is an absent answer and not a claim about any commit
   * @param dirty
   *   the build inputs that differed from that commit, by path; empty means none did
   * @param instrumented
   *   whether the classes were compiled with the coverage plugin, which rewrites every method
   */
  final case class Identity(
      module: String,
      version: String,
      commit: Option[String],
      dirty: Vector[String],
      instrumented: Boolean
  ) {

    /** What stands in the way of rebuilding these classes from the commit, one line per reason. */
    def obstacles: Vector[String] =
      Vector(
        Option.when(commit.isEmpty)(s"$module: built from a tree with no commit to name"),
        Option.when(dirty.nonEmpty)(
          s"$module: built from a tree that differs from its commit at ${dirty.mkString(", ")}"
        ),
        Option.when(instrumented)(s"$module: compiled with the coverage instrumentation")
      ).flatten
  }

  /**
   * Every module present on the classpath of `loader`, or every reason a record could not be read.
   *
   * All the unreadable records are named rather than the first, because a consumer repairing its
   * classpath would otherwise meet them one run at a time.
   */
  def modules(loader: ClassLoader = getClass.getClassLoader): Either[Vector[String], Vector[Identity]] = {
    val read = loader.getResources(ResourceName).asScala.toVector.map { url =>
      val properties = new Properties
      Using.resource(url.openStream())(properties.load)
      parse(properties).left.map(missing => s"$url: $missing")
    }
    val faults = read.collect { case Left(fault) => fault }
    if (faults.nonEmpty) Left(faults)
    else Right(read.collect { case Right(identity) => identity }.sortBy(_.module))
  }

  /**
   * The one commit every module on the classpath was built from, or why there is none.
   *
   * This is the question a certificate asks: not whether the kernel names a commit, but whether
   * the classes that ran are one reproducible build. So it refuses where the kernel is absent,
   * where any module is dirty, instrumented or unnamed, and where two modules name different
   * commits, and it names every one of those it finds.
   */
  def reproducibleCommit(loader: ClassLoader = getClass.getClassLoader): Either[Vector[String], String] =
    modules(loader).flatMap { present =>
      val absent =
        Option.when(!present.exists(_.module == "kernel"))(s"no kernel record on this classpath").toVector
      val commits = present.flatMap(_.commit).distinct
      val disagreement = Option
        .when(commits.size > 1)(
          "the modules name different commits: " +
            present.map(identity => s"${identity.module} ${identity.commit.getOrElse("none")}").mkString(", ")
        )
        .toVector
      val reasons = absent ++ present.flatMap(_.obstacles) ++ disagreement
      if (reasons.nonEmpty) Left(reasons) else Right(commits.head)
    }

  private val Hexadecimal = "[0-9a-f]{40}".r

  private[kernel] def parse(properties: Properties): Either[String, Identity] = {
    def field(key: String): Either[String, String] =
      Option(properties.getProperty(key)).toRight(s"no `$key`")
    for {
      module <- field("module")
      version <- field("version")
      commitText <- field("commit")
      commit <- commitText match {
        case "unrecorded" => Right(None)
        case Hexadecimal() => Right(Some(commitText))
        case other =>
          Left(s"`commit` is `$other`, neither forty hexadecimal digits nor `unrecorded`")
      }
      dirtyText <- field("dirty")
      instrumentedText <- field("instrumented")
      instrumented <- instrumentedText.toBooleanOption.toRight(
        s"`instrumented` is `$instrumentedText`, not a boolean"
      )
    } yield Identity(module, version, commit, dirtyText.split(',').toVector.filter(_.nonEmpty), instrumented)
  }
}
