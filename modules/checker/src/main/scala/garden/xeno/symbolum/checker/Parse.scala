package garden.xeno.symbolum.checker

import scala.annotation.tailrec

/**
 * A proof read from text, by something that has never seen the kernel.
 *
 * This file imports nothing. That is the property it exists for and a test asserts it: everything
 * the checker needs about a proof arrives as characters, so the last thing the in-process route
 * shared with the kernel, the extractors it read terms through, is gone on this one. What is left
 * shared is the writer, and a writer that puts down something other than what was derived produces
 * a table that does not check.
 *
 * == The format ==
 *
 * One record per line, each naming itself and referring to earlier records by number. Ids are
 * per-kind and dense from zero, and a record may only refer backwards, so a reader needs one pass
 * and no fixup. Names are percent-encoded, because a constant here is called `=` and a lambda's
 * body is separated from its binder by a space.
 *
 * {{{
 * proof 1
 * y 0 o bool                  a type operator, then its argument ids
 * y 1 v a                     a type variable
 * t 0 c %3D 3 -               a constant: name, type, and the id of what defined it or `-`
 * t 1 f x 2                   a free variable: name and type
 * t 2 b 0                     a bound index
 * t 3 a 0 1                   an application: function then argument
 * t 4 l 2 3                   an abstraction: the binder's type then the body
 * s 0 refl 4 ; ; ; 7          a step: rule, its own fields, premises, hypotheses, conclusion
 * s 1 cite NAT_ADD_SYM ; 0 ; ; 7   a published fact under its name, with its proof as the premise
 * end 12
 * }}}
 *
 * The three semicolons are always there, so a step is read by position and an empty section is not
 * a special case. The `end` line names the step the proof is of.
 *
 * == What it refuses ==
 *
 * Every malformed thing, by returning a reason rather than throwing: a record out of order, a
 * reference forward or past the end, a rule that does not exist, a premise count the rule does not
 * take. None of that can be a false theorem, since a table that does not parse never reaches
 * `Check`; what it can be is a checker that fell over on a proof it should have refused, which is
 * the same class of defect as the one this file's own text was written after.
 */
object Parse {

  /** A proof, ready for `Check.table`, or why the text is not one. */
  final case class Proof(nodes: Vector[Node], theorem: Int)

  /**
   * The version this reader understands. A different one is refused rather than guessed at.
   *
   * Two since 2026-09-25, when `cite` became a rule: a reader of the first version would refuse a
   * proof holding one as naming a rule that does not exist, which is safe and says the wrong thing.
   */
  val Version: String = "proof 2"

  /**
   * What has been read so far, threaded through the records in order.
   *
   * Named for what it holds and not `Read`, which is already an object in this package that turns
   * a theorem into the reader's own types. One record rather than five accumulators, because every record that succeeds advances some of
   * them and a caller reading this has to be able to see which. The three vectors are also the
   * back-reference tables: a record may name a type, a term or a step already read and nothing
   * later, which is what makes a forward reference a refusal rather than a cycle.
   */
  private final case class Tables(
    types: Vector[Ty],
    terms: Vector[Expr],
    nodes: Vector[Node],
    theorem: Option[Int]
  )

  private object Tables {
    val nothing: Tables = Tables(Vector.empty, Vector.empty, Vector.empty, None)
  }

  def proof(text: String): Either[String, Proof] = {
    val lines = text.linesIterator.map(_.trim).filter(_.nonEmpty).toVector

    def record(so: Tables, line: String): Either[String, Tables] = {
      val fields = line.split(' ').toVector

      def because(why: String): Either[String, Tables] = Left(s"$why: $line")

      fields.headOption match {
        case Some("y") =>
          readType(fields, so.types.length, so.types)
            .fold(because, value => Right(so.copy(types = so.types :+ value)))

        case Some("t") =>
          readTerm(fields, so.terms.length, so.types, so.terms)
            .fold(because, value => Right(so.copy(terms = so.terms :+ value)))

        case Some("s") =>
          readNode(fields, so.nodes.length, so.types, so.terms)
            .fold(because, value => Right(so.copy(nodes = so.nodes :+ value)))

        case Some("end") =>
          fields match {
            case Vector(_, id) =>
              number(id, so.nodes.length)
                .fold(because("the theorem's step exists"))(value =>
                  Right(so.copy(theorem = Some(value)))
                )
            case _ => because("`end` names one step")
          }

        case _ => because("a record of a kind this reader knows")
      }
    }

    @tailrec
    def walk(remaining: Vector[String], so: Tables): Either[String, Tables] =
      remaining.headOption match {
        case None => Right(so)
        case Some(line) =>
          // The first refusal is the answer and reading stops. A reader shown the second malformed
          // record of a file whose first one is already wrong is being told about the wrong one,
          // and every record after a failure is read against a table that stopped advancing.
          record(so, line) match {
            case Left(why) => Left(why)
            case Right(next) => walk(remaining.tail, next)
          }
      }

    if (!lines.headOption.contains(Version)) Left(s"the first line is `$Version`")
    else
      walk(lines.tail, Tables.nothing).flatMap { read =>
        read.theorem
          .toRight("the text names no theorem, so there is nothing to check")
          .map(claimed => Proof(read.nodes, claimed))
      }
  }

  /* ------------------------------------------------------------------ the records */

  private def readType(
    fields: Vector[String],
    expected: Int,
    known: Vector[Ty]
  ): Either[String, Ty] =
    if (fields.length < 4 || fields.head != "y" || !number(fields(1), expected + 1).contains(expected))
      Left("a type record with this id")
    else
      (fields(2), decode(fields(3)), fields.drop(4)) match {
        case ("v", name, Vector()) => Right(Ty.Variable(name))

        case ("o", name, arguments) =>
          allOf(arguments, field => number(field, known.length).map(known))
            .map(read => Ty.Operator(name, read.toList))
            .toRight("every argument of a type operator is a type already read")

        case _ => Left("a type record of a shape this reader knows")
      }

  private def readTerm(
    fields: Vector[String],
    expected: Int,
    types: Vector[Ty],
    terms: Vector[Expr]
  ): Either[String, Expr] = {
    def ty(field: String): Option[Ty] = number(field, types.length).map(types)
    def term(field: String): Option[Expr] = number(field, terms.length).map(terms)

    if (fields.length < 3 || fields.head != "t" || !number(fields(1), expected + 1).contains(expected))
      Left("a term record with this id")
    else
      (fields(2), fields.drop(3)) match {
        case ("b", Vector(index)) =>
          number(index, Int.MaxValue).map(Expr.Bound.apply).toRight("a bound index is a number")

        case ("f", Vector(name, kind)) =>
          ty(kind).map(Expr.Free(decode(name), _)).toRight("a free variable's type is already read")

        case ("c", Vector(name, kind, origin)) =>
          val from = if (origin == "-") Right(None) else term(origin).map(Some(_)).toRight("a constant's origin is a term already read")
          for {
            source <- from
            kind <- ty(kind).toRight("a constant's type is already read")
          } yield Expr.Constant(decode(name), kind, source)

        case ("a", Vector(fn, argument)) =>
          for {
            function <- term(fn).toRight("an application's function is a term already read")
            value <- term(argument).toRight("an application's argument is a term already read")
          } yield Expr.Apply(function, value)

        case ("l", Vector(binder, body)) =>
          for {
            kind <- ty(binder).toRight("an abstraction's binder is a type already read")
            inner <- term(body).toRight("an abstraction's body is a term already read")
          } yield Expr.Lambda(kind, inner)

        case _ => Left("a term record of a shape this reader knows")
      }
  }

  private def readNode(
    fields: Vector[String],
    expected: Int,
    types: Vector[Ty],
    terms: Vector[Expr]
  ): Either[String, Node] = {
    def ty(field: String): Option[Ty] = number(field, types.length).map(types)
    def term(field: String): Option[Expr] = number(field, terms.length).map(terms)

    if (fields.length < 3 || fields.head != "s" || !number(fields(1), expected + 1).contains(expected))
      Left("a step record with this id")
    else {
      val sections = split(fields.drop(3))
      sections match {
        case Vector(own, premiseFields, hypothesisFields, Vector(conclusionField)) =>
          for {
            step <- readStep(fields(2), own, types, terms)
            premises <- allOf(premiseFields, field => number(field, expected))
              .toRight("every premise is a step already read")
            _ <-
              if (premises.length == Step.arity(step)) Right(())
              else Left(s"${Plural.count(Step.arity(step), "premise", "premises")} for ${fields(2)}, not ${premises.length}")
            hypotheses <- allOf(hypothesisFields, term).toRight("every hypothesis is a term already read")
            conclusion <- term(conclusionField).toRight("a conclusion that is a term already read")
          } yield Node(Claim(hypotheses, conclusion), step, premises)

        case _ => Left("four sections separated by `;`")
      }
    }
  }

  private def readStep(
    rule: String,
    own: Vector[String],
    types: Vector[Ty],
    terms: Vector[Expr]
  ): Either[String, Step] = {
    def term(field: String): Option[Expr] = number(field, terms.length).map(terms)
    def ty(field: String): Option[Ty] = number(field, types.length).map(types)

    (rule, own) match {
      case ("refl", Vector(subject)) =>
        term(subject).map(Step.Reflexivity.apply).toRight("`refl` names a term already read")
      case ("trans", Vector()) => Right(Step.Transitivity)
      case ("comb", Vector()) => Right(Step.Congruence)
      case ("abs", Vector(variable)) =>
        term(variable).collect { case free: Expr.Free => Step.Abstraction(free) }
          .toRight("`abs` names a free variable already read")
      case ("beta", Vector(redex)) =>
        term(redex).map(Step.BetaStep.apply).toRight("`beta` names a term already read")
      case ("assume", Vector(proposition)) =>
        term(proposition).map(Step.Assumption.apply).toRight("`assume` names a term already read")
      case ("eqmp", Vector()) => Right(Step.EqualityElimination)
      case ("deduct", Vector()) => Right(Step.Antisymmetry)

      case ("inst", pairs) if pairs.length % 2 == 0 =>
        val read = pairs.grouped(2).map {
          case Vector(variable, replacement) =>
            (term(variable).collect { case free: Expr.Free => free }, term(replacement))
          case _ => (None, None)
        }.toVector
        if (read.forall { case (variable, replacement) => variable.isDefined && replacement.isDefined })
          Right(Step.Instantiation(read.map { case (variable, replacement) =>
            variable.get -> replacement.get
          }.toMap))
        else Left("`inst` names free variables and terms already read")

      case ("insttype", pairs) if pairs.length % 2 == 0 =>
        val read = pairs.grouped(2).map {
          case Vector(name, replacement) => (Some(decode(name)), ty(replacement))
          case _ => (None, None)
        }.toVector
        if (read.forall(_._2.isDefined))
          Right(Step.TypeInstantiation(read.map { case (name, replacement) =>
            name.get -> replacement.get
          }.toMap))
        else Left("`insttype` names type variables and types already read")

      case ("def", Vector(name, body)) =>
        term(body).map(Step.Definition(decode(name), _)).toRight("`def` names a term already read")
      case ("axiom", Vector(proposition)) =>
        term(proposition).map(Step.Axiom.apply).toRight("`axiom` names a term already read")
      case ("cite", Vector(name)) => Right(Step.Citation(decode(name)))

      case ("tydef", Vector(typeName, absName, repName, half)) =>
        val which = half match {
          case "abs" => Some(Step.Half.AbstractionOfRepresentation)
          case "char" => Some(Step.Half.Characterisation)
          case _ => None
        }
        which
          .map(Step.TypeDefinition(decode(typeName), decode(absName), decode(repName), _))
          .toRight("`tydef` names which half it is, `abs` or `char`")

      case _ => Left(s"a rule this reader knows, with the fields it takes; `$rule` with ${own.length}")
    }
  }

  /* ------------------------------------------------------------------ the small parts */

  /** The four sections of a step, split on the separator, which is a field of its own. */
  private def split(fields: Vector[String]): Vector[Vector[String]] =
    // Starts at one empty section rather than none, so that a leading separator opens an empty
    // section instead of being swallowed: the count of sections is what the caller matches on.
    fields.foldLeft(Vector(Vector.empty[String])) { (sections, field) =>
      if (field == ";") sections :+ Vector.empty
      else sections.init :+ (sections.last :+ field)
    }

  private def allOf[T](fields: Vector[String], read: String => Option[T]): Option[Vector[T]] = {
    val found = fields.map(read)
    if (found.forall(_.isDefined)) Some(found.flatten) else None
  }

  /** A field as an index below `bound`, which is what makes a forward reference a refusal. */
  private def number(field: String, bound: Int): Option[Int] =
    field.toIntOption.filter(value => value >= 0 && value < bound)

  /**
   * A name, with the encoding undone.
   *
   * Percent-encoding and not quotes, because the alternative is deciding what an escaped quote
   * inside a name looks like, and a constant here is genuinely called `\/`.
   */
  def decode(field: String): String = {
    @tailrec
    def walk(at: Int, out: Vector[Byte]): Vector[Byte] =
      if (at >= field.length) out
      else if (field(at) == '%' && at + 2 < field.length)
        walk(at + 3, out :+ Integer.parseInt(field.substring(at + 1, at + 3), 16).toByte)
      else walk(at + 1, out ++ field.substring(at, at + 1).getBytes("UTF-8"))

    // The array is the `String` constructor's requirement and not an accumulator: it is built from
    // the finished sequence, in this expression, and nothing can observe it.
    new String(walk(0, Vector.empty).toArray, "UTF-8")
  }
}
