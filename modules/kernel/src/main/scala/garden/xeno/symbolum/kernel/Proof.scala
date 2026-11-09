package garden.xeno.symbolum.kernel

import scala.annotation.tailrec

/**
 * A theorem's derivation, written out as text.
 *
 * `Derivation` made a proof an object; this makes it an artifact. The difference is what a second
 * reading can be: `modules/checker` reading a `Thm` runs in this process and reads the terms through
 * this kernel's extractors, so a defect in *those* tells it the story they tell everyone.
 * `docs/architecture.md` said so under "what the kernel deliberately does not do" and named a
 * serialised proof as the step after. This is that step. What crosses the boundary now is
 * characters, and a reader on the other side shares no type, no algorithm and no assumption with
 * what wrote them.
 *
 * == It is not part of the trusted base, for the same reason `Derivation` is not ==
 *
 * Writing is not checking. If this file writes down something that is not what the kernel derived,
 * a checker reads a table that does not check and reports it. A defect here is a false alarm and
 * never a false theorem, which is why it sits in the kernel directory and outside the four files
 * `DocumentationSpec` counts.
 *
 * == The format ==
 *
 * One record per line, referring to earlier records by number, each kind numbered densely from
 * zero. The reader is `Parse` in `modules/checker` and its comment carries the grammar. Three
 * properties are the format's whole design and each is here for a reader that has to be simple:
 *
 *  - **References go backwards only**, so one pass suffices and a reader needs no fixup stage.
 *  - **A term is written once**, however many steps use it, which is what keeps a proof of tens of
 *    thousands of inferences to a size somebody can hold. Sharing is by value, since two terms that
 *    are equal are interchangeable everywhere.
 *  - **A step is written once per step and not per sequent.** Two steps that prove the same thing
 *    by different routes are two records, which is the property `Derivation.walk`'s comment exists
 *    about: deduplicating those would report a proof shorter than the one that was run.
 */
object Proof {

  /** The format's version, which a reader checks before anything else; two since `cite`. */
  val Version: String = "proof 2"

  /**
   * How many step records [[write]] puts down for `theorem`, without writing them.
   *
   * The same walk `write` numbers its steps by, so the two cannot disagree on what is reached: every
   * theorem the proof was built from, citations followed. It exists because a caller counting the
   * `s ` lines of the text paid for the text. Measured on 2026-11-09 in `ReachSpec`, writing the
   * proofs of the corpus one at a time to count them filled a 1024 MB heap from about 480 MB live
   * and forced a full compaction, since a proof that cites the library is written with the library
   * beneath it, and every term it reaches is put in a table to be numbered.
   */
  def steps(theorem: Kernel.Thm): Int = topological(theorem).length

  /** A theorem, as text. */
  def write(theorem: Kernel.Thm): String = {
    val out = new StringBuilder
    out.append(Version).append('\n')

    val types = scala.collection.mutable.HashMap.empty[Type, Int]
    val terms = scala.collection.mutable.HashMap.empty[Term, Int]

    // The record is built before the id is taken, in both of these, because building it writes the
    // parts this record refers to and the ids are dense in the order they were written. Taking the
    // id first would number this record before the ones it points at.
    def typeId(ty: Type): Int = types.get(ty) match {
      case Some(id) => id
      case None =>
        val record = ty match {
          case TyVar(name) => s"v ${encode(name)}"
          case TyApp(operator, arguments) =>
            val argumentIds = arguments.map(typeId)
            s"o ${encode(operator)}${argumentIds.map(" " + _).mkString}"
        }
        val id = types.size
        out.append(s"y $id $record\n")
        types.put(ty, id)
        id
    }

    def termId(term: Term): Int = terms.get(term) match {
      case Some(id) => id
      case None =>
        val record = term match {
          case BVar(index) => s"b $index"
          case FVar(name, kind) => s"f ${encode(name)} ${typeId(kind)}"
          case constant: Const =>
            val origin = constant.origin.map(termId).map(_.toString).getOrElse("-")
            s"c ${encode(constant.name)} ${typeId(constant.ty)} $origin"
          case App(fn, argument) => s"a ${termId(fn)} ${termId(argument)}"
          case Abs(binder, body) => s"l ${typeId(binder)} ${termId(body)}"
        }
        val id = terms.size
        out.append(s"t $id $record\n")
        terms.put(term, id)
        id
    }

    val ordered = topological(theorem)
    val stepIds = new java.util.IdentityHashMap[Kernel.Thm, Integer]

    ordered.zipWithIndex.foreach { case (current, id) =>
      val premises = Derivation.premises(current.derivation).map(stepIds.get(_).intValue)
      val (rule, own) = record(current.derivation, termId, typeId)
      val hypotheses = current.hypotheses.map(termId)
      val conclusion = termId(current.conclusion)

      out
        .append(s"s $id $rule")
        .append(own.map(" " + _).mkString)
        .append(" ;")
        .append(premises.map(" " + _).mkString)
        .append(" ;")
        .append(hypotheses.map(" " + _).mkString)
        .append(" ; ")
        .append(conclusion)
        .append('\n')

      stepIds.put(current, id)
    }

    out.append(s"end ${ordered.length - 1}\n")
    out.toString
  }

  /** A rule's name and the fields it carries besides its premises. */
  private def record(
    derivation: Derivation,
    termId: Term => Int,
    typeId: Type => Int
  ): (String, Vector[String]) = derivation match {
    case Derivation.Reflexivity(term) => ("refl", Vector(termId(term).toString))
    case Derivation.Transitivity(_, _) => ("trans", Vector.empty)
    case Derivation.Congruence(_, _) => ("comb", Vector.empty)
    case Derivation.Abstraction(variable, _) => ("abs", Vector(termId(variable).toString))
    case Derivation.BetaStep(term) => ("beta", Vector(termId(term).toString))
    case Derivation.Assumption(proposition) => ("assume", Vector(termId(proposition).toString))
    case Derivation.EqualityElimination(_, _) => ("eqmp", Vector.empty)
    case Derivation.Antisymmetry(_, _) => ("deduct", Vector.empty)

    case Derivation.Instantiation(substitution, _) =>
      ("inst", substitution.toVector.flatMap { case (variable, replacement) =>
        Vector(termId(variable).toString, termId(replacement).toString)
      })

    case Derivation.TypeInstantiation(substitution, _) =>
      ("insttype", substitution.toVector.flatMap { case (name, replacement) =>
        Vector(encode(name), typeId(replacement).toString)
      })

    case Derivation.Definition(name, body) =>
      ("def", Vector(encode(name), termId(body).toString))

    case Derivation.Axiom(proposition) => ("axiom", Vector(termId(proposition).toString))

    case Derivation.Citation(name, _) => ("cite", Vector(encode(name)))

    case Derivation.TypeDefinition(typeName, absName, repName, _, half) =>
      val which = half match {
        case Derivation.Half.AbstractionOfRepresentation => "abs"
        case Derivation.Half.Characterisation => "char"
      }
      ("tydef", Vector(encode(typeName), encode(absName), encode(repName), which))
  }

  /**
   * Every step of a proof, premises before the step that uses them.
   *
   * Iterative, for the reason `Derivation.walk` is: a numeral procedure chains hundreds of steps
   * and a recursive traversal would meet the stack first. By identity for the reason that walk
   * gives too, and this is where it bites hardest: two theorems are equal when they are the same
   * sequent, so a table deduplicated by equality would give one record two different derivations
   * and a reader no way to tell which it was reading.
   *
   * `@tailrec` is what keeps the first of those properties visible: the compiler rejects the
   * definition if the recursion is ever moved out of tail position, where the previous `while`
   * could only be read.
   */
  private def topological(theorem: Kernel.Thm): Vector[Kernel.Thm] = {
    val seen = java.util.Collections.newSetFromMap(
      new java.util.IdentityHashMap[Kernel.Thm, java.lang.Boolean]
    )

    // The flag says which visit this is: `false` asks for the premises to be pushed ahead of a
    // second entry for the same node, `true` is that second entry and emits it, so a node arrives
    // in the result only after everything it was built from.
    @tailrec
    def step(pending: List[(Kernel.Thm, Boolean)], order: Vector[Kernel.Thm]): Vector[Kernel.Thm] =
      pending match {
        case Nil => order
        case (current, true) :: rest => step(rest, order :+ current)
        case (current, false) :: rest =>
          if (seen.add(current))
            step(
              Derivation.premises(current.derivation).map((_, false)) ++ ((current, true) :: rest),
              order
            )
          else step(rest, order)
      }

    step(List((theorem, false)), Vector.empty)
  }

  /**
   * A name, so that it is one field.
   *
   * Percent-encoding over quoting, because a name here is `=`, `/\` or `\/` and deciding what an
   * escaped quote looks like inside one of those is a second decision nobody needs. Anything that
   * is not a letter, a digit, `_`, `.` or `-` is encoded, which is more than the separator and the
   * newline and is deliberate: a reader should never have to know which characters this writer
   * thought were safe.
   */
  def encode(name: String): String =
    name.getBytes("UTF-8").map { byte =>
      val character = (byte & 0xff).toChar
      if (character.isLetterOrDigit && character < 128) character.toString
      else if (character == '_' || character == '.' || character == '-') character.toString
      else f"%%${byte & 0xff}%02X"
    }.mkString
}
