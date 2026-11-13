package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Datatype

/**
 * A function defined by structural recursion, from the equations a document writes: `docs/adr/0080`.
 *
 * {{{
 *   define SIZE : tree -> num
 *     SIZE LEAF = 0
 *     SIZE (NODE l x r) = SIZE l + 1 + SIZE r
 *   end
 * }}}
 *
 * The equations are read, checked to be structural recursion, and turned into the clauses
 * `Datatype.defineRecursive` takes; it defines the constant from the datatype's recursion theorem
 * and hands back one equation per constructor, which are then brought to the form written, and
 * compared with it. Nothing is asserted, so a function defined here costs what the datatype costs,
 * and an equation that is not what was written is a refusal rather than a theorem about something
 * else.
 *
 * == What is structural recursion here ==
 *
 * Every equation is `NAME p1 .. pk (C x1 .. xa) t1 .. tq = RHS`, the same `k` for all of them: the
 * arguments before the one matched are **parameters**, the same in every equation, and a recursive
 * call passes them unchanged; the argument matched is one constructor applied to distinct
 * variables, each constructor in exactly one equation; the arguments after it are variables, and a
 * recursive call may pass anything there, which is what an accumulator is. A recursive call is
 * `NAME p1 .. pk y ...` where `y` is an argument of the constructor of the type itself. Anything
 * else is refused, naming the place: a call on something smaller that is not an argument of the
 * constructor, which is well-founded recursion and not this, and a nested pattern, which is two
 * definitions.
 *
 * The trailing arguments are why the result handed to `defineRecursive` is a function: the clause
 * of a constructor returns `\t1 .. tq. RHS`, and the equation it gives is applied to the trailing
 * variables and reduced. `APPEND (CONS x xs) ys = CONS x (APPEND xs ys)` is defined that way, with
 * no parameter and one trailing argument.
 */
object Recursive {

  /** Why the equations were not taken, on the line that shows it. */
  final case class Refused(line: Int, reason: String, next: Option[String])

  /**
   * The definition made: the theory with the constant, the constant, its equations as written, in
   * the order written, and what makes it again where it is imported.
   */
  final case class Defined(
    theory: Theory,
    constant: Term,
    equations: Vector[Kernel.Thm],
    typeName: String,
    parameters: List[FVar],
    clauses: List[Term]
  )

  /** One equation read: its line, the parameters, the constructor and its variables, the trailing variables, and the right side. */
  private final case class Read(
    line: Int,
    parameters: List[FVar],
    constructor: String,
    arguments: List[FVar],
    trailing: List[FVar],
    rhs: Term
  )

  def define(
    ground: Datatype.Ground,
    theory: Theory,
    notation: Notation,
    datatypes: Map[String, Datatype],
    name: String,
    line: Int,
    typeText: String,
    written: Vector[Document.Equation]
  ): Either[Refused, Defined] = {
    def show(term: Term): String = Show.show(notation, term)
    def refuse(at: Int, reason: String, next: Option[String] = None): Either[Refused, Nothing] = Left(Refused(at, reason, next))
    def lifted[A](at: Int)(result: Either[LogicError, A]): Either[Refused, A] =
      result.left.map(error => Refused(at, error.render(show), None))
    val shape = s"an equation `$name ... (C x ...) ... = VALUE`"

    for {
      ty <- lifted(line)(Parser.parseType(theory, typeText))
      _ <- if (theory.constants.contains(name)) refuse(line, s"$name is already a constant of the theory", Some("give the function a name of its own")) else Right(())
      self = Term.variable(name, ty)
      terms <- sequence(written.map(e => lifted(e.line)(Parser.term(theory, notation, e.text, Some(Type.Bool), Map(name -> ty))).map(e -> _)))
      sides <- sequence(terms.map { case (e, term) =>
        Term.destEq(term) match {
          case Some((lhs, rhs)) =>
            spine(lhs) match {
              case (head, arguments) if head == self && arguments.nonEmpty => Right((e, arguments, rhs))
              case _ => refuse(e.line, s"the left side of an equation of $name is $name applied to its arguments", Some(s"write $shape"))
            }
          case None => refuse(e.line, s"an equation of $name is $shape", None)
        }
      })
      // Which argument is matched: the one that is a constructor applied to variables, and the same in every equation.
      positions <- sequence(sides.map { case (e, arguments, _) =>
        arguments.zipWithIndex.collect { case (argument, index) if constructorOf(datatypes, spine(argument)._1).isDefined => index } match {
          case List(index) => Right(index)
          case Nil => refuse(e.line, s"no argument of $name here is a constructor of a datatype, so there is nothing for the recursion to take apart",
            Some("a function defined by equations matches one argument against a constructor of a datatype the document declares"))
          case _ => refuse(e.line, s"more than one argument of $name here is a constructor: the recursion takes apart one argument",
            Some("match one argument, and take the others apart in a second definition"))
        }
      })
      position = positions.head
      _ <- sides.zip(positions).find(_._2 != position).fold(Right(()): Either[Refused, Unit]) { case ((e, _, _), _) =>
        refuse(e.line, s"this equation matches argument ${positions(sides.indexWhere(_._1 == e)) + 1} of $name, and the first one matches argument ${position + 1}",
          Some("match the same argument in every equation"))
      }
      _ <- sides.find(_._2.size != sides.head._2.size).fold(Right(()): Either[Refused, Unit]) { case (e, _, _) =>
        refuse(e.line, s"this equation gives $name ${sides.find(_._1 == e).map(_._2.size).getOrElse(0)} arguments and the first one ${sides.head._2.size}",
          Some("give every equation the same arguments"))
      }
      datatype = constructorOf(datatypes, spine(sides.head._2(position))._1).get._1
      reads <- sequence(sides.map { case (e, arguments, rhs) => equation(e, arguments, rhs, position, datatype, name, show) })
      // The parameters are the first equation's; another equation naming them otherwise is renamed to them.
      parameters = reads.head.parameters
      renamed <- sequence(reads.map { r =>
        val renaming = r.parameters.zip(parameters).filter { case (a, b) => a != b }.toMap
        val others = (r.arguments ++ r.trailing).toSet ++ Term.freeVariables(r.rhs)
        if (renaming.values.exists(others.contains))
          refuse(r.line, s"this equation names the parameters ${r.parameters.map(_.name).mkString(" ")} and the first one ${parameters.map(_.name).mkString(" ")}, and the names collide here",
            Some("name the parameters the same way in every equation"))
        else lifted(r.line)(LogicError.lift(Term.substitute(renaming.map { case (k, v) => k -> (v: Term) }, r.rhs))).map(rhs => r.copy(parameters = parameters, rhs = rhs))
      })
      specification = datatype.specification
      byConstructor <- {
        val names = specification.constructors.map(_.name)
        val repeated = renamed.groupBy(_.constructor).collectFirst { case (c, found) if found.size > 1 => found(1) }
        val missing = names.filterNot(c => renamed.exists(_.constructor == c))
        repeated match {
          case Some(second) => refuse(second.line, s"${second.constructor} has an equation already", Some("one equation per constructor"))
          case None if missing.nonEmpty =>
            refuse(line, s"$name has no equation for ${missing.mkString(", ")}", Some(s"a function defined by recursion over ${specification.typeName} has one equation per constructor"))
          case None => Right(names.map(c => renamed.find(_.constructor == c).get))
        }
      }
      recursiveType = afterArrows(ty, position + 1)
      clauses <- sequence(byConstructor.toVector.map(r => clause(r, self, parameters, recursiveType, datatype, name, show)))
      made <- lifted(line)(Datatype.defineRecursive(datatype, ground, theory, name, parameters, clauses.toList))
      (extended, constant, equations) = made
      logic <- lifted(line)(ground.classical.logic.over(extended))
      // The equations as written, in the order written.
      stated <- sequence(renamed.map { r =>
        val index = specification.constructors.indexWhere(_.name == r.constructor)
        lifted(r.line)(asWritten(logic, equations(index), r, constant, self))
      })
    } yield Defined(extended, constant, stated, specification.typeName, parameters, clauses.toList)
  }

  /** The constructor `head` is, with its datatype, when it is one. */
  private def constructorOf(datatypes: Map[String, Datatype], head: Term): Option[(Datatype, String)] =
    head match {
      case Const(constant, _) =>
        datatypes.values.collectFirst { case d if d.specification.constructors.exists(_.name == constant) => (d, constant) }
      case _ => None
    }

  /** One equation's arguments checked for the shape structural recursion has. */
  private def equation(
    e: Document.Equation,
    arguments: List[Term],
    rhs: Term,
    position: Int,
    datatype: Datatype,
    name: String,
    show: Term => String
  ): Either[Refused, Read] = {
    val (constructor, constructorArguments) = spine(arguments(position))
    val Const(constructorName, _) = constructor: @unchecked
    val others = arguments.take(position) ++ arguments.drop(position + 1)
    val variables = others ++ constructorArguments
    variables.find(variable(_).isEmpty) match {
      case Some(bad) if constructorArguments.contains(bad) =>
        Left(Refused(e.line, s"$constructorName is applied here to ${show(bad)}, and a pattern of a definition by recursion is a constructor applied to variables",
          Some("match one level at a time: a nested pattern is a second function defined by recursion")))
      case Some(bad) =>
        Left(Refused(e.line, s"the argument ${show(bad)} of $name is not a variable, and only the argument matched against a constructor may be anything else",
          None))
      case None =>
        val named = variables.flatMap(variable)
        if (named.distinct.size != named.size)
          Left(Refused(e.line, s"a variable is named twice on the left side of this equation", Some("give every argument a name of its own")))
        else
          Right(Read(e.line, arguments.take(position).flatMap(variable), constructorName, constructorArguments.flatMap(variable),
            arguments.drop(position + 1).flatMap(variable), rhs))
    }
  }

  /**
   * The clause of one constructor: `\x1 .. xa. \r1 .. rj. \t1 .. tq. RHS'`, where `RHS'` is the right
   * side with each recursive call `NAME p1 .. pk y s ...` on the recursive argument `y` replaced by
   * `r s ...`, `r` standing for the value of the function at `y`.
   */
  private def clause(
    read: Read,
    self: FVar,
    parameters: List[FVar],
    recursiveType: Type,
    datatype: Datatype,
    name: String,
    show: Term => String
  ): Either[Refused, Term] = {
    val specification = datatype.specification.constructors.find(_.name == read.constructor).get
    val recursive = read.arguments.zip(specification.arguments).collect { case (variable, Datatype.Argument.Recursive) => variable }
    val taken = (read.arguments ++ read.trailing ++ parameters).map(_.name).toSet ++ Term.freeVariables(read.rhs).map(_.name)
    val values = recursive.map(y => y -> Term.variable(fresh(s"${y.name}_value", taken), recursiveType)).toMap
    def refuse(term: Term): Either[Refused, Nothing] =
      Left(Refused(read.line,
        s"$name is applied here as ${show(term)}, and a recursive call of $name passes ${if (parameters.isEmpty) "" else "its parameters unchanged and then "}" +
          s"one of the arguments ${read.constructor} takes of the type itself" +
          (if (recursive.isEmpty) s", which ${read.constructor} has none of" else s": ${recursive.map(_.name).mkString(", ")}"),
        Some("structural recursion calls the function on a part of the value matched; anything else wants a different definition")))
    def walk(term: Term, used: Set[String]): Either[Refused, Term] =
      term match {
        case Abs(binderType, _) =>
          val opened = Term.variable(fresh("v", used), binderType)
          for {
            applied <- Term.app(term, opened).left.map(_ => Refused(read.line, s"the right side of this equation does not read", None))
            body <- Term.betaReduce(applied).toRight(Refused(read.line, s"the right side of this equation does not read", None))
            inner <- walk(body, used + opened.name)
            closed <- Term.abs(opened, inner).left.map(_ => Refused(read.line, s"the right side of this equation does not read", None))
          } yield closed
        case _ =>
          val (head, arguments) = spine(term)
          if (head == self) {
            val (prefix, rest) = arguments.splitAt(parameters.size + 1)
            val call = prefix.take(parameters.size) == parameters && prefix.size == parameters.size + 1
            prefix.lastOption.flatMap(variable).flatMap(values.get) match {
              case Some(value) if call =>
                sequence(rest.toVector.map(walk(_, used))).flatMap(walked =>
                  Term.appAll(value, walked.toList).left.map(_ => Refused(read.line, s"the right side of this equation does not read", None)))
              case _ => refuse(term)
            }
          } else
            for {
              walkedHead <- if (head == term) Right(head) else walk(head, used)
              walkedArguments <- sequence(arguments.toVector.map(walk(_, used)))
              rebuilt <- Term.appAll(walkedHead, walkedArguments.toList).left.map(_ => Refused(read.line, s"the right side of this equation does not read", None))
            } yield rebuilt
      }
    for {
      body <- walk(read.rhs, taken)
      _ <- if (Term.occursFree(self, body)) refuse(self) else Right(())
      closed <- Term.absAll(read.arguments ++ recursive.map(values) ++ read.trailing, body)
        .left.map(_ => Refused(read.line, s"the right side of this equation does not read", None))
    } yield closed
  }

  /**
   * `|- !p xs. NAME p (C xs) = \t. RHS` as written: specialised at the equation's own variables,
   * applied to its trailing ones and reduced, generalised over them all, and compared with the
   * equation read, the function's variable replaced by the constant.
   */
  private def asWritten(logic: Logic, general: Kernel.Thm, read: Read, constant: Term, self: FVar): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      opened <- rules.specAll(general, read.parameters ++ read.arguments)
      applied <- read.trailing.foldLeft[Either[LogicError, Kernel.Thm]](Right(opened)) { (acc, t) =>
        for {
          equation <- acc
          withArgument <- LogicError.lift(Kernel.mkComb(equation, Conv.refl(t)))
          right <- Term.destEq(withArgument.conclusion).map(_._2).toRight(NotOfForm("an equation", withArgument.conclusion))
          reduced <- Conv.betaRoot(right)
          next <- Conv.trans(withArgument, reduced)
        } yield next
      }
      lhs <- Term.destEq(applied.conclusion).map(_._1).toRight(NotOfForm("an equation", applied.conclusion))
      expectedRight <- LogicError.lift(Term.substitute(Map(self -> constant), read.rhs))
      expected <- LogicError.lift(Term.eq(lhs, expectedRight))
      matched <-
        if (applied.conclusion == expected) Right(applied)
        else
          // The right side as written may hold a redex, which the equation made has reduced.
          for {
            normal <- Conv.betaNormalise(expected)
            target <- Term.destEq(normal.conclusion).map(_._2).toRight(NotOfForm("an equation", normal.conclusion))
            back <- Conv.sym(normal)
            moved <-
              if (target == applied.conclusion) LogicError.lift(Kernel.eqMp(back, applied))
              else Left(NotOfForm("the equation as it is written", applied.conclusion))
          } yield moved
      closed <- rules.genAll(matched, read.parameters ++ read.arguments ++ read.trailing)
    } yield closed
  }

  private def spine(term: Term): (Term, List[Term]) = term match {
    case App(function, argument) =>
      val (head, arguments) = spine(function)
      (head, arguments :+ argument)
    case other => (other, Nil)
  }

  private def variable(term: Term): Option[FVar] = term match {
    case v: FVar => Some(v)
    case _ => None
  }

  /** The type after `count` arrows of `ty`. */
  private def afterArrows(ty: Type, count: Int): Type =
    if (count <= 0) ty else Type.destFun(ty).fold(ty)(pair => afterArrows(pair._2, count - 1))

  private def fresh(base: String, taken: Set[String]): String =
    LazyList.from(0).map(i => if (i == 0) base else s"$base$i").find(candidate => !taken.contains(candidate)).get

  private def sequence[A](reads: Vector[Either[Refused, A]]): Either[Refused, Vector[A]] =
    reads.foldLeft(Right(Vector.empty): Either[Refused, Vector[A]])((acc, read) => acc.flatMap(done => read.map(done :+ _)))
}
