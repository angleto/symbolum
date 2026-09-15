package garden.xeno.symbolum.logic

import scala.annotation.tailrec
import garden.xeno.symbolum.kernel.*

/**
 * Concrete syntax: text in, a well-typed term out.
 *
 * This exists for one reason, and it is not convenience. The arithmetic axioms have to be read
 * against a textbook by a person, and a page of nested builder calls cannot be read that way: the
 * reader ends up checking that the code is plausible rather than that the axiom is right. So the
 * axioms are written as text and this turns them into terms.
 *
 * That purpose decides the one design question worth arguing about. Types are inferred, because a
 * syntax where every subterm carries an annotation is no more readable than the builders it
 * replaces. But a type that inference cannot pin down is an error here rather than an invented
 * type variable: `x = y` with nothing to say what `x` is could mean anything, and a parser that
 * quietly picks something turns an unreadable statement into a plausible-looking one, which is
 * worse than a refusal.
 *
 * == The syntax ==
 *
 * {{{
 * !x:real y:real. x + y = y + x        binders, `?` for the existential, `\` for lambda
 * p /\ q ==> q \/ ~p                   whatever the notation declares
 * f x y                                application, left associative and tightest
 * x:'a                                 a type annotation; `'a` is a type variable
 * }}}
 *
 * Which symbols exist, at what precedence and which way they associate, comes from [[Notation]]
 * rather than from this file: a theory that declares `+` declares how to write it. A name the
 * theory declares as a constant is that constant; any other name is a free variable, and every
 * occurrence of it in one term has one type.
 */
object Parser {

  /** A term of any type, in the standard notation of the logic. */
  def term(theory: Theory, text: String): Either[LogicError, Term] =
    term(theory, Notation.standard, text)

  /** A term of any type. */
  def term(theory: Theory, notation: Notation, text: String): Either[LogicError, Term] =
    parse(theory, notation, text, None)

  /**
   * A term of a type the caller already knows, refused if it is anything else.
   *
   * The elaborator has always taken an expected type and only [[proposition]] passed one, because
   * `bool` was the only type a caller ever knew in advance. A caller often does know: a summand of
   * a series is a `num -> real` whoever wrote the text, and since 2026-09-12 that is the
   * difference between reading `\i:num. 1` and refusing it for an undetermined numeral.
   *
   * **This is the preferred way out of that refusal and the annotation is the worse one**, which is
   * measured rather than preferred. The `collatz` repository put 630 hand-written texts to the
   * numerals on the day they landed; seven were refused, and **all seven were unambiguous to the
   * caller** -- six numerals about to be handed to `spec` at a lemma whose signature says the type,
   * and one constant summand. Writing `4:real` into the text puts the type in the one place a
   * reader compares against the informal claim it translates; passing it here puts it where it
   * belongs, in the interface of the code that already knew it.
   *
   * Seven out of seven is also a prediction worth checking: if the next consumer produces only
   * refusals its caller could have resolved, then the type was never the writer's to supply and
   * offering [[term]] without an expected type first is the wrong default rather than a
   * convenience.
   *
   * **Which of the two entry points, and it is not the same answer inside and outside.** A caller
   * in this repository reaches for `Signature.term`, whose theory is the chain's. A consumer does
   * not: it parses against a theory of its own, declaring constants the chain has never heard of,
   * and putting its text to the chain's signature turns each of those into a free variable whose
   * type never closes. So a consumer wants **this** method, with its own theory and notation. That
   * correction came from a consumer trying the advice and finding it wrong, which is why it is
   * written here rather than left to be discovered again.
   */
  def term(
    theory: Theory,
    notation: Notation,
    text: String,
    expected: Type
  ): Either[LogicError, Term] =
    parse(theory, notation, text, Some(expected))

  /** A term of type `bool`, in the standard notation of the logic. */
  def proposition(theory: Theory, text: String): Either[LogicError, Term] =
    proposition(theory, Notation.standard, text)

  /** A term of type `bool`, refused if it is anything else. */
  def proposition(theory: Theory, notation: Notation, text: String): Either[LogicError, Term] =
    parse(theory, notation, text, Some(Type.Bool))

  /** A type. */
  def parseType(theory: Theory, text: String): Either[LogicError, Type] = {
    val notation = Notation.standard
    val reader = new Reader(notation)
    Lexer.tokenise(notation.symbols, text).flatMap { tokens =>
      reader.readType(Cursor(tokens, 0)).flatMap { case (result, rest) =>
        for {
          _ <- reader.expectEnd(rest)
          _ <- LogicError.lift(theory.checkType(result))
        } yield result
      }
    }
  }

  private def parse(
    theory: Theory,
    notation: Notation,
    text: String,
    expected: Option[Type]
  ): Either[LogicError, Term] = {
    val reader = new Reader(notation)
    Lexer.tokenise(notation.symbols, text).flatMap { tokens =>
      reader.readTerm(Cursor(tokens, 0)).flatMap { case (pre, rest) =>
        for {
          _ <- reader.expectEnd(rest)
          result <- new Elaborator(theory, notation).run(pre, expected)
        } yield result
      }
    }
  }

  /* -------------------------------------------------------------------- tokens */

  private sealed trait Token {
    def position: Int
  }

  private object Token {
    final case class Name(text: String, position: Int) extends Token
    final case class Symbol(text: String, position: Int) extends Token
    final case class End(position: Int) extends Token
  }

  private object Lexer {

    def tokenise(symbols: List[String], text: String): Either[LogicError, Vector[Token]] = {
      @tailrec
      def go(index: Int, tokens: Vector[Token]): Either[LogicError, Vector[Token]] =
        if (index >= text.length) Right(tokens :+ Token.End(index))
        else if (text(index).isWhitespace) go(index + 1, tokens)
        else if (isNameStart(text(index))) {
          val end = advanceWhile(text, index, isNameCharacter)
          go(end, tokens :+ Token.Name(text.substring(index, end), index))
        } else if (text(index) == '\'') {
          val end = advanceWhile(text, index + 1, isNameCharacter)
          if (end == index + 1)
            Left(SyntaxError("a type variable needs a name after the quote", index))
          else go(end, tokens :+ Token.Name(text.substring(index, end), index))
        } else
          symbols.find(text.startsWith(_, index)) match {
            case Some(symbol) => go(index + symbol.length, tokens :+ Token.Symbol(symbol, index))
            case None =>
              Left(SyntaxError(s"cannot read the character '${text(index)}'", index))
          }

      go(0, Vector.empty)
    }

    private def isNameStart(c: Char): Boolean = c.isLetter || c == '_' || c.isDigit
    private def isNameCharacter(c: Char): Boolean = c.isLetterOrDigit || c == '_' || c == '\''

    @tailrec
    private def advanceWhile(text: String, index: Int, accept: Char => Boolean): Int =
      if (index < text.length && accept(text(index))) advanceWhile(text, index + 1, accept)
      else index
  }

  /* ------------------------------------------------------------------ preterms */

  /**
   * The shape of the text, before anything is known about types.
   *
   * Three cases, because every piece of surface syntax reduces to them: `!x. p` is `!` applied to
   * a lambda, `p /\ q` is `/\` applied twice, and both `!` and `/\` are constants the theory
   * already declares. Notation gets no cases of its own here and no special treatment in the
   * elaborator.
   */
  private enum Pre {
    case Ident(name: String, annotation: Option[Type], position: Int)
    case Apply(fn: Pre, argument: Pre)
    case Lambda(name: String, annotation: Option[Type], body: Pre)

    /**
     * An operator symbol that more than one constant is written with.
     *
     * Not an [[Ident]] with a name chosen here, which is what it was until `docs/adr/0018`: the
     * name is what this node exists not to decide. `x + y` is `real_add x y` or `NUM_ADD x y`
     * depending on what `x` and `y` turn out to be, and they are what the operator is being applied
     * to, so nothing is known about them yet at the point the symbol is read.
     */
    case Overloaded(symbol: String, candidates: Vector[String], position: Int)
  }

  /** The same shape with a type on every node, before the kernel is asked to build anything. */
  private enum Typed {
    case Free(name: String, ty: Type)
    case Constant(name: String, ty: Type)
    case Apply(fn: Typed, argument: Typed)
    case Lambda(name: String, ty: Type, body: Typed)

    /**
     * A digit string whose type its context has still to decide.
     *
     * Every other node knows which constants it is made of by the time it is built. A numeral does
     * not: `3` is `BIT1 1` over the reals and `NUM_BIT1 NUM_ONE` over `num`, and which of the two
     * it is depends on what the surrounding term applies it to. So it carries a metavariable like
     * any other unknown and is expanded in `build`, after unification has run, which is the same
     * place every other type is settled.
     */
    case Numeral(value: BigInt, ty: Type, position: Int)

    /**
     * An operator symbol with its candidates still open, carrying the shape they share.
     *
     * The numeral's case one step further out, and deferred for the same reason and to the same
     * place. `ty` is the least general type every candidate is an instance of, with a metavariable
     * wherever they differ, so unifying against it propagates whatever the arguments know without
     * committing to a candidate. `build` reads it back once unification has run.
     */
    case Overloaded(symbol: String, candidates: Vector[String], ty: Type, position: Int)
  }

  /* ------------------------------------------------------------------- reading */

  /**
   * A place in the token stream, which is what a reading step consumes and hands back.
   *
   * The reader held a mutable index into the tokens until the night of 2026-09-12, and the index
   * is now this.
   * What the change buys is in the signatures rather than in the behaviour: `readAtom(cursor)`
   * returning a cursor says that it consumes tokens and `atSymbol(cursor, ".")` says that it does
   * not, where the two used to be told apart only by reading their bodies. That distinction is the
   * one a reader of a recursive-descent parser has to keep in their head at every line, and it is
   * now written down.
   *
   * **The alternative was a private `Step[S, A]` with `map` and `flatMap`**, which would have left
   * every method body below byte-identical and changed only their return types, and it was rejected
   * for two things it costs. It puts twenty-five lines of abstraction between a reader and the
   * parser, on a file whose whole argument is that an axiom has to be readable; and `continue` and
   * `readApplication.go` are `@tailrec` today, which a chain of closures cannot be. Threading is
   * noisier at each line and asks nothing of the reader that the parser was not already asking.
   *
   * What this does **not** buy: nothing here backtracks, and a cursor that can be re-run from an
   * earlier position is not the same thing as a parser that ever does. The two `@tailrec` above are
   * the only depth bounds; `readAt` recurses through `readOperand` as it always did, so a term
   * nested thousands deep would still meet the stack, and that is unchanged rather than fixed.
   */
  private final case class Cursor(tokens: Vector[Token], index: Int) {
    def peek: Token = tokens(index)
    def next: Cursor = copy(index = index + 1)
  }

  /** What a reading step yields: a value, and where the next step starts. */
  private type Read[A] = Either[LogicError, (A, Cursor)]

  private final class Reader(notation: Notation) {

    private def atSymbol(cursor: Cursor, text: String): Boolean = cursor.peek match {
      case Token.Symbol(symbol, _) => symbol == text
      case _ => false
    }

    /** Past `text` if it is here, and nothing if it is not. */
    private def skip(cursor: Cursor, text: String): Option[Cursor] =
      if (atSymbol(cursor, text)) Some(cursor.next) else None

    private def expect(cursor: Cursor, text: String): Either[LogicError, Cursor] =
      skip(cursor, text).toRight(SyntaxError(s"expected '$text'", cursor.peek.position))

    def expectEnd(cursor: Cursor): Either[LogicError, Unit] = cursor.peek match {
      case Token.End(_) => Right(())
      case other => Left(SyntaxError("unexpected text after the term", other.position))
    }

    /* ---- terms, by precedence climbing over the notation ---- */

    def readTerm(cursor: Cursor): Read[Pre] = readAt(cursor, 0)

    /**
     * Everything binding at least as tightly as `minimum`.
     *
     * An operator that associates to the right hands its own precedence to its right operand, so
     * another of the same kind is read into it; one that associates to the left hands one more,
     * so it is not. Reading the right operand from the top instead, which is the obvious mistake
     * and the one made here once already, makes `p /\ q ==> r` mean `p /\ (q ==> r)`.
     */
    private def readAt(cursor: Cursor, minimum: Int): Read[Pre] =
      readOperand(cursor).flatMap { case (left, afterLeft) => continue(afterLeft, left, minimum) }

    @tailrec
    private def continue(cursor: Cursor, left: Pre, minimum: Int): Read[Pre] =
      currentInfix(cursor) match {
        case Some(operator) if operator.precedence >= minimum =>
          val next =
            if (operator.rightAssociative) operator.precedence else operator.precedence + 1
          readAt(cursor.next, next) match {
            case Left(error) => Left(error)
            case Right((right, afterRight)) =>
              continue(afterRight, infixApplication(operator, left, right), minimum)
          }

        case _ => Right((left, cursor))
      }

    private def currentInfix(cursor: Cursor): Option[Infix] = cursor.peek match {
      case Token.Symbol(symbol, _) => notation.infixFor(symbol)
      case _ => None
    }

    /**
     * The operator node for a symbol, which is one constant or a choice between several.
     *
     * The single case is left exactly as it was rather than routed through the plural one, and that
     * is deliberate: it is every operator in the repository but four, it carries `fixedType`, which
     * an overload cannot have and which `<=>` uses, and a change that made `p /\ q` take a
     * different path through the elaborator would have to be argued for on its own.
     *
     * Which candidates this theory actually declares is **not** decided here, because this class
     * has no theory and is not given one: that is the layering `docs/adr/0018` keeps, and the same
     * one `Notation.withNumerals` refused to break. The reader says "this symbol is a choice", and
     * the elaborator, which has the theory, says which choice and whether it is one at all.
     */
    private def infixApplication(operator: Infix, left: Pre, right: Pre): Pre = {
      val (first, second) = if (operator.flipped) (right, left) else (left, right)
      val candidates = notation
        .infixesFor(operator.symbol)
        .filter(candidate => candidate.flipped == operator.flipped)
        .map(_.constant)
        .distinct
      val head =
        if (candidates.sizeIs > 1) Pre.Overloaded(operator.symbol, candidates, 0)
        else Pre.Ident(operator.constant, operator.fixedType, 0)
      Pre.Apply(Pre.Apply(head, first), second)
    }

    /** A binder, a prefix operator, or an application. */
    private def readOperand(cursor: Cursor): Read[Pre] = cursor.peek match {
      case Token.Symbol(symbol, _) if notation.binderFor(symbol).isDefined =>
        readBinder(cursor, notation.binderFor(symbol).get)

      case Token.Symbol(symbol, _) if notation.prefixFor(symbol).isDefined =>
        val operator = notation.prefixFor(symbol).get
        readAt(cursor.next, operator.precedence).map { case (argument, rest) =>
          (Pre.Apply(Pre.Ident(operator.constant, None, 0), argument), rest)
        }

      case _ => readApplication(cursor)
    }

    /**
     * `!x y. body`, and the body extends as far to the right as it can.
     *
     * `p /\ !x. q ==> r` is `p /\ (!x. (q ==> r))`, which is the usual reading and the only one
     * that makes a quantifier at the end of a formula mean what it looks like.
     */
    private def readBinder(cursor: Cursor, binder: BinderNotation): Read[Pre] =
      readBinderVariables(cursor.next, Nil).flatMap { case (variables, afterVariables) =>
        expect(afterVariables, ".").flatMap { afterDot =>
          readTerm(afterDot).map { case (body, rest) =>
            val quantified = variables.foldLeft(body) { case (inner, (name, annotation)) =>
              val lambda = Pre.Lambda(name, annotation, inner)
              binder.constant match {
                case None => lambda
                case Some(constant) => Pre.Apply(Pre.Ident(constant, None, 0), lambda)
              }
            }
            (quantified, rest)
          }
        }
      }

    /** The variables of a binder, innermost first, up to the dot. */
    private def readBinderVariables(
      cursor: Cursor,
      acc: List[(String, Option[Type])]
    ): Read[List[(String, Option[Type])]] = cursor.peek match {
      case Token.Name(name, _) =>
        readAnnotation(cursor.next).flatMap { case (annotation, afterAnnotation) =>
          val gathered = (name, annotation) :: acc
          if (atSymbol(afterAnnotation, ".")) Right((gathered, afterAnnotation))
          else readBinderVariables(afterAnnotation, gathered)
        }

      case other => Left(SyntaxError("expected a variable after the binder", other.position))
    }

    private def readApplication(cursor: Cursor): Read[Pre] = {
      @tailrec
      def go(acc: Pre, from: Cursor): Read[Pre] =
        if (startsAtom(from)) readAtom(from) match {
          case Left(error) => Left(error)
          case Right((argument, rest)) => go(Pre.Apply(acc, argument), rest)
        }
        else Right((acc, from))

      readAtom(cursor).flatMap { case (first, rest) => go(first, rest) }
    }

    private def startsAtom(cursor: Cursor): Boolean = cursor.peek match {
      case Token.Name(_, _) => true
      case Token.Symbol("(", _) => true
      case _ => false
    }

    private def readAtom(cursor: Cursor): Read[Pre] = cursor.peek match {
      case Token.Name(name, position) =>
        readAnnotation(cursor.next).map { case (annotation, rest) =>
          (Pre.Ident(name, annotation, position), rest)
        }

      case Token.Symbol("(", _) =>
        readTerm(cursor.next).flatMap { case (inner, afterInner) =>
          expect(afterInner, ")").map(rest => (inner, rest))
        }

      case other => Left(SyntaxError("expected a name or '('", other.position))
    }

    private def readAnnotation(cursor: Cursor): Read[Option[Type]] =
      skip(cursor, ":") match {
        case Some(afterColon) =>
          readType(afterColon).map { case (ty, rest) => (Some(ty), rest) }
        case None => Right((None, cursor))
      }

    /* ---- types ---- */

    def readType(cursor: Cursor): Read[Type] =
      readAtomType(cursor).flatMap { case (domain, afterDomain) =>
        skip(afterDomain, "->") match {
          case Some(afterArrow) =>
            readType(afterArrow).map { case (codomain, rest) => (Type.fun(domain, codomain), rest) }
          case None => Right((domain, afterDomain))
        }
      }

    private def readAtomType(cursor: Cursor): Read[Type] = cursor.peek match {
      case Token.Name(name, _) if name.startsWith("'") =>
        Right((TyVar(name.drop(1)), cursor.next))

      case Token.Name(name, _) =>
        skip(cursor.next, "(") match {
          case Some(afterOpen) =>
            readTypeArguments(afterOpen, Nil).map { case (arguments, rest) =>
              (TyApp(name, arguments), rest)
            }
          case None => Right((TyApp(name, Nil), cursor.next))
        }

      case Token.Symbol("(", _) =>
        readType(cursor.next).flatMap { case (inner, afterInner) =>
          expect(afterInner, ")").map(rest => (inner, rest))
        }

      case other => Left(SyntaxError("expected a type", other.position))
    }

    private def readTypeArguments(cursor: Cursor, acc: List[Type]): Read[List[Type]] =
      readType(cursor).flatMap { case (argument, afterArgument) =>
        skip(afterArgument, ",") match {
          case Some(afterComma) => readTypeArguments(afterComma, argument :: acc)
          case None => expect(afterArgument, ")").map(rest => ((argument :: acc).reverse, rest))
        }
      }
  }

  /* --------------------------------------------------------------- elaboration */

  /**
   * Everything elaboration has worked out so far, carried from one step to the next.
   *
   * Three things and not one, because they answer to different questions: `counter` is how a
   * metavariable gets a name nothing else can have, `bindings` is what unification has settled
   * about those metavariables, and `freeTypes` is the rule that one free name has one type
   * throughout one term. They travel together because every step that changes one may change
   * another, and splitting them would put a second parameter on every signature to no end.
   *
   * `counter` never restarts and is never reused, so the name a refusal prints (`?4`) identifies
   * one metavariable of one parse. A test pins that text, which is the reason a step that mints
   * one has to say so.
   */
  private final case class Context(
    counter: Int,
    bindings: Map[String, Type],
    freeTypes: Map[String, Type]
  )

  private object Context {
    val empty: Context = Context(0, Map.empty, Map.empty)
  }

  /** A subterm typed, with what elaboration knew once it had been. */
  private final case class Inferred(typed: Typed, ty: Type, context: Context)

  /**
   * Types are worked out by unification, over metavariables that cannot be written down.
   *
   * A metavariable is a type variable whose name starts with `?`, which the lexer cannot produce,
   * so one can never collide with a type variable the text mentions. Any that survive to the end
   * are the ambiguous statement this parser refuses to guess at.
   *
   * What unification has worked out is carried in a [[Context]] that each step hands to the next,
   * rather than in fields this class mutates as it goes. The difference a reader sees is that
   * `resolve` and `substitute` now say in their signatures that they read the substitution and
   * `unify` says that it extends it, where the three used to be told apart only by reading them.
   * There is a difference in behaviour too, though nothing today depends on it: a failed `unify`
   * used to leave behind whatever it had bound before it failed, and now it leaves nothing, so a
   * caller that wanted to try a unification and carry on from before it would get what it asked
   * for. No caller does; every one of them stops at the first `Left`.
   */
  private final class Elaborator(theory: Theory, notation: Notation) {

    def run(pre: Pre, expected: Option[Type]): Either[LogicError, Term] =
      infer(pre, Map.empty, Context.empty).flatMap { inferred =>
        for {
          constrained <- constrain(inferred.ty, expected, inferred.context)
          settled <- settleNumerals(inferred.typed, constrained)
          term <- build(inferred.typed, Map.empty, settled)
          _ <- rejectUndetermined(term)
        } yield term
      }

    /**
     * Give every numeral its type where the theory leaves no choice about it.
     *
     * Between unification and building, and it has to be between them rather than inside either.
     * Inside `infer` the context has not spoken yet, and the numeral would fix a type the term
     * around it was going to disagree with. Inside `build` it is too late: the nodes above this one
     * have already had their types read off, so binding the metavariable here leaves them holding
     * the `?4` the application then refuses.
     *
     * A numeral whose type something else determined is left alone; one nothing determined is bound
     * only when the theory reads numerals at exactly one type, which [[expand]] explains.
     */
    private def settleNumerals(typed: Typed, context: Context): Either[LogicError, Context] =
      encodings match {
        case Vector((_, at)) =>
          numeralTypes(typed).foldLeft(Right(context): Either[LogicError, Context]) { (acc, ty) =>
            acc.flatMap(current =>
              if (Type.variables(resolve(ty, current)).exists(isMetavariable)) unify(ty, at, current)
              else Right(current)
            )
          }
        case _ => Right(context)
      }

    /** The type carried by every numeral in the tree, in the order they were written. */
    private def numeralTypes(typed: Typed): Vector[Type] = typed match {
      case Typed.Numeral(_, ty, _) => Vector(ty)
      case Typed.Apply(fn, argument) => numeralTypes(fn) ++ numeralTypes(argument)
      case Typed.Lambda(_, _, body) => numeralTypes(body)
      case Typed.Free(_, _) | Typed.Constant(_, _) | Typed.Overloaded(_, _, _, _) => Vector.empty
    }

    /* ---- inference ---- */

    private def infer(
      pre: Pre,
      bound: Map[String, Type],
      context: Context
    ): Either[LogicError, Inferred] =
      pre match {
        case Pre.Ident(name, annotation, position) =>
          identifier(name, annotation, position, bound, context)

        case Pre.Overloaded(symbol, candidates, position) =>
          overloaded(symbol, candidates, position, context)

        case Pre.Apply(fn, argument) =>
          infer(fn, bound, context).flatMap { inferredFn =>
            infer(argument, bound, inferredFn.context).flatMap { inferredArgument =>
              val (result, afterFresh) = fresh(inferredArgument.context)
              unify(inferredFn.ty, Type.fun(inferredArgument.ty, result), afterFresh)
                .map(next => Inferred(Typed.Apply(inferredFn.typed, inferredArgument.typed), result, next))
            }
          }

        case Pre.Lambda(name, annotation, body) =>
          val (binderType, afterBinder) = annotation match {
            case Some(declared) => (declared, context)
            case None => fresh(context)
          }
          infer(body, bound.updated(name, binderType), afterBinder).map { inner =>
            Inferred(
              Typed.Lambda(name, binderType, inner.typed),
              Type.fun(binderType, inner.ty),
              inner.context
            )
          }
      }

    private def identifier(
      name: String,
      annotation: Option[Type],
      position: Int,
      bound: Map[String, Type],
      context: Context
    ): Either[LogicError, Inferred] =
      bound.get(name) match {
        case Some(ty) =>
          constrain(ty, annotation, context).map(next => Inferred(Typed.Free(name, ty), ty, next))

        case None =>
          theory.constants.get(name) match {
            // A digit string is a numeral **before** it is a constant, and the order is the whole
            // point. The reals declare two constants literally named `0` and `1`, so a lookup first
            // would settle those two as the reals' whatever their context wanted, while `2` and up
            // went through the encoding and could be either. `Power 2 3` reading and
            // `NUM_ADD n 0` refusing "num and real cannot be the same type" is the shape of that,
            // and it is how this was found.
            case _ if name.forall(_.isDigit) && notation.numerals.nonEmpty =>
              numeral(BigInt(name), annotation, position, context)

            case Some(schema) =>
              val (instance, afterInstance) = instantiate(schema, context)
              constrain(instance, annotation, afterInstance)
                .map(next => Inferred(Typed.Constant(name, instance), instance, next))

            case None if name.head.isDigit =>
              Left(SyntaxError(
                s"no constant named $name; a numeral needs a theory that defines it", position))

            // A name the lexer produced always starts with a letter, a digit or an underscore, so
            // anything else here came from a notation. Those have to be constants of the theory
            // being parsed against; turning one into a free variable would read as a formula and
            // mean nothing.
            case None if !name.head.isLetter && name.head != '_' =>
              Left(TypeError(
                s"this theory declares no constant $name, so that notation is not available"))

            // Every occurrence of one free name in one term has one type, so the first occurrence
            // decides it and the rest unify against it. A metavariable is minted only where
            // neither a previous occurrence nor an annotation has already said what it is, which
            // is why the counter does not move on the other two paths.
            case None =>
              val (ty, afterType) = context.freeTypes.get(name) match {
                case Some(existing) => (existing, context)
                case None =>
                  annotation match {
                    case Some(declared) => (declared, context)
                    case None => fresh(context)
                  }
              }
              val recorded = afterType.copy(freeTypes = afterType.freeTypes.updated(name, ty))
              constrain(ty, annotation, recorded)
                .map(next => Inferred(Typed.Free(name, ty), ty, next))
          }
      }

    /**
     * A symbol several constants are written with, elaborated against the shape they share.
     *
     * The three ways this can go are the three the numerals already have, and two of them are
     * settled here while the third waits for `build`. **No candidate this theory declares** is a
     * refusal now, because nothing later can supply one. **One candidate** is not a choice and
     * becomes an ordinary constant, which is what lets the chain's single notation serve a
     * development built over the reals alone: `+` is declared at both types in the table and at one
     * type in that theory, and a text there reads exactly as it did before this existed. **More
     * than one** takes the shared shape and is decided in [[resolveOverload]] after unification.
     *
     * The shape is the least general type every candidate is an instance of, which for `+` at
     * `real -> real -> real` and `num -> num -> num` is `?a -> ?a -> ?a`. Getting the **same**
     * metavariable into all three positions is what makes this work rather than merely typecheck:
     * with three independent ones the arguments would settle two positions and leave the result
     * open, and the term would be refused for an undetermined type it plainly has.
     */
    private def overloaded(
      symbol: String,
      candidates: Vector[String],
      position: Int,
      context: Context
    ): Either[LogicError, Inferred] = {
      val declared = candidates.flatMap(name => theory.constants.get(name).map(name -> _))
      declared match {
        case Vector() =>
          Left(TypeError(
            s"this theory declares no constant the operator $symbol stands for, so that notation " +
              s"is not available; $symbol is written for " + candidates.mkString(", ")
          ))

        case Vector((name, schema)) =>
          val (instance, afterInstance) = instantiate(schema, context)
          Right(Inferred(Typed.Constant(name, instance), instance, afterInstance))

        case several =>
          val (shape, afterShape) = generalise(several.map { case (_, ty) => ty }, context)
          Right(Inferred(
            Typed.Overloaded(symbol, several.map { case (name, _) => name }, shape, position),
            shape,
            afterShape
          ))
      }
    }

    /**
     * The least general type every one of these is an instance of.
     *
     * Anti-unification, and the table it is keyed by is the whole of why it is not a fold over
     * `if (all agree) that else fresh`: subterms that differ **in the same way** in every position
     * get the same metavariable, so `real -> real -> real` against `num -> num -> num` comes out
     * `?a -> ?a -> ?a` and not `?a -> ?b -> ?c`. The second is a correct generalisation and is
     * useless here, for the reason [[overloaded]] gives.
     */
    private def generalise(types: Vector[Type], context: Context): (Type, Context) = {
      // The substitution and the context are threaded rather than held in a `var`, which is the
      // repository's rule and is also what makes the metavariable counter's movement readable:
      // a fresh one is minted exactly where a new pair of differing subterms is met.
      type State = (Map[Vector[Type], Type], Context)

      def walk(candidates: Vector[Type], state: State): (Type, State) =
        if (candidates.distinct.sizeIs == 1) (candidates.head, state)
        else
          candidates.head match {
            case TyApp(name, arguments)
                if candidates.forall {
                  case TyApp(other, others) => other == name && others.sizeIs == arguments.size
                  case _ => false
                } =>
              val (children, next) = arguments.indices.foldLeft((List.empty[Type], state)) {
                case ((seen, current), i) =>
                  val (child, after) = walk(
                    candidates.map {
                      case TyApp(_, others) => others(i)
                      case ty => ty
                    },
                    current
                  )
                  (seen :+ child, after)
              }
              (TyApp(name, children), next)

            case _ =>
              val (assigned, current) = state
              assigned.get(candidates) match {
                case Some(existing) => (existing, state)
                case None =>
                  val (variable, after) = fresh(current)
                  (variable, (assigned.updated(candidates, variable), after))
              }
          }

      val (shape, (_, context1)) = walk(types, (Map.empty, context))
      (shape, context1)
    }

    /**
     * Which candidate the settled type names, or a refusal that says why none does.
     *
     * The mirror of [[expand]] and refused in the same two ways, because the question is the same
     * question: a type nothing determined, and a type no candidate is declared at. The second is
     * the one that catches a real mistake rather than a vague text -- `x:num + y:real` settles the
     * shape at neither candidate's type and is told so, where before this existed the same text
     * was a type error about `real` and `num` deep inside an application.
     */
    private def resolveOverload(
      symbol: String,
      candidates: Vector[String],
      position: Int,
      ty: Type
    ): Either[LogicError, Term] = {
      val declared = candidates.flatMap(name => theory.constants.get(name).map(name -> _))
      if (Type.variables(ty).exists(isMetavariable))
        Left(TypeError(
          s"the type of the operator $symbol is not determined; annotate one of its arguments, " +
            "or write it where something says what they are. This theory reads " + symbol +
            " at: " + declared.map { case (_, at) => Show.show(at) }.mkString(", ")
        ))
      else
        declared.find { case (_, at) => at == ty } match {
          case Some((name, at)) => LogicError.lift(theory.constant(name, at))
          case None =>
            Left(TypeError(
              s"there is no $symbol at type ${Show.show(ty)}; the ones this theory has are at " +
                declared.map { case (_, at) => Show.show(at) }.mkString(", ")
            ))
        }
    }

    /** Unify against the type the writer annotated, where they annotated one. */
    private def constrain(
      ty: Type,
      annotation: Option[Type],
      context: Context
    ): Either[LogicError, Context] =
      annotation match {
        case Some(declared) => unify(ty, declared, context)
        case None => Right(context)
      }

    /**
     * A digit string, with its type left to the context and its encoding left with it.
     *
     * Until 2026-09-12 this decided both here, from the declared type of `1`, and its docstring
     * said why: *"numerals here belong to one theory and one type, and a polymorphic numeral would
     * need the elaborator to decide which."* The chain now declares two encodings, the reals' and
     * `num`'s, so the elaborator decides: the numeral takes a metavariable and [[expand]] reads it
     * back once unification has run. A numeral whose type nothing constrained is **refused** where
     * the theory offers a choice, which is the same rule this parser already applies to every other
     * undetermined type, and **taken** where it offers one encoding, because one encoding is not a
     * choice. [[expand]] carries the measurement behind that second half.
     *
     * The annotation is what a writer says it with when nothing else does: `3:num` was not a term
     * this parser read before, because a numeral's type was not a thing anybody could have an
     * opinion about. It is the escape hatch the refusal above needs to be fair.
     */
    private def numeral(
      value: BigInt,
      annotation: Option[Type],
      position: Int,
      context: Context
    ): Either[LogicError, Inferred] = {
      val (ty, afterFresh) = fresh(context)
      constrain(ty, annotation, afterFresh)
        .map(next => Inferred(Typed.Numeral(value, ty, position), ty, next))
    }

    /** The encodings this theory can actually read, each with the type its `one` is declared at. */
    private lazy val encodings: Vector[(NumeralNotation, Type)] =
      notation.numerals.flatMap(spec => theory.constants.get(spec.one).map(spec -> _))

    /**
     * A numeral as a term, in the binary encoding declared at its type.
     *
     * The inverse of [[NumeralNotation.valueOf]], which the printer uses, and a property test
     * asserts the two are inverse.
     */
    private def expand(value: BigInt, position: Int, ty: Type): Either[LogicError, Term] = {
      def digits(current: BigInt, spec: NumeralNotation, at: Type): Either[LogicError, Term] =
        if (current == 0) LogicError.lift(theory.constant(spec.zero, at))
        else if (current == 1) LogicError.lift(theory.constant(spec.one, at))
        else
          for {
            inner <- digits(current / 2, spec, at)
            name = if (current.testBit(0)) spec.bit1 else spec.bit0
            bit <- LogicError.lift(theory.constant(name, Type.fun(at, at)))
            applied <- LogicError.lift(Term.app(bit, inner))
          } yield applied

      encodings match {
        case Vector() =>
          Left(SyntaxError(
            s"this theory declares no ${notation.numerals.map(_.one).mkString(" and no ")}, " +
              "so numerals cannot be read",
            position
          ))

        // An undetermined type reaching here means more than one encoding was on offer, because
        // `settleNumerals` has already bound the one-encoding case. That is the only genuine
        // ambiguity there is, and it is measured rather than assumed: forty call sites in
        // `modules/theories` parse the bare text `"0"` or `"1"` against a signature holding only
        // the reals, and refusing those would have been a refusal with no second reading to
        // protect anybody from.
        case _ if Type.variables(ty).exists(isMetavariable) =>
          Left(TypeError(
            s"the type of the numeral $value is not determined; annotate it as `$value:<type>`, " +
              "or write it where something says what it is. This theory reads numerals at: " +
              encodings.map { case (_, at) => Show.show(at) }.mkString(", ")
          ))

        case _ =>
          encodings.find { case (_, at) => at == ty } match {
            case Some((spec, at)) => digits(value, spec, at)
            case None =>
              Left(TypeError(
                s"there are no numerals at type ${Show.show(ty)}; the ones this theory has are at " +
                  encodings.map { case (_, at) => Show.show(at) }.mkString(", ")
              ))
          }
      }
    }

    /** A constant's declared type with a fresh metavariable for each of its type variables. */
    private def instantiate(schema: Type, context: Context): (Type, Context) = {
      val (substitution, next) =
        Type.variables(schema).foldLeft((Map.empty[String, Type], context)) {
          case ((acc, current), name) =>
            val (ty, after) = fresh(current)
            (acc.updated(name, ty), after)
        }
      (Type.substitute(substitution, schema), next)
    }

    /* ---- unification ---- */

    private def fresh(context: Context): (Type, Context) = {
      val issued = context.counter + 1
      (TyVar(s"?$issued"), context.copy(counter = issued))
    }

    private def isMetavariable(name: String): Boolean = name.startsWith("?")

    @tailrec
    private def resolve(ty: Type, context: Context): Type = ty match {
      case TyVar(name) if isMetavariable(name) =>
        context.bindings.get(name) match {
          case Some(bound) => resolve(bound, context)
          case None => ty
        }
      case other => other
    }

    private def unify(left: Type, right: Type, context: Context): Either[LogicError, Context] =
      (resolve(left, context), resolve(right, context)) match {
        case (TyVar(name), other) if isMetavariable(name) => bind(name, other, context)
        case (other, TyVar(name)) if isMetavariable(name) => bind(name, other, context)

        case (TyVar(a), TyVar(b)) if a == b => Right(context)

        case (TyApp(operator1, arguments1), TyApp(operator2, arguments2))
          if operator1 == operator2 && arguments1.length == arguments2.length =>
          arguments1.zip(arguments2).foldLeft(Right(context): Either[LogicError, Context]) {
            case (acc, (a, b)) => acc.flatMap(current => unify(a, b, current))
          }

        case (a, b) =>
          Left(TypeError(s"${Show.show(a)} and ${Show.show(b)} cannot be the same type"))
      }

    private def bind(name: String, ty: Type, context: Context): Either[LogicError, Context] =
      if (ty == TyVar(name)) Right(context)
      else if (occurs(name, ty, context))
        Left(TypeError(
          s"the type of a term would have to contain itself: $name in ${Show.show(ty)}"))
      else Right(context.copy(bindings = context.bindings.updated(name, ty)))

    private def occurs(name: String, ty: Type, context: Context): Boolean =
      resolve(ty, context) match {
        case TyVar(other) => other == name
        case TyApp(_, arguments) => arguments.exists(occurs(name, _, context))
      }

    private def substitute(ty: Type, context: Context): Type = resolve(ty, context) match {
      case TyApp(operator, arguments) => TyApp(operator, arguments.map(substitute(_, context)))
      case other => other
    }

    /* ---- building ---- */

    /**
     * Build the kernel term.
     *
     * No renaming happens and none is needed, which is worth saying because a parser for a
     * name-carrying representation would need it here. A binder puts its name in `environment`,
     * so every occurrence inside its body resolves to that variable and never to an outer one of
     * the same name; and abstraction closes over a variable by identity, so the only occurrences
     * it can capture are the ones the environment produced. The name a binder was written with
     * does not survive into the term at all.
     */
    private def build(
      typed: Typed,
      environment: Map[String, FVar],
      context: Context
    ): Either[LogicError, Term] =
      typed match {
        case Typed.Free(name, ty) =>
          environment.get(name) match {
            case Some(variable) => Right(variable)
            case None => Right(Term.variable(name, substitute(ty, context)))
          }

        case Typed.Constant(name, ty) =>
          LogicError.lift(theory.constant(name, substitute(ty, context)))

        case Typed.Apply(fn, argument) =>
          for {
            fnTerm <- build(fn, environment, context)
            argumentTerm <- build(argument, environment, context)
            result <- LogicError.lift(Term.app(fnTerm, argumentTerm))
          } yield result

        case Typed.Lambda(name, ty, body) =>
          val variable = Term.variable(name, substitute(ty, context))
          build(body, environment.updated(name, variable), context)
            .flatMap(inner => LogicError.lift(Term.abs(variable, inner)))

        case Typed.Numeral(value, ty, position) =>
          expand(value, position, substitute(ty, context))

        case Typed.Overloaded(symbol, candidates, ty, position) =>
          resolveOverload(symbol, candidates, position, substitute(ty, context))
      }

    /**
     * Refuse a term whose type did not close, naming what left it open.
     *
     * This counted the undetermined types and named nothing until 2026-09-12, and the case that
     * says why that was not enough came from a consumer parsing against a theory of its own:
     * `\\i:num. Power (z:real) (Odd t i)` where `Odd` is one of ITS constants and not one of this
     * theory's. A name no theory declares is read as a free variable, so the term is well formed
     * and its type simply never closes, and the message said "Undetermined: 1 type" while the
     * actual mistake -- a constant that is not here -- appeared nowhere in it.
     *
     * **The sentence does more work than the list, and that is the consumer's finding rather than
     * mine.** `Odd, t` alone is two names, one of which the writer meant as a variable, and a
     * reader has to guess which is which; with the sentence, a name in that list that was supposed
     * to be a constant is the diagnosis. So the sentence is printed whenever anything is open, and
     * the list is what it points at.
     *
     * **And the remedy follows the diagnosis rather than being said always**, which is the second
     * correction from the same consumer and a defect in the first version of this message. It
     * opened with "annotate it" in every case. Where a name in the list is a constant the theory
     * does not declare, annotating is exactly what does not help -- no annotation makes `Odd`
     * exist -- and the reader who acts on the first thing they read loses the time this message
     * was written to save. So an open name asks for the theory that declares it first and for an
     * annotation second, and the count goes: `Undetermined: 1 type` was the whole message this
     * morning and is the least informative part of it now.
     *
     * Sorted, because a message that varies between runs of the same text is a message nobody can
     * pin in a test.
     *
     * **The order is what makes it survive being long, not the length**, and that was read back
     * from inside a real refusal rather than predicted here. This message is long, and inside a
     * refusal's own report the line scrolls; it works because the part that decides which branch
     * you are in -- the list -- arrives after six words. With twelve names the closing sentence
     * would run off the screen and the list would not, which is the right thing to lose. So an
     * edit that shortens this by moving the list later has made it worse while making it smaller.
     *
     * The clause that earns its place is "which no annotation can do for you": it **closes** the
     * wrong road rather than pointing at the right one, and the consumer that met this reported
     * that closing is what saved the trip. Pointing leaves every other road open.
     */
    private def rejectUndetermined(term: Term): Either[LogicError, Unit] = {
      val undetermined = Term.typeVariables(term).filter(isMetavariable)
      if (undetermined.isEmpty) Right(())
      else {
        val open = Term
          .freeVariables(term)
          .filter(variable => Type.variables(variable.ty).exists(isMetavariable))
          .map(_.name)
          .toVector
          .sorted

        if (open.isEmpty)
          Left(TypeError(
            "the type of this term is not determined; annotate it. " +
              s"Undetermined: ${undetermined.size} type${if (undetermined.size == 1) "" else "s"}"
          ))
        else
          Left(TypeError(
            "the type of this term is not determined. " +
              s"The names whose type is still open: ${open.mkString(", ")}. " +
              "A name this theory does not declare as a constant is read as a free variable, so a " +
              "constant you meant and this theory has not got appears in that list: if one of " +
              "them is that, parse against the theory that declares it, which no annotation can " +
              "do for you. If they are all variables you meant, annotate them."
          ))
      }
    }
  }
}
