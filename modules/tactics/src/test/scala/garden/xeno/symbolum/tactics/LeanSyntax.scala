package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.{Add, Div, Expr, Mul, Neg, Num, Pow, Sub, Var}

/**
 * Lean's infix arithmetic, read as an `Expr`. Syntax only.
 *
 * This exists so that a corpus written for another prover can be measured without anyone
 * transcribing it. Transcription is where a benchmark stops measuring: whoever copies the examples
 * chooses which ones to carry over and how to write them, and both choices flatter the system being
 * measured. Reading the upstream file means the corpus is what upstream wrote.
 *
 * == Syntax only, and why that matters ==
 *
 * Nothing here interprets. It recognises identifiers, whole literals, `+`, `-`, `*`, `/`, `^`,
 * parentheses, and the `=` between the two sides, and it builds the matching `Expr` nodes. Whether
 * the result can be said in the theory of the reals is [[Translate]]'s decision and is taken after:
 * `X^(-1)` becomes a `Pow` here and is refused there, by name, because that border does not expand
 * an inverse.
 *
 * That division of labour is the whole design. The one semantic step in this pipeline, expanding a
 * power into a product, already lives in `Translate`, is tested and is documented. A reader that
 * performed it would be a second implementation of it, and the two would have to be kept agreeing
 * about the exponent bound and about what a whole exponent is.
 *
 * == What it refuses ==
 *
 * Lean's notation is far larger than this: `•`, `↑`, `↔`, `→`, `∧`, `fun`, and unicode
 * operators generally. None of them are read, and the comparisons `<`, `>`, `≤` and `≥` are read
 * only by [[relation]] and never inside a side. Such a goal comes back as a `Left` naming what stopped it, and
 * the corpus counts it as unreadable rather than as something the prover failed at, which is the
 * honest place to put it.
 *
 * == Type ascriptions, and the asymmetry in how they are treated ==
 *
 * `(876544 : ℤ)` is read as the literal. `(x : α)` is not read at all.
 *
 * Dropping an ascription from a literal cannot change what the text says: a literal at a type is
 * that literal. Dropping one from anything else can, because an ascription is also how Lean writes
 * a coercion, and `(n : ℝ)` where `n : ℕ` denotes the image of `n` rather than `n` itself. Reading
 * that as `n` would be a semantic step taken silently, and it is the exact failure a translator has
 * to avoid: the kernel would go on to certify a true theorem about a statement nobody wrote.
 *
 * == Associativity ==
 *
 * `^` groups to the right, so `X^2^3` is `X^(2^3)`, which is what Lean means and is the whole of
 * why the grouping is worth stating: read the other way it would be `X^6`, a different statement
 * that this reader would hand on without complaint. Both readings are inside the fragment, since
 * `Translate` evaluates a closed exponent before expanding, so `X^(2^3)` is `X^8` and eight is
 * within `Translate.MaximumExponent`; what the grouping decides here is faithfulness and not reach.
 * Unary minus binds looser than `^` and tighter than `*`, so `-a^2` is `-(a^2)` and `-a * b` is
 * `(-a) * b`, again following Lean.
 */
object LeanSyntax {

  /**
   * The two sides a Lean equation claims equal, or why the text could not be read as one.
   *
   * The reason is a plain string rather than a [[TacticError]]: this is a reader for a benchmark
   * corpus and nothing downstream branches on the kind of failure, only on whether there was one.
   */
  def equation(text: String): Either[String, (Expr, Expr)] =
    try {
      val tokens = lex(text)
      val (left, rest) = climb(tokens, 1)
      rest match {
        case Tok.Op("=") :: tail =>
          val (right, remaining) = climb(tail, 1)
          if (remaining.nonEmpty) Left(s"trailing text after the right side: ${show(remaining)}")
          else Right((left, right))
        case Nil => Left("not an equation: no `=`")
        case other => Left(s"not an equation: ${show(other)} where `=` was expected")
      }
    } catch {
      case unreadable: Unreadable => Left(unreadable.getMessage)
      // A construction the algebra system refuses arrives here as a `Left` rather than as a stack
      // trace through the suite. Several constructors carry a `require`; none of them is reachable
      // from this grammar today, and the guard is for the corpus that reaches one.
      case refused: IllegalArgumentException => Left(s"the algebra system refused it: ${refused.getMessage}")
    }

  /** How two sides are compared. `>` and its non-strict twin are read as the same two the other way. */
  enum Comparison:
    case Less, LessEqual, Equal

  /** A Lean proposition that compares two expressions. */
  final case class Relation(comparison: Comparison, left: Expr, right: Expr)

  /**
   * The relation a text states, or why it could not be read as one.
   *
   * The same reader as [[equation]] with a wider set of separators, and the separators are the
   * only thing that is new: `<` and `=` are read, `\u2264` and `\u2265` are read, `>` and `\u2265` are
   * turned round rather than carried, and everything else Lean can put between two terms, `\u2260`
   * and `\u2194` among them, stops the read. An implication or a conjunction inside a proposition
   * stops it too, which is why a hypothesis written `h : a < b \u2192 c < d` counts as unreadable
   * rather than as something the prover failed at.
   */
  def relation(text: String): Either[String, Relation] =
    try {
      val tokens = lex(text)
      val (left, rest) = climb(tokens, 1)

      rest match {
        case Tok.Op(symbol) :: tail if Comparisons.contains(symbol) =>
          val (right, remaining) = climb(tail, 1)
          if (remaining.nonEmpty) Left(s"trailing text after the right side: ${show(remaining)}")
          else
            Right(symbol match {
              case "<" => Relation(Comparison.Less, left, right)
              case ">" => Relation(Comparison.Less, right, left)
              case "\u2264" => Relation(Comparison.LessEqual, left, right)
              case "\u2265" => Relation(Comparison.LessEqual, right, left)
              case _ => Relation(Comparison.Equal, left, right)
            })

        case Nil => Left("not a comparison: nothing between two sides")
        case other => Left(s"not a comparison: ${show(other)} where one was expected")
      }
    } catch {
      case unreadable: Unreadable => Left(unreadable.getMessage)
      case refused: IllegalArgumentException =>
        Left(s"the algebra system refused it: ${refused.getMessage}")
    }

  private val Comparisons: Set[String] = Set("<", ">", "\u2264", "\u2265", "=")

  /**
   * Thrown inside, caught at the boundary above, never seen by a caller.
   *
   * The alternative, threading `Either` through the lexer and both parser functions, was written
   * first and made the grammar unreadable: every recursive call became a for-comprehension and the
   * precedence climb, which is the only part worth reading, disappeared into the plumbing.
   */
  private final class Unreadable(why: String) extends RuntimeException(why)

  private enum Tok:
    case Name(text: String)
    case Number(value: BigInt)
    case Op(symbol: String)
    case Inverse
    case Colon
    case Open
    case Close

  private def show(tokens: List[Tok]): String = tokens.take(3).map {
    case Tok.Name(text) => text
    case Tok.Number(value) => value.toString
    case Tok.Op(symbol) => symbol
    case Tok.Inverse => "\u207b\u00b9"
    case Tok.Colon => ":"
    case Tok.Open => "("
    case Tok.Close => ")"
  }.mkString(" ")

  /**
   * Characters that make an operator. Unicode letters lex as names, which is deliberate: `ℤ` and
   * `α` are ordinary letters to `Character.isLetter`, so a type inside an ascription needs no
   * special case. A unicode *operator* is not a letter and stops the read, which is what should
   * happen.
   */
  private val Operators: String = "+-*/^=<>\u2264\u2265"

  private def lex(text: String): List[Tok] = {
    val out = collection.mutable.ListBuffer.empty[Tok]
    var i = 0
    while (i < text.length) {
      val c = text(i)
      if (c.isWhitespace) i += 1
      else if (c.isDigit) {
        val end = text.indexWhere(!_.isDigit, i) match { case -1 => text.length; case j => j }
        out += Tok.Number(BigInt(text.substring(i, end)))
        i = end
      } else if (c.isLetter || c == '_') {
        val end = text.indexWhere(ch => !(ch.isLetterOrDigit || ch == '_' || ch == '\''), i) match {
          case -1 => text.length
          case j => j
        }
        out += Tok.Name(text.substring(i, end))
        i = end
      } else if (c == '(') { out += Tok.Open; i += 1 }
      else if (c == ')') { out += Tok.Close; i += 1 }
      else if (c == ':') { out += Tok.Colon; i += 1 }
      // The one two-character token, and the only unicode operator read at all. It is `\u207b`
      // followed by `\u00b9`, and a lone `\u207b` is still unreadable rather than a minus: a
      // superscript minus that is not part of an inverse is something else, and guessing which
      // is the failure this reader exists to avoid.
      else if (c == '\u207b' && i + 1 < text.length && text(i + 1) == '\u00b9') {
        out += Tok.Inverse
        i += 2
      }
      else if (Operators.contains(c)) { out += Tok.Op(c.toString); i += 1 }
      else throw new Unreadable(s"cannot read '$c'")
    }
    out.toList
  }

  private def precedence(op: String): Int = op match {
    case "^" => 3
    case "*" | "/" => 2
    case "+" | "-" => 1
    case _ => 0
  }

  private val PowerPrecedence: Int = precedence("^")

  private def build(op: String, left: Expr, right: Expr): Expr = op match {
    case "+" => Add(Vector(left, right))
    case "-" => Sub(Vector(left, right))
    case "*" => Mul(Vector(left, right))
    case "/" => Div(Vector(left, right))
    case "^" => Pow(left, right)
    case other => throw new Unreadable(s"no such operator: $other")
  }

  /**
   * A term, then every `\u207b\u00b9` written after it.
   *
   * Postfix and tighter than everything, which is what it is in Lean: `2 * x\u207b\u00b9` is
   * `2 * (x\u207b\u00b9)` and `(a * b)\u207b\u00b9` needs its parentheses.
   *
   * It reads as `1 / x` rather than as `x ^ -1`, and the difference is not cosmetic. A negative
   * exponent is refused by `Translate`, which does not expand an inverse; a quotient is read, and
   * `1 / x` is `1 * inv x`, which is `inv x` in either normal form. So the reading is faithful and
   * lands inside the fragment instead of just outside it.
   */
  private def atom(tokens: List[Tok]): (Expr, List[Tok]) = {
    val (base, rest) = primary(tokens)
    inverted(base, rest)
  }

  @annotation.tailrec
  private def inverted(base: Expr, tokens: List[Tok]): (Expr, List[Tok]) = tokens match {
    case Tok.Inverse :: rest => inverted(Div(Vector(Num(1), base)), rest)
    case _ => (base, tokens)
  }

  private def primary(tokens: List[Tok]): (Expr, List[Tok]) = tokens match {
    case Tok.Op("-") :: rest =>
      val (argument, remaining) = climb(rest, PowerPrecedence)
      (Neg(argument), remaining)

    case Tok.Number(value) :: rest =>
      if (!value.isValidLong) throw new Unreadable(s"$value does not fit a literal")
      (Num(value.toLong), rest)

    case Tok.Name(text) :: rest => (Var(text), rest)

    case Tok.Open :: rest =>
      val (inner, remaining) = climb(rest, 1)
      remaining match {
        case Tok.Close :: after => (inner, after)
        case Tok.Colon :: after => (ascribed(inner), skipToClose(after))
        case other => throw new Unreadable(s"unclosed parenthesis at ${show(other)}")
      }

    case other => throw new Unreadable(s"expected a term, found ${show(other)}")
  }

  /** See the note on ascriptions above: on a literal it says nothing, on anything else it may. */
  private def ascribed(inner: Expr): Expr = inner match {
    case _: Num => inner
    case other => throw new Unreadable(s"a type ascription on $other could be a coercion")
  }

  private def skipToClose(tokens: List[Tok]): List[Tok] = {
    def go(remaining: List[Tok], depth: Int): List[Tok] = remaining match {
      case Nil => throw new Unreadable("unclosed type ascription")
      case Tok.Close :: rest if depth == 0 => rest
      case Tok.Close :: rest => go(rest, depth - 1)
      case Tok.Open :: rest => go(rest, depth + 1)
      case _ :: rest => go(rest, depth)
    }
    go(tokens, 0)
  }

  private def climb(tokens: List[Tok], minimum: Int): (Expr, List[Tok]) = {
    var (left, rest) = atom(tokens)
    var continue = true
    while (continue)
      rest match {
        case Tok.Op(symbol) :: tail if symbol != "=" && precedence(symbol) >= minimum =>
          // `^` groups to the right, so it recurses at its own precedence; everything else groups
          // to the left and recurses one above.
          val next = if (symbol == "^") precedence(symbol) else precedence(symbol) + 1
          val (right, remaining) = climb(tail, next)
          left = build(symbol, left, right)
          rest = remaining
        case _ => continue = false
      }
    (left, rest)
  }
}
