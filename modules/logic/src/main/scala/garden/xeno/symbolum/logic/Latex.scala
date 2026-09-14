package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * Terms written the way they are set in print, for a document a person reads.
 *
 * `Show` prints the form the parser reads back, and that is the form a reader has to be shown when
 * the question is whether the formalisation says what the source said. This is the other form: the
 * one with the symbols on it, for a page whose purpose is to be read rather than to be checked
 * character by character. The two are not alternatives. **What this produces does not read back and
 * is not meant to**, so it is only ever published beside the form that does; `Signature.readable`
 * is where that pairing is made and refused when the pair cannot be formed.
 *
 * == Why a template and not a symbol with a precedence ==
 *
 * `Notation` spells a constant as an infix, a prefix or a binder, which is all the parser needs and
 * is not all a page needs. Measured on 2026-09-13 over the widest signature: of the 82 constants
 * that appear in the library's statements, 22 have a notation entry and **60 do not**, and 231 of
 * the 278 statements name at least one of the 60. Three of them, `Sum`, `Prod` and `NUM_SUM`, want
 * a large operator with a bound index under it, `MAT2` wants a bracketed array of four entries, and
 * `NUM_CONG` wants a relation with a modulus set after it in parentheses. None of those is a symbol
 * between two arguments, so the table here holds a **template** with the arguments substituted into
 * it, and that is the whole of why this is not two more columns in `Notation`.
 *
 * == The three shapes, and the bracketing rule each carries ==
 *
 * A renderer has to decide where a bracket is needed, and in print that decision is not the one the
 * parser's precedences make: `\gcd(a, b)` brackets its own arguments, `\lvert x \rvert` delimits
 * itself, and `x^{n}` delimits the exponent and not the base. So a spelling carries the precedence
 * of what it produces and the precedence its arguments are rendered at, and the three constructors
 * are the three answers worth having:
 *
 *  - [[delimited]]: the result is an atom and never bracketed, and the arguments sit inside marks
 *    of the template's own, so they are never bracketed either. `\gcd(#1, #2)`, `\lvert #1 \rvert`.
 *  - [[operator]]: the result is bracketed by the context the way an infix is, and the arguments
 *    are rendered one tighter. `#1 \mid #2`, `#1 + #2`.
 *  - [[binding]]: argument one is a function, its binder is named and written under a large
 *    operator, and the body is rendered tightly enough that a sum inside a sum is bracketed.
 *    `\sum_{#b < #2} #1`.
 *
 * The precedences are `Notation`'s own, so the two renderings agree about which term is the
 * argument of which; where they disagree is only about whether that needs a bracket in print, and
 * they disagree on purpose.
 *
 * == What it does not do ==
 *
 * It does not check that the spelling is the right one. A table saying `\gcd` for `NUM_LCM` renders
 * every statement beautifully and wrongly, and nothing here can tell: that is a reading, and
 * `docs/reading-register.md` is where a constant's meaning is attested. What a test can hold is
 * narrower and is held: that every constant a statement names has a row, that no row names a
 * constant the signature does not have, and that the page is published only beside a form that
 * reads back.
 */
final class Latex private (
  val symbols: Map[String, String],
  val spellings: Map[String, Latex.Spelling]
) {

  /** This table with an ASCII symbol of the notation given its printed form. */
  def withSymbol(ascii: String, printed: String): Latex =
    new Latex(symbols + (ascii -> printed), spellings)

  /** This table with a constant spelled by a template that delimits itself and its arguments. */
  def delimited(constant: String, arity: Int, template: String): Latex =
    withSpelling(constant, Latex.Spelling(template, arity, Latex.Atom, 0, binds = false))

  /** This table with a constant spelled the way an infix is, bracketed by its context. */
  def operator(constant: String, arity: Int, template: String, precedence: Int): Latex =
    withSpelling(
      constant,
      Latex.Spelling(template, arity, precedence, precedence + 1, binds = false)
    )

  /**
   * This table with a constant whose first argument is a function, written under a large operator.
   *
   * `#b` is the name given to the binder, `#1` the body of the function and `#2` the bound. The
   * body is rendered at the precedence of an application, so a sum inside a sum is bracketed and
   * `\sum_{x < n} y + 1` cannot be read as a sum of `y` plus one.
   */
  def binding(constant: String, template: String): Latex =
    withSpelling(
      constant,
      Latex.Spelling(template, 2, Latex.LargeOperator, Notation.ApplicationPrecedence, binds = true)
    )

  private def withSpelling(constant: String, spelling: Latex.Spelling): Latex =
    new Latex(symbols, spellings + (constant -> spelling))

  /** Every constant this table spells, which is what a drift check compares against a theory. */
  def spelled: Set[String] = spellings.keySet

  /** A term, set in print. */
  def show(notation: Notation, term: Term): String =
    render(notation, term, Nil, 0, Term.freeVariables(term).map(_.name))

  /**
   * A type, set in print.
   *
   * The named types get the letter a reader expects and everything else gets its own name in
   * roman, which is the honest fallback: a type nobody has chosen a symbol for is better shown as
   * the word it is than as a letter that means something else to the reader.
   */
  def showType(ty: Type): String = ty match {
    case TyVar(name) => Latex.TypeVariables.getOrElse(name, s"\\mathrm{${Latex.escape(name)}}")
    case TyApp("fun", List(domain, codomain)) =>
      val left = domain match {
        case TyApp("fun", List(_, _)) => s"(${showType(domain)})"
        case _ => showType(domain)
      }
      s"$left \\to ${showType(codomain)}"
    // Bracketed on both sides where the side is itself a product or a function, because
    // `prod(prod(real, real), prod(real, real))` set flat is four reals in a row, and a two by two
    // matrix is not a quadruple. Found by reading `MAT_DET_MUL` off the printer rather than by
    // reasoning about the table.
    case TyApp("prod", List(left, right)) => s"${grouped(left)} \\times ${grouped(right)}"
    case TyApp(operator, Nil) =>
      Latex.Types.getOrElse(operator, s"\\mathrm{${Latex.escape(operator)}}")
    case TyApp(operator, arguments) =>
      val name = Latex.Types.getOrElse(operator, s"\\mathrm{${Latex.escape(operator)}}")
      s"$name(${arguments.map(showType).mkString(", ")})"
  }

  /** A type inside a product, bracketed where leaving it bare would lose where it ends. */
  private def grouped(ty: Type): String = ty match {
    case TyApp("prod", _) | TyApp("fun", _) => s"(${showType(ty)})"
    case other => showType(other)
  }

  private def render(
    notation: Notation,
    term: Term,
    bound: List[String],
    context: Int,
    avoid: Set[String]
  ): String = {
    def sub(inner: Term, innerContext: Int, innerBound: List[String] = bound): String =
      render(notation, inner, innerBound, innerContext, avoid)

    val asNumeral = notation.valueOfNumeral(term)

    if (asNumeral.isDefined) asNumeral.get.toString
    else
      spelledHere(notation, term, bound, avoid) match {
        case Some((text, precedence)) => bracket(text, context, precedence)
        case None =>
          term match {
            case BVar(index) => if (index < bound.length) bound(index) else s"?$index"
            case FVar(name, _) => Latex.escape(name)
            case Const(name, _) => s"\\mathrm{${Latex.escape(name)}}"

            case App(Const(name, _), Abs(binderType, body)) if notation.binderOf(name).isDefined =>
              binder(notation, notation.binderOf(name).get.symbol, binderType, body, bound, context, avoid)

            case App(Const(name, _), argument) if notation.prefixOf(name).isDefined =>
              val operator = notation.prefixOf(name).get
              bracket(
                s"${printed(operator.symbol)} ${sub(argument, Notation.ApplicationPrecedence + 1)}",
                context,
                operator.precedence
              )

            case App(App(Const(name, _), left), right) if notation.infixOf(name).isDefined =>
              val operator = notation.infixOf(name).get
              val leftContext =
                if (operator.rightAssociative) operator.precedence + 1 else operator.precedence
              val rightContext =
                if (operator.rightAssociative) operator.precedence else operator.precedence + 1
              bracket(
                s"${sub(left, leftContext)} ${printed(operator.symbol)} ${sub(right, rightContext)}",
                context,
                operator.precedence
              )

            // `f(x)` and not `f\,x`, which is how a page sets an application and is also the one
            // form that does not read as a product: `x\,\mathrm{suc}(y)` in `NUM_INDUCTION` was
            // the induction hypothesis at the successor and looked like a multiplication.
            case App(fn, argument) =>
              s"${sub(fn, Notation.ApplicationPrecedence)}(${sub(argument, 0)})"

            case Abs(binderType, body) =>
              binder(notation, "\\", binderType, body, bound, context, avoid)
          }
      }
  }

  /**
   * The term as its own spelling renders it, if it has one and is applied to all of its arguments.
   *
   * A constant applied to fewer arguments than its template has places falls through to the
   * ordinary application above and prints as its name, which is the only honest answer: a template
   * with an empty place in it would be a formula with a hole where the reader expects a term.
   */
  private def spelledHere(
    notation: Notation,
    term: Term,
    bound: List[String],
    avoid: Set[String]
  ): Option[(String, Int)] = {
    def spine(current: Term, collected: List[Term]): (Term, List[Term]) = current match {
      case App(fn, argument) => spine(fn, argument :: collected)
      case other => (other, collected)
    }

    spine(term, Nil) match {
      case (Const(name, _), arguments) =>
        spellings.get(name).filter(_.arity == arguments.length).map { spelling =>
          val text =
            if (spelling.binds) bindingText(notation, spelling, arguments, bound, avoid)
            else
              arguments.zipWithIndex.foldLeft(spelling.template) { case (template, (argument, at)) =>
                template.replace(
                  s"#${at + 1}",
                  render(notation, argument, bound, spelling.inner, avoid)
                )
              }
          (text, spelling.result)
        }

      case _ => None
    }
  }

  /** A large operator: the binder is named here, the body is rendered under that name. */
  private def bindingText(
    notation: Notation,
    spelling: Latex.Spelling,
    arguments: List[Term],
    bound: List[String],
    avoid: Set[String]
  ): String = arguments match {
    case Abs(_, body) :: limit :: Nil =>
      val name = freshName(bound, avoid)
      spelling.template
        .replace("#b", name)
        .replace("#1", render(notation, body, name :: bound, spelling.inner, avoid))
        .replace("#2", render(notation, limit, bound, 0, avoid))

    // A function that is not a lambda, `Sum f n`, has no binder to name, so it is written applied.
    case function :: limit :: Nil =>
      spelling.template
        .replace("#b", "i")
        .replace(
          "#1",
          s"${render(notation, function, bound, Notation.ApplicationPrecedence, avoid)}(i)"
        )
        .replace("#2", render(notation, limit, bound, 0, avoid))

    case _ => spelling.template
  }

  private def binder(
    notation: Notation,
    symbol: String,
    binderType: Type,
    body: Term,
    bound: List[String],
    context: Int,
    avoid: Set[String]
  ): String = {
    val name = freshName(bound, avoid)
    val inner = render(notation, body, name :: bound, 0, avoid)
    bracket(s"${printed(symbol)} $name \\colon ${showType(binderType)}.\\ $inner", context, 0)
  }

  private def printed(symbol: String): String = symbols.getOrElse(symbol, Latex.escape(symbol))

  private def bracket(text: String, context: Int, precedence: Int): String =
    if (context > precedence) s"\\left( $text \\right)" else text

  private def freshName(bound: List[String], avoid: Set[String]): String = {
    val names = Show.binderNames
    Iterator
      .from(0)
      .map { index =>
        val base = names(index % names.length)
        val round = index / names.length
        if (round == 0) base else s"$base$round"
      }
      .find(candidate => !bound.contains(candidate) && !avoid.contains(candidate))
      .get
  }
}

object Latex {

  /** The precedence of something that is bracketed by nothing. */
  val Atom: Int = Notation.ApplicationPrecedence + 10

  /**
   * The precedence of a large operator, between a comparison and a sum.
   *
   * A sum written `\sum_{i < n} f(i) + 1` reads, to a person, as the sum of `f(i) + 1` or as a sum
   * plus one depending on how it is set, and the two are different terms. Putting it below addition
   * means the bracket appears when the sum is an operand of one, which is the reading a page wants.
   */
  val LargeOperator: Int = 55

  /**
   * How a constant is set in print: a template, how many arguments it takes, and two precedences.
   *
   * `arity` is not decoration. A template is used only where the constant carries exactly that many
   * arguments, so a partial application prints as a name rather than as a formula with a hole.
   */
  final case class Spelling(
    template: String,
    arity: Int,
    result: Int,
    inner: Int,
    binds: Boolean
  )

  /** The letters a type variable is given, where a reader expects one. */
  private val TypeVariables: Map[String, String] =
    Map("a" -> "\\alpha", "b" -> "\\beta", "c" -> "\\gamma")

  /** The symbols the named types are set with. */
  private val Types: Map[String, String] =
    Map(
      "real" -> "\\mathbb{R}",
      "num" -> "\\mathbb{N}",
      "bool" -> "\\mathbb{B}",
      "ind" -> "\\mathbb{I}",
      "word" -> "\\mathrm{word}"
    )

  /** What has to be written with a backslash before it for TeX to set it as itself. */
  def escape(text: String): String =
    text.flatMap {
      case '_' => "\\_"
      case '#' => "\\#"
      case '%' => "\\%"
      case '&' => "\\&"
      case '{' => "\\{"
      case '}' => "\\}"
      case '$' => "\\$"
      case other => other.toString
    }

  /**
   * The connectives, the binders and the three constants `Classical` defines.
   *
   * Everything here belongs to `modules/logic`, and everything a development declares belongs to
   * the development: this table is extended where the constants are, for the reason `Notation` is.
   */
  val standard: Latex =
    new Latex(Map.empty, Map.empty)
      .withSymbol("==>", "\\Rightarrow")
      .withSymbol("\\/", "\\lor")
      .withSymbol("/\\", "\\land")
      .withSymbol("<=>", "\\iff")
      .withSymbol("~", "\\lnot")
      .withSymbol("!", "\\forall")
      .withSymbol("?", "\\exists")
      .withSymbol("\\", "\\lambda")
      .withSymbol("<=", "\\le")
      .withSymbol("*", "\\cdot")
      .delimited("T", 0, "\\top")
      .delimited("F", 0, "\\bot")
      // An operator and not delimited, at a precedence below every connective, because the else
      // branch ends the template and is therefore not delimited by it: `COND p a (b + c)` set as
      // `if p then a else b + c`, which as an operand of another sum reads as a conditional that
      // swallowed it. Found by the check in `LatexSpec`, which is the sixth row of this kind and
      // the only one outside the theories' own table.
      .operator(
        "COND",
        3,
        "\\mathrm{if}\\ #1\\ \\mathrm{then}\\ #2\\ \\mathrm{else}\\ #3",
        5
      )
      .delimited("select", 1, "\\varepsilon(#1)")
}
