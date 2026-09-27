package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * Terms printed the way they are written on paper, using the same notation the parser reads.
 *
 * One table drives both directions, which is what makes the round trip meaningful: a formula that
 * prints one way and reads back as something else would mean the two disagreed about precedence,
 * and there is no second place for them to disagree in.
 *
 * The kernel has a printer of its own and this does not replace it. That one knows only equality,
 * because the kernel knows only equality, and it has to keep working when a term mentions no
 * constant this module has defined.
 *
 * Display only. Nothing here participates in a proof, and a term that prints wrongly is still the
 * term it was.
 */
object Show {

  /**
   * The names a binder of a given type is offered, in order.
   *
   * A term holds indices where a reader expects names, so every name a binder prints with is
   * invented here. Until 2026-09-26 the invention ignored the type and went x, y, z by position,
   * and 185 of the library's 784 statements bound a FUNCTION called `x`, counted on `docs/lemmas.md`
   * at `e0ac66a5` as every binder named `x` whose type has an arrow at its top: the mean value
   * theorem read `!x:real -> real. !y:real. !z:real. y < z ==> ...`. So the choice is by the
   * type, which the term does hold: a function is `f`, `g`, `h`, a proposition `p`, `q`, `r`, a
   * natural `n`, `m`, `k`, `i`, `j`, and everything else what it always was. The names the author
   * wrote are not recoverable, and this does not pretend to recover them.
   *
   * Public because a bound variable that is freed has to be named by somebody, and if that
   * somebody chooses differently then a goal written `!x y. ...` comes back as a statement about
   * `a1`, which is a statement the reader did not write. [[Logic.stripForall]] and the LaTeX
   * printer take their names from [[binderName]] so that the three agree.
   */
  def binderNames(binderType: Type): Vector[String] = binderType match {
    case TyApp("fun", List(_, _)) => Functions
    case TyApp("bool", Nil) => Propositions
    case TyApp("num", Nil) => Naturals
    case _ => Values
  }

  private val Functions: Vector[String] = Vector("f", "g", "h")
  private val Propositions: Vector[String] = Vector("p", "q", "r")
  private val Naturals: Vector[String] = Vector("n", "m", "k", "i", "j")
  private val Values: Vector[String] = Vector("x", "y", "z", "u", "v", "w")

  /**
   * The first name offered to a binder of this type that is not `taken`, going round the offer
   * again with a digit once it is spent: `f`, `g`, `h`, `f1`, `g1`, ...
   */
  def binderName(binderType: Type, taken: String => Boolean): String =
    firstFree(binderNames(binderType), taken)

  /**
   * The name of the index a large operator binds, `i`, `j`, `k`: a sum over `n` terms written
   * `\sum_{n < m}` would name its index the way the text names a bound, and the page already
   * writes `i` where the summand is not a lambda and there is no binder to name.
   */
  def indexName(taken: String => Boolean): String = firstFree(Indices, taken)

  private val Indices: Vector[String] = Vector("i", "j", "k")

  private def firstFree(names: Vector[String], taken: String => Boolean): String =
    Iterator
      .from(0)
      .map { index =>
        val round = index / names.length
        val base = names(index % names.length)
        if (round == 0) base else s"$base$round"
      }
      .find(candidate => !taken(candidate))
      .get

  /** A term, in the standard notation of the logic. */
  def show(term: Term): String = show(Notation.standard, term)

  /** A term, with the outermost expression unparenthesised. */
  def show(notation: Notation, term: Term): String =
    render(notation, term, Nil, 0, Term.freeVariables(term).map(_.name), annotateFree = false)

  /**
   * The same, with every free variable's type written at each occurrence.
   *
   * A free variable prints as a bare name, and a bare name carries no type: `x = y` between two
   * reals is text the reader refuses, because equality is polymorphic and nothing in those five
   * characters says at which type. A bound variable does not have the problem, since a binder
   * prints its own annotation. So this is not a second notation, it is the same one with the
   * information a free name cannot carry put back in.
   *
   * It is not what a person should normally read, which is why [[show]] is the default and this is
   * reached for only when the plain form does not read back. `Readback` is what decides that, by
   * trying, rather than by predicting which terms will need it.
   */
  def annotated(notation: Notation, term: Term): String =
    render(notation, term, Nil, 0, Term.freeVariables(term).map(_.name), annotateFree = true)

  /** A theorem, in the standard notation of the logic. */
  def show(theorem: Kernel.Thm): String = show(Notation.standard, theorem)

  /** A theorem, as `hypotheses |- conclusion`. */
  def show(notation: Notation, theorem: Kernel.Thm): String = {
    val hypotheses = theorem.hypotheses.map(hypothesis => show(notation, hypothesis))
    val left = if (hypotheses.isEmpty) "" else hypotheses.mkString(", ") + " "
    s"$left|- ${show(notation, theorem.conclusion)}"
  }

  /**
   * A type, in the syntax the parser reads.
   *
   * **A type variable is printed with its quote**, and until 2026-09-12 it was not. Everything in
   * the library was then over `real` or `num`, so no statement this printed had a type variable in
   * it; `Product` and `Word` landed fourteen that do, and every one of them printed `prod(a, b)`
   * where the parser reads `prod('a, 'b)` and refused the text with "no type operator named a".
   * Printing a type variable as a bare name also gave `TyVar("a")` and `TyApp("a", Nil)` one
   * spelling, which is two different types rendered the same.
   *
   * The exception is the elaborator's metavariables, which are type variables named `?1`, `?2` and
   * so on precisely because the lexer cannot produce such a name. They are not writable and a quote
   * in front of one would say they were, in the one place they are ever seen: the type error that
   * says two types cannot be the same. `ParserSpec` pins that message.
   */
  def show(ty: Type): String = ty match {
    case TyVar(name) => if (name.startsWith("?")) name else s"'$name"
    case TyApp("fun", List(domain, codomain)) =>
      val left = domain match {
        case TyApp("fun", List(_, _)) => s"(${show(domain)})"
        case _ => show(domain)
      }
      s"$left -> ${show(codomain)}"
    case TyApp(operator, Nil) => operator
    case TyApp(operator, arguments) =>
      s"$operator(${arguments.map(argument => show(argument)).mkString(", ")})"
  }

  private def render(
    notation: Notation,
    term: Term,
    bound: List[String],
    context: Int,
    avoid: Set[String],
    annotateFree: Boolean
  ): String = {
    def sub(inner: Term, innerContext: Int, innerBound: List[String] = bound): String =
      render(notation, inner, innerBound, innerContext, avoid, annotateFree)

    // A numeral prints as digits whatever it is made of, and this is checked before everything
    // else: the encoding is applications of BIT0 and BIT1, which would otherwise print as the
    // applications they are.
    val asNumeral = notation.valueOfNumeral(term)

    if (asNumeral.isDefined)
      // Annotated in the annotated form, for the reason a free variable is: a bare `1` carries no
      // type, and since 2026-09-12 there are two types it could be. `~(1 = 0)` is `ONE_NOT_ZERO`
      // over the reals and prints exactly so; put back to the widest signature that text is
      // genuinely ambiguous and is refused, which `NotationRoundTripSpec` is what found. This is
      // the same repair the free variables got and reached for by the same mechanism: `Readback`
      // tries the plain form first and comes here only when it does not read back.
      if (annotateFree) s"(${asNumeral.get}:${show(Term.typeOf(term))})"
      else asNumeral.get.toString
    else term match {
      case BVar(index) =>
        if (index < bound.length) bound(index) else s"?$index"

      // An annotated free variable is parenthesised, because the annotation binds to the name and
      // an unparenthesised `neg x:real` would have to be read by knowing that. The parentheses cost
      // nothing here: this form is produced only when the plain one did not read back.
      case FVar(name, ty) => if (annotateFree) s"($name:${show(ty)})" else name

      // A constant is annotated in the annotated form only when its type still has a type variable
      // in it, which is the one case the parser cannot fill in: it refuses to invent a type
      // variable rather than guessing, which is `Parser`'s stated design, and `Word.WitnessBody`
      // already carries `(WORD_PAD:'a)` for exactly that reason on the writing side.
      //
      // Narrow twice over, and the second narrowing is what keeps the text readable by a person.
      // The form is a fallback, reached only when the plain one did not read back, so a constant
      // whose type is ground is never annotated; and a constant in the **head** position of an
      // application is not annotated either, which the application case below arranges. Pinning one
      // occurrence is enough because the elaborator unifies, and annotating the head as well gave
      // `(WORD_LENGTH:word('a) -> num) (WORD_EMPTY:word('a)) = (0:num)` where the leaf alone gives
      // `WORD_LENGTH (WORD_EMPTY:word('a)) = 0`. Both read back and only one is worth printing.
      //
      // What it repairs is exactly that statement: closed, polymorphic, and with nothing beside the
      // constant to pin the element type from. Before 2026-09-16 nothing in the library was that
      // shape, so the claim that everything there reads back was true rather than checked.
      case Const(name, ty) =>
        if (annotateFree && Type.variables(ty).nonEmpty) s"($name:${show(ty)})" else name

      case App(Const(name, _), Abs(binderType, body))
        if notation.binderOf(name).isDefined =>
        binder(
          notation,
          notation.binderOf(name).get.symbol,
          binderType,
          body,
          bound,
          context,
          avoid,
          annotateFree
        )

      case App(Const(name, _), argument) if notation.prefixOf(name).isDefined =>
        val operator = notation.prefixOf(name).get
        // The argument is printed as if it were the argument of an application, so anything but a
        // name or a numeral is parenthesised. Its own precedence would be enough to read back
        // correctly, and gave `~x = 0` for `~(x = 0)`: right to the parser and wrong to a person.
        // The parentheses are for the person.
        parenthesise(
          s"${operator.symbol}${sub(argument, Notation.ApplicationPrecedence + 1)}",
          context,
          operator.precedence
        )

      case App(App(Const(name, _), left), right) if notation.infixOf(name).isDefined =>
        val operator = notation.infixOf(name).get
        val leftContext =
          if (operator.rightAssociative) operator.precedence + 1 else operator.precedence
        val rightContext =
          if (operator.rightAssociative) operator.precedence else operator.precedence + 1
        parenthesise(
          s"${sub(left, leftContext)} ${operator.symbol} ${sub(right, rightContext)}",
          context,
          operator.precedence
        )

      case App(fn, argument) =>
        // The head is printed without its annotation even in the annotated form, which is the
        // second half of the rule the `Const` case above states: its type variables are determined
        // by the arguments, and a curried head is an `App` whose own head reaches this case again.
        val head = fn match {
          case Const(name, _) => name
          case other => sub(other, Notation.ApplicationPrecedence)
        }
        parenthesise(
          s"$head ${sub(argument, Notation.ApplicationPrecedence + 1)}",
          context,
          Notation.ApplicationPrecedence
        )

      case Abs(binderType, body) =>
        val symbol = notation.binders.find(_.constant.isEmpty).map(_.symbol).getOrElse("\\")
        binder(notation, symbol, binderType, body, bound, context, avoid, annotateFree)
    }
  }

  private def binder(
    notation: Notation,
    symbol: String,
    binderType: Type,
    body: Term,
    bound: List[String],
    context: Int,
    avoid: Set[String],
    annotateFree: Boolean
  ): String = {
    val name = binderName(binderType, candidate => bound.contains(candidate) || avoid.contains(candidate))
    val inner = render(notation, body, name :: bound, 0, avoid, annotateFree)
    parenthesise(s"$symbol$name:${show(binderType)}. $inner", context, 0)
  }

  private def parenthesise(text: String, context: Int, precedence: Int): String =
    if (context > precedence) s"($text)" else text


}
