package garden.xeno.symbolum.tactics

/**
 * A proof document as it is written: declarations, structured proofs, and where each one stands.
 *
 * This is the syntax of `docs/adr/0070` and nothing else. It reads text into a tree whose nodes carry
 * the line they were written on, and it decides nothing about terms, which stay strings here and are
 * read by the term parser at the point the elaborator knows which variables are fixed. Keeping the two
 * apart is what lets a proof write `n + 0 = n` after `fix n` and mean the `n` it fixed.
 *
 * == The shape ==
 *
 * {{{
 * define double := \x:num. x + x
 *
 * theorem ADD_ZERO_LEFT : !n:num. 0 + n = n
 * proof
 *   fix n
 *   induction n
 *   case zero:
 *     by arith
 *   case succ m ih:
 *     calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
 *          _         = SUC m       by rewrite ih
 *   end
 * qed
 * }}}
 *
 * One step is one line. Blocks are delimited by keywords and never by indentation: `proof ... qed`
 * around a proof, `case LABEL names: ... end` around the branches of a step that splits. Indentation
 * is free and is there for the reader. The reason is in the ADR: a writer, and an LLM in particular,
 * gets indentation wrong more often than a keyword, and an indentation error that reparses as a
 * different proof is a mistake the reader cannot see.
 *
 * `--` starts a comment that runs to the end of the line, where it is at the start of the line or
 * after a space. The term language has no `--`; a subtraction of a negation is written `a - -b`.
 *
 * == Recovery ==
 *
 * A syntax error ends the declaration it is in and nothing else: the reader skips to the next line
 * that starts a declaration at the top level and carries on, and the error is reported with its line.
 * A document with one malformed theorem still has every other theorem read and checked, which is the
 * property a long development needs and the one a line-by-line session did not have.
 */
object Document {

  /**
   * A document: the documents it imports, what was read, and what could not be.
   *
   * The imports are apart from the declarations because they are not checked, they are resolved:
   * what an import means is decided by whoever holds the other documents, which is `Workspace`, and
   * a document read on its own has nothing to resolve them against.
   */
  final case class Parsed(declarations: Vector[Declaration], errors: Vector[Malformed], imports: Vector[Import] = Vector.empty)

  /** `import NAME`: the document of that name, whose definitions and theorems this one may use. */
  final case class Import(line: Int, name: String)

  /** Text that does not read as the grammar, at a line, with what was expected there. */
  final case class Malformed(line: Int, reason: String)

  /** What can appear at the top level of a document. */
  enum Declaration(val line: Int) {

    /** `define NAME := TERM`, a conservative definition: it costs a name and no belief. */
    case Define(at: Int, name: String, body: String) extends Declaration(at)

    /** `theorem NAME : CLAIM`, with its proof. */
    case Theorem(at: Int, name: String, claim: String, proof: Justification) extends Declaration(at)
  }

  /** How a claim is established: one method on the same line, or a block of steps. */
  enum Justification {
    case By(line: Int, method: Method)
    case Block(line: Int, steps: Vector[Step], closed: Int)
  }

  /**
   * One step of a structured proof.
   *
   * The terminal steps are the ones that close the goal they are applied to: `by`, `show`, `calc`, and
   * the splitting steps, whose branches each close one of the goals they produce. The others change
   * the goal or add a fact and leave the rest of the block to finish the proof.
   */
  enum Step(val line: Int) {

    /** `fix x y`: the goal is `!x y. P`, and the proof goes on about fixed `x` and `y`. */
    case Fix(at: Int, names: Vector[String]) extends Step(at)

    /** `assume h k`: the goal is `A ==> B ==> C`, and the proof goes on with `h : A` and `k : B`. */
    case Assume(at: Int, names: Vector[String]) extends Step(at)

    /** `have h : P by M`, or with a block: `P` is proved here and is a fact from here on. */
    case Have(at: Int, name: String, claim: String, proof: Justification) extends Step(at)

    /** `show P by M`, or with a block, or `by M` with no claim: the goal is closed. */
    case Show(at: Int, claim: Option[String], proof: Justification) extends Step(at)

    /** `obtain x h from F`: `F` is `?x. P x`, and the proof goes on with a fixed `x` and `h : P x`. */
    case Obtain(at: Int, variable: String, hypothesis: String, from: String) extends Step(at)

    /** `cases h : P`, then `case pos:` with `h : P` and `case neg:` with `h : ~P`. */
    case Cases(at: Int, name: String, claim: String, branches: Vector[Branch]) extends Step(at)

    /** `cases h from F`, with `F : A \/ B`, then `case left:` with `h : A` and `case right:` with `h : B`. */
    case CasesFrom(at: Int, name: String, from: String, branches: Vector[Branch]) extends Step(at)

    /** `induction x [using LEMMA]`, then one branch per case of the induction principle. */
    case Induction(at: Int, variable: String, using: Option[String], branches: Vector[Branch]) extends Step(at)

    /** `split`: the goal is `A /\ B`, then `case left:` and `case right:`. */
    case Split(at: Int, branches: Vector[Branch]) extends Step(at)

    /** `left` or `right`: the goal is `A \/ B`, and the proof goes on with the side named. */
    case Choose(at: Int, left: Boolean) extends Step(at)

    /** `witness t`: the goal is `?x. P x`, and the proof goes on with `P t`. */
    case Witness(at: Int, term: String) extends Step(at)

    /** `rewrite F, G`: the goal is rewritten with the equations named, and the proof goes on. */
    case Rewrite(at: Int, facts: Vector[String]) extends Step(at)

    /**
     * `apply L`: the goal is an instance of what `L` concludes, and the proof goes on with what `L`
     * assumes. Branches numbered from 1 when it assumes more than one thing.
     */
    case Apply(at: Int, lemma: String, branches: Vector[Branch]) extends Step(at)

    /** `calc a = b by M` and then `_ = c by M` lines: a chain whose ends are the goal. */
    case Calc(at: Int, links: Vector[Link]) extends Step(at)
  }

  /** `case LABEL names:`, and the steps up to the next `case` or the `end` of the group. */
  final case class Branch(line: Int, label: String, names: Vector[String], steps: Vector[Step])

  /** One link of a `calc`: `claim` is written in full, the leading `_` already replaced. */
  final case class Link(line: Int, claim: String, method: Method)

  /** How one claim is settled at one step. */
  enum Method {

    /** `auto [from F, G]`: the tactic surface, `Prove`, over the goal with the facts named as hypotheses. */
    case Auto(from: Vector[String])

    /** `ring`: `RING`, which decides equations of commutative rings. */
    case Ring

    /** `linarith [from F, G]`: `LINARITH` over the reals, with the facts named as hypotheses. */
    case Linarith(from: Vector[String])

    /** `arith [from F, G]`: linear arithmetic over the naturals, with the facts named. */
    case Arith(from: Vector[String])

    /** `rewrite F, G`: the goal rewritten with the equations named until it is `T` or `t = t`. */
    case Rewrite(facts: Vector[String])

    /** `exact F`: the goal is the fact, or an instance of it. */
    case Exact(fact: String)

    /** `apply L`: the goal is an instance of what `L` concludes and `L` owes nothing more. */
    case Apply(lemma: String)

    /** `A then B`: `A` changes the goal and `B` closes what is left. Only `rewrite` changes a goal. */
    case Then(first: Method, second: Method)

    /** `first A | B`: the first that settles the goal, and every refusal if none does. */
    case First(alternatives: Vector[Method])
  }

  /** The words a proof step starts with, which are also what `read` recognises. */
  val StepKeywords: Vector[String] =
    Vector("fix", "assume", "have", "show", "by", "obtain", "cases", "induction", "split", "left", "right",
      "witness", "rewrite", "apply", "calc")

  /**
   * What a document is called: its file name without `.sym`, and what an `import` names.
   *
   * One word, so that a name is a file name on every system and never a path: an import cannot
   * reach outside the directory its documents are in.
   */
  val DocumentName: scala.util.matching.Regex = "[A-Za-z][A-Za-z0-9_]*".r

  /**
   * `cases NAME from FACT`, told apart from `cases NAME : CLAIM` by having no `:` and the word
   * `from` where the colon would be. A claim is a term, and `from` is no word of the term language.
   */
  private val CasesFromShape: scala.util.matching.Regex = "([^\\s:]+)\\s+from\\s+([^\\s:]+)".r

  /** The words a method starts with. */
  val MethodKeywords: Vector[String] =
    Vector("auto", "ring", "linarith", "arith", "rewrite", "exact", "apply", "first")

  /* ------------------------------------------------------------------ reading */

  /** Read a document. */
  def read(text: String): Parsed = {
    val lines = text.linesIterator.zipWithIndex.map { case (raw, index) => Line(index + 1, stripComment(raw).trim) }
      .filter(_.text.nonEmpty).toVector
    new Reader(lines).document
  }

  private final case class Line(number: Int, text: String) {
    def keyword: String = text.takeWhile(c => !c.isWhitespace && c != ':')
    def rest: String = text.drop(keyword.length).trim
  }

  /** The text before `--`, where `--` starts the line or follows whitespace. */
  private def stripComment(raw: String): String =
    raw.indices.find(i => raw.startsWith("--", i) && (i == 0 || raw(i - 1).isWhitespace)) match {
      case Some(at) => raw.take(at)
      case None => raw
    }

  /**
   * The reader, as functions from a position in the lines to what was read there and the position
   * after it, or the syntax error that stopped it.
   *
   * No state: a position is an index into `lines`, every function returns the next one, and a
   * failure is a value that carries its own line. The one place a failure is recovered from is
   * `document`, which skips to the next declaration and carries on.
   */
  private final class Reader(lines: Vector[Line]) {
    private type Read[A] = Either[Malformed, (A, Int)]

    private val Declarations = Set("import", "define", "theorem")

    private def lastLine: Int = lines.lastOption.map(_.number).getOrElse(0)
    private def at(position: Int): Option[Line] = lines.lift(position)
    private def fail(line: Int, message: String): Either[Malformed, Nothing] = Left(Malformed(line, message))
    private def check(ok: Boolean, line: Int, message: => String): Either[Malformed, Unit] =
      if (ok) Right(()) else fail(line, message)

    /**
     * Every import and declaration that reads, and an error for each one that does not.
     *
     * Imports come first. One written after a declaration is refused rather than taken, because
     * what a declaration can cite would otherwise depend on where in the file a line was moved to,
     * and a reader looks for what a document builds on at its top, as in every language with them.
     */
    def document: Parsed = {
      @annotation.tailrec
      def go(position: Int, imports: Vector[Import], declarations: Vector[Declaration], errors: Vector[Malformed]): Parsed =
        if (position >= lines.size) Parsed(declarations, errors, imports)
        else {
          val line = lines(position)
          if (line.keyword == "import") {
            val read = for {
              _ <- check(declarations.isEmpty && !errors.exists(error => error.line < line.number && !isImportError(error)), line.number,
                "`import` comes before every `define` and `theorem`: move it to the top of the document")
              named <- documentName(line)
              _ <- imports.find(_.name == named).fold(Right(()): Either[Malformed, Unit])(earlier =>
                fail(line.number, s"$named is already imported on line ${earlier.line}"))
            } yield Import(line.number, named)
            read match {
              case Right(taken) => go(position + 1, imports :+ taken, declarations, errors)
              case Left(error) => go(position + 1, imports, declarations, errors :+ error)
            }
          } else
            declaration(position) match {
              case Right((declaration, next)) => go(next, imports, declarations :+ declaration, errors)
              case Left(error) =>
                // Skip to the next line that starts a declaration at the top level. The line that
                // began this one is always passed over, so the reader always moves.
                val resume = lines.indexWhere(line => Declarations.contains(line.keyword), position + 1)
                go(if (resume < 0) lines.size else resume, imports, declarations, errors :+ error)
            }
        }
      go(0, Vector.empty, Vector.empty, Vector.empty)
    }

    /** Whether an error was met on an import line, which does not end the run of imports. */
    private def isImportError(error: Malformed): Boolean =
      lines.find(_.number == error.line).exists(_.keyword == "import")

    /** The name an import line gives, which is a document's file name without `.sym`. */
    private def documentName(line: Line): Either[Malformed, String] =
      if (line.rest.isEmpty) fail(line.number, "`import` wants the name of a document")
      else if (DocumentName.matches(line.rest)) Right(line.rest)
      else fail(line.number, s"`${line.rest}` is not the name of a document: one word of letters, digits and `_`, starting with a letter")

    private def declaration(position: Int): Read[Declaration] = {
      val line = lines(position)
      line.keyword match {
        case "define" =>
          split(line, line.rest, ":=", "define NAME := TERM").map { case (name, body) =>
            (Declaration.Define(line.number, name, body), position + 1)
          }
        case "theorem" =>
          for {
            parts <- split(line, line.rest, ":", "theorem NAME : CLAIM")
            (name, rest) = parts
            (claim, written) = trailingBy(rest)
            read <- written match {
              case Some(text) => method(line, text).map(m => (Justification.By(line.number, m), position + 1))
              case None => block(line, position + 1)
            }
          } yield (Declaration.Theorem(line.number, name, claim, read._1), read._2)
        case other =>
          fail(line.number, s"a document holds `import`, `define` and `theorem` at its top level, and this line starts with `$other`")
      }
    }

    /** `proof`, steps, `qed`, starting at `position`, after the line that asked for it. */
    private def block(opener: Line, position: Int): Read[Justification] =
      at(position) match {
        case Some(line) if line.text == "proof" =>
          steps(position + 1, Set("qed")).flatMap { case (read, next) =>
            at(next) match {
              case Some(end) if end.text == "qed" => Right((Justification.Block(line.number, read, end.number), next + 1))
              case Some(other) => fail(other.number, s"expected `qed` to close the proof opened on line ${line.number}")
              case None => fail(lastLine, s"the proof opened on line ${line.number} has no `qed`")
            }
          }
        case Some(line) =>
          fail(line.number, s"line ${opener.number} has no `by`, so a proof was expected here: write `proof` on its own line")
        case None =>
          fail(opener.number, "this has no `by`, so a proof was expected after it, and the document ends")
      }

    /** Steps until a line that begins with one of `stops`, which is left for the caller. */
    private def steps(position: Int, stops: Set[String]): Read[Vector[Step]] = {
      @annotation.tailrec
      def go(current: Int, read: Vector[Step]): Read[Vector[Step]] =
        at(current) match {
          case Some(line) if !stops.contains(line.keyword) && !stops.contains(line.text) =>
            step(current) match {
              case Right((next, after)) => go(after, read :+ next)
              case Left(error) => Left(error)
            }
          case _ => Right((read, current))
        }
      go(position, Vector.empty)
    }

    private def isName(text: String): Boolean =
      text.nonEmpty && (text.head.isLetter || text.head == '_') && text.forall(c => c.isLetterOrDigit || c == '_' || c == '\'')

    private def names(line: Line, text: String, what: String): Either[Malformed, Vector[String]] = {
      val found = text.split("\\s+").filter(_.nonEmpty).toVector
      for {
        _ <- check(found.nonEmpty, line.number, s"`${line.keyword}` wants $what")
        _ <- found.find(name => !isName(name)).fold(Right(()): Either[Malformed, Unit])(bad => fail(line.number, s"`$bad` is not a name"))
      } yield found
    }

    private def name(line: Line, text: String): Either[Malformed, String] =
      if (isName(text)) Right(text) else fail(line.number, s"`$text` is not a name")

    private def step(position: Int): Read[Step] = {
      val line = lines(position)
      val next = position + 1
      def alone[A](result: Either[Malformed, A]): Read[A] = result.map(value => (value, next))
      line.keyword match {
        case "fix" => alone(names(line, line.rest, "the names of the variables it fixes").map(Step.Fix(line.number, _)))
        case "assume" => alone(names(line, line.rest, "a name for each hypothesis it assumes").map(Step.Assume(line.number, _)))
        case "have" =>
          for {
            parts <- split(line, line.rest, ":", "have NAME : CLAIM by METHOD")
            (named, rest) = parts
            _ <- name(line, named)
            (claim, written) = trailingBy(rest)
            proof <- justification(line, written, next)
          } yield (Step.Have(line.number, named, claim, proof._1), proof._2)
        case "show" =>
          val (claim, written) = trailingBy(line.rest)
          for {
            _ <- check(claim.nonEmpty, line.number, "`show` wants the claim it closes; `by METHOD` alone closes the goal as it stands")
            proof <- justification(line, written, next)
          } yield (Step.Show(line.number, Some(claim), proof._1), proof._2)
        case "by" =>
          for {
            _ <- check(line.rest.nonEmpty, line.number, "`by` wants a method")
            settled <- method(line, line.rest)
          } yield (Step.Show(line.number, None, Justification.By(line.number, settled)), next)
        case "obtain" =>
          val split = line.rest.indexOf(" from ")
          for {
            _ <- check(split >= 0, line.number, "`obtain` is written `obtain x h from FACT`")
            bound <- names(line, line.rest.take(split), "a variable and a hypothesis name")
            _ <- check(bound.size == 2, line.number, "`obtain` names exactly one variable and one hypothesis: `obtain x h from FACT`")
            from <- single(line, line.keyword, line.rest.drop(split + 6), "the fact it opens")
          } yield (Step.Obtain(line.number, bound(0), bound(1), from), next)
        case "cases" if CasesFromShape.matches(line.rest) =>
          val CasesFromShape(named, from) = line.rest: @unchecked
          for {
            _ <- name(line, named)
            _ <- name(line, from)
            grouped <- branches(line, next)
          } yield (Step.CasesFrom(line.number, named, from, grouped._1), grouped._2)
        case "cases" =>
          for {
            parts <- split(line, line.rest, ":", "cases NAME : CLAIM, or cases NAME from FACT")
            (named, claim) = parts
            _ <- name(line, named)
            grouped <- branches(line, next)
          } yield (Step.Cases(line.number, named, claim, grouped._1), grouped._2)
        case "induction" =>
          line.rest.split("\\s+").filter(_.nonEmpty).toVector match {
            case Vector(variable) if isName(variable) =>
              branches(line, next).map { case (grouped, after) => (Step.Induction(line.number, variable, None, grouped), after) }
            case Vector(variable, "using", lemma) if isName(variable) =>
              branches(line, next).map { case (grouped, after) => (Step.Induction(line.number, variable, Some(lemma), grouped), after) }
            case _ => fail(line.number, "`induction` is written `induction x` or `induction x using LEMMA`")
          }
        case "split" =>
          for {
            _ <- check(line.rest.isEmpty, line.number, "`split` takes nothing after it")
            grouped <- branches(line, next)
          } yield (Step.Split(line.number, grouped._1), grouped._2)
        case "left" | "right" =>
          for {
            _ <- check(line.rest.isEmpty, line.number, s"`${line.keyword}` takes nothing after it")
          } yield (Step.Choose(line.number, line.keyword == "left"), next)
        case "witness" =>
          for {
            _ <- check(line.rest.nonEmpty, line.number, "`witness` wants the term")
          } yield (Step.Witness(line.number, line.rest), next)
        case "rewrite" => alone(list(line, line.keyword, line.rest, "the equations it rewrites with").map(Step.Rewrite(line.number, _)))
        case "apply" =>
          for {
            lemma <- single(line, line.keyword, line.rest, "the lemma it applies")
            grouped <- if (at(next).exists(_.keyword == "case")) branches(line, next) else Right((Vector.empty, next))
          } yield (Step.Apply(line.number, lemma, grouped._1), grouped._2)
        case "calc" => links(line, next).map { case (read, after) => (Step.Calc(line.number, read), after) }
        case "case" | "end" =>
          fail(line.number, s"`${line.keyword}` belongs to the branches of `cases`, `induction`, `split` or `apply`, and none is open here")
        case "qed" => fail(line.number, "`qed` with no proof open")
        case other => fail(line.number, s"no step `$other`; a step is one of ${StepKeywords.mkString(", ")}")
      }
    }

    /** `by METHOD` on the line, or a block starting at `position`. */
    private def justification(line: Line, written: Option[String], position: Int): Read[Justification] =
      written match {
        case Some(text) => method(line, text).map(settled => (Justification.By(line.number, settled), position))
        case None => block(line, position)
      }

    /** `case ...:` groups starting at `position`, up to `end`. */
    private def branches(opener: Line, position: Int): Read[Vector[Branch]] = {
      def branch(head: Line, current: Int): Read[Branch] = {
        val body = head.rest
        val words = body.dropRight(1).trim.split("\\s+").filter(_.nonEmpty).toVector
        for {
          _ <- check(body.endsWith(":"), head.number, "a branch is written `case LABEL names:`, ending with a colon")
          _ <- check(words.nonEmpty, head.number, "a branch wants its label: `case LABEL names:`")
          _ <- words.drop(1).find(word => !isName(word)).fold(Right(()): Either[Malformed, Unit])(bad => fail(head.number, s"`$bad` is not a name"))
          read <- steps(current + 1, Set("case", "end", "qed"))
        } yield (Branch(head.number, words.head, words.tail, read._1), read._2)
      }
      @annotation.tailrec
      def go(current: Int, read: Vector[Branch]): Read[Vector[Branch]] =
        at(current) match {
          case Some(head) if head.keyword == "case" =>
            branch(head, current) match {
              case Right((next, after)) => go(after, read :+ next)
              case Left(error) => Left(error)
            }
          case Some(line) if line.text == "end" => Right((read, current + 1))
          case Some(line) => fail(line.number, s"the branches opened on line ${opener.number} end with `end`")
          case None => fail(lastLine, s"the branches opened on line ${opener.number} have no `end`")
        }
      go(position, Vector.empty)
    }

    /** The first link on the `calc` line and every `_` line after it. */
    private def links(opener: Line, position: Int): Read[Vector[Link]] = {
      def link(line: Line, text: String, previous: Option[String]): Either[Malformed, (Link, String)] = {
        val (claim, written) = trailingBy(text)
        for {
          body <- written.toRight(Malformed(line.number, "every link of a `calc` ends with `by METHOD`"))
          _ <- check(previous.isEmpty || claim.startsWith("_"), line.number,
            "a link after the first starts with `_`, which stands for where the last one ended")
          settled <- method(line, body)
          right <- rightOf(line, claim)
        } yield {
          val full = previous.fold(claim)(last => s"($last)${claim.drop(1)}")
          (Link(line.number, full, settled), right)
        }
      }
      @annotation.tailrec
      def go(current: Int, read: Vector[Link], right: String): Read[Vector[Link]] =
        at(current) match {
          case Some(line) if line.text.startsWith("_") =>
            link(line, line.text, Some(right)) match {
              case Right((next, after)) => go(current + 1, read :+ next, after)
              case Left(error) => Left(error)
            }
          case _ => Right((read, current))
        }
      link(opener, opener.rest, None).flatMap { case (first, right) => go(position, Vector(first), right) }
    }

    /**
     * What a link ends with, as text: everything after its relation.
     *
     * The relation is the first one at the top level, outside parentheses, so `f (a = b) = c` ends
     * with `c`. It is text and not a term because the next link is read with it substituted, by the
     * elaborator, at the point the fixed variables are known.
     */
    private def rightOf(line: Line, claim: String): Either[Malformed, String] = {
      // `==>` is an implication and not a relation of a chain, so it is stepped over whole; `<=`
      // and `>=` are read before `<`, `>` and `=`, so a non-strict order is never taken for its
      // strict half followed by an equation.
      @annotation.tailrec
      def scan(i: Int, depth: Int): Option[(Int, Int)] =
        if (i >= claim.length) None
        else claim(i) match {
          case '(' => scan(i + 1, depth + 1)
          case ')' => scan(i + 1, depth - 1)
          case _ if depth != 0 => scan(i + 1, depth)
          case _ if claim.startsWith("==>", i) => scan(i + 3, depth)
          case _ if claim.startsWith("<=", i) || claim.startsWith(">=", i) => Some((i, 2))
          case '<' | '>' | '=' => Some((i, 1))
          case _ => scan(i + 1, depth)
        }
      scan(0, 0) match {
        case Some((found, size)) => Right(claim.drop(found + size).trim)
        case None => fail(line.number, "a link of a `calc` is a relation, `a = b`, `a <= b` or `a < b`")
      }
    }

    /** One method. `first` binds loosest, then `then`. */
    private def method(line: Line, text: String): Either[Malformed, Method] = {
      val trimmed = text.trim
      // `first rewrite A then ring | auto` is two alternatives, the first of them a `then`.
      val chained = trimmed.indexOf(" then ")
      if (trimmed.startsWith("first ")) {
        val alternatives = trimmed.drop(6).split("\\|").map(_.trim).filter(_.nonEmpty).toVector
        for {
          _ <- check(alternatives.size >= 2, line.number, "`first` is written `first A | B`, with at least two methods")
          read <- sequence(alternatives.map(method(line, _)))
        } yield Method.First(read)
      } else if (chained >= 0)
        for {
          first <- method(line, trimmed.take(chained))
          second <- method(line, trimmed.drop(chained + 6))
        } yield Method.Then(first, second)
      else {
        val keyword = trimmed.takeWhile(!_.isWhitespace)
        val rest = trimmed.drop(keyword.length).trim
        def from: Either[Malformed, Vector[String]] =
          if (rest.isEmpty) Right(Vector.empty)
          else if (rest.startsWith("from ")) list(line, keyword, rest.drop(5), "the facts it uses")
          else fail(line.number, s"`$keyword` is written `$keyword` or `$keyword from F, G`")
        keyword match {
          case "auto" => from.map(Method.Auto(_))
          case "ring" => check(rest.isEmpty, line.number, "`ring` takes nothing after it").map(_ => Method.Ring)
          case "linarith" => from.map(Method.Linarith(_))
          case "arith" => from.map(Method.Arith(_))
          case "rewrite" => list(line, keyword, rest, "the equations it rewrites with").map(Method.Rewrite(_))
          case "exact" => single(line, keyword, rest, "the fact").map(Method.Exact(_))
          case "apply" => single(line, keyword, rest, "the lemma").map(Method.Apply(_))
          case "first" => fail(line.number, "`first` is written `first A | B`, with at least two methods")
          case other => fail(line.number, s"no method `$other`; a method is one of ${MethodKeywords.mkString(", ")}")
        }
      }
    }

    private def sequence[A](reads: Vector[Either[Malformed, A]]): Either[Malformed, Vector[A]] =
      reads.foldLeft(Right(Vector.empty): Either[Malformed, Vector[A]])((acc, read) => acc.flatMap(done => read.map(done :+ _)))

    /** Names separated by commas, for `keyword`, which is the step or the method that wants them. */
    private def list(line: Line, keyword: String, text: String, what: String): Either[Malformed, Vector[String]] = {
      val found = text.split(",").map(_.trim).filter(_.nonEmpty).toVector
      for {
        _ <- check(found.nonEmpty, line.number, s"`$keyword` wants $what")
        _ <- found.find(name => !isName(name)).fold(Right(()): Either[Malformed, Unit])(bad => fail(line.number, s"`$bad` is not a name"))
      } yield found
    }

    /** One name, for `keyword`, which is the step or the method that wants it. */
    private def single(line: Line, keyword: String, text: String, what: String): Either[Malformed, String] = {
      val trimmed = text.trim
      for {
        _ <- check(trimmed.nonEmpty, line.number, s"`$keyword` wants $what")
        named <- name(line, trimmed)
      } yield named
    }

    private def split(line: Line, text: String, separator: String, shape: String): Either[Malformed, (String, String)] = {
      val found = text.indexOf(separator)
      val left = if (found < 0) "" else text.take(found).trim
      val right = if (found < 0) "" else text.drop(found + separator.length).trim
      check(found >= 0 && left.nonEmpty && right.nonEmpty, line.number, s"`${line.keyword}` is written `$shape`").map(_ => (left, right))
    }

    /** `CLAIM by METHOD` split at the last ` by `, or the claim alone. */
    private def trailingBy(text: String): (String, Option[String]) = {
      val found = text.lastIndexOf(" by ")
      if (found >= 0) (text.take(found).trim, Some(text.drop(found + 4).trim))
      else if (text.startsWith("by ")) ("", Some(text.drop(3).trim))
      else (text.trim, None)
    }
  }
}
