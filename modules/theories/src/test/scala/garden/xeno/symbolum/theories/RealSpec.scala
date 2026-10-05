package garden.xeno.symbolum.theories

import java.nio.file.Files
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The theory of the reals, and the check that it proves what it says it proves.
 *
 * The pinned list below is the test that matters. Until phase 5 the sixteen were asserted, and an
 * axiom altered by accident would not have failed a single other test: it would have made more
 * things provable, which looks like progress. They are proved from the cuts now, so a mis-stated one
 * fails to build; what the pin still catches is a statement that was **changed** into something
 * the cuts happen to prove as well, since the construction would prove that one too and nothing
 * else would notice that `ADD_SYM` had stopped saying commutativity.
 *
 * The first version of this file compared the theory against `Real.Laws` parsed again, which is
 * the list compared with itself: an edit to an axiom passed. An audit pointed it out. The copy here
 * is written out by hand, in the form the theory prints, so that an edit fails until the same
 * commit edits this file too, which is the moment of attention the check exists to force.
 */
class RealSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val reals = Real.standard

  /** The sixteen statements as the theory prints them. Change this only with a textbook open. */
  private val Pinned: Vector[(String, String)] = Vector(
    "ADD_SYM" -> "!x:real. !y:real. x + y = y + x",
    "ADD_ASSOC" -> "!x:real. !y:real. !z:real. x + y + z = x + (y + z)",
    "ADD_ZERO" -> "!x:real. x + 0 = x",
    "ADD_INVERSE" -> "!x:real. x + -x = 0",
    "MUL_SYM" -> "!x:real. !y:real. x * y = y * x",
    "MUL_ASSOC" -> "!x:real. !y:real. !z:real. x * y * z = x * (y * z)",
    "MUL_ONE" -> "!x:real. x * 1 = x",
    "MUL_INVERSE" -> "!x:real. ~(x = 0) ==> x * inv x = 1",
    "DISTRIBUTE" -> "!x:real. !y:real. !z:real. x * (y + z) = x * y + x * z",
    "ONE_NOT_ZERO" -> "~(1 = 0)",
    "LT_IRREFLEXIVE" -> "!x:real. ~(x < x)",
    "LT_TRANSITIVE" -> "!x:real. !y:real. !z:real. x < y /\\ y < z ==> x < z",
    "LT_TOTAL" -> "!x:real. !y:real. x < y \\/ x = y \\/ y < x",
    "LT_ADD" -> "!x:real. !y:real. !z:real. x < y ==> x + z < y + z",
    "LT_MUL" -> "!x:real. !y:real. 0 < x /\\ 0 < y ==> 0 < x * y",
    // The bound names are the printer's, since a bound variable has no name of its own: `x` is
    // the predicate, `y` its witness and bound, `z` and `u` the elements compared.
    "COMPLETENESS" ->
      ("!f:real -> bool. (?x:real. f x) /\\ (?x:real. !y:real. f y ==> y <= x) ==> " +
        "(?x:real. (!y:real. f y ==> y <= x) /\\ (!y:real. (!z:real. f z ==> z <= y) ==> x <= y))")
  )

  "The theory of the reals" should "build" in {
    Real.construction(Classical.standard, Natural.standard) should matchPattern { case Right(_) => }
  }

  it should "prove exactly the statements pinned in this file, in that order, with nothing assumed" in {
    Real.Laws.map { case (name, _) => name } shouldBe Pinned.map { case (name, _) => name }
    Pinned.foreach { case (name, text) =>
      val proved = force(reals.law(name))
      withClue(s"$name: ") {
        reals.show(proved.conclusion) shouldBe text
        proved.hypotheses shouldBe empty
      }
    }
  }

  it should "assert nothing of its own: its theory's axioms are the logic's two and the naturals' one" in {
    // The sixteen are theorems, so what the theory asserts is what it was built on. The comparison
    // is with the two developments that assert something rather than with a count, which would pass
    // over a swap.
    val foundation = Classical.standard.theory.axioms.toSet ++ Natural.standard.theory.axioms
    foundation should have size 3
    reals.theory.axioms.toSet shouldBe foundation
  }

  it should "spend the foundation on the sixteen and nothing else" in {
    val foundation = reals.theory.axioms.toSet
    Real.Laws.foreach { case (name, _) =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(reals.law(name))).diff(foundation) shouldBe empty
      }
    }
    // The positive control for the line above: an instrument that found no axiom anywhere would
    // pass it. Completeness is the union of a family of cuts, and two cuts with the same members
    // are one cut only by extensionality.
    Derivation.axiomsOf(force(reals.law("COMPLETENESS"))) should not be empty
  }

  it should "add nothing to the trusted base by defining an abbreviation" in {
    // Subtraction, division and the non-strict order are definitional extensions: the pinned list
    // above is the whole trusted content, and these three are not in it.
    reals.theory.definitions.keySet should contain allOf (
      Real.Subtraction, Real.Division, Real.NonStrictOrder
    )
  }

  it should "define each of its operations as the operation on cuts it names" in {
    // They were declared and left undefined until phase 5, which is what the sixteen then said
    // something about. Each is an alias now, so none of the seven is undefined.
    val primitives = Set(Real.Zero, Real.One, Real.Addition, Real.Multiplication, Real.Negation, Real.Inverse, Real.Order)
    reals.theory.definitions.keySet should contain allElementsOf primitives
    reals.theory.undefinedConstants.toSet.intersect(primitives) shouldBe empty
    Show.show(force(reals.definition(Real.Addition)).conclusion) shouldBe "real_add = CUT_ADD"
  }

  "Every one of the sixteen" should "be closed and mention only constants the theory declares" in {
    // A statement with a free variable would be a schema, and one mentioning an undeclared constant
    // would be about nothing. The kernel refuses both; this says so from the outside, on the
    // sixteen that matter.
    Real.Laws.map { case (name, _) => force(reals.law(name)).conclusion }.foreach { axiom =>
      withClue(s"${reals.show(axiom)}\n") {
        Term.freeVariables(axiom) shouldBe empty
        constantsIn(axiom).diff(reals.theory.constants.keySet) shouldBe empty
      }
    }
  }

  it should "print back as something that reads as the same statement" in {
    Real.Laws.foreach { case (name, _) =>
      val statement = force(reals.law(name)).conclusion
      val printed = reals.show(statement)

      withClue(s"$name printed as $printed\n") {
        reals.proposition(printed) shouldBe Right(statement)
      }
    }
  }

  /**
   * The sources that assert an axiom **this repository itself believes**.
   *
   * These three are the trusted base as `CLAUDE.md` enumerates it, and each asserts a fixed,
   * enumerated proposition written in the file beside the call: choice and eta, infinity. The list
   * grows by one file per axiom, in the commit that adds it; it shrank once, when phase 5 proved the
   * sixteen of the reals and `Real.scala` left it.
   */
  private val Foundation: Vector[String] = Vector(
    "modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/Kernel.scala",
    "modules/logic/src/main/scala/garden/xeno/symbolum/logic/Classical.scala",
    "modules/theories/src/main/scala/garden/xeno/symbolum/theories/Natural.scala"
  )

  /**
   * The sources that assert an axiom **a caller asked for**, which is a different kind of thing.
   *
   * **Two**, since 2026-09-16, and the distinction is worth the second list rather than two more rows
   * in the first. A file in [[Foundation]] names the proposition it asserts, and a reader can go and
   * read it; neither of these names one. `Session.scala` asserts what somebody typed into a cell,
   * and `Domain.scala` asserts the axiom texts carried by a `Domain` a caller built and handed it. So it does not enlarge what this system asks anyone to believe: it offers a surface on
   * which a user can assume something of their own, which `DomainTheorySpec` is the argument for,
   * and every theorem downstream of such an assumption carries it through `Derivation.foreignTo`,
   * which `SessionSpec` asserts in both directions.
   *
   * Merging the two lists would lose exactly the distinction this repository keeps everywhere else:
   * one says the trusted base grew, the other says a user can put a hypothesis on the table and be
   * told what stands on it. A reader's next move differs, and so does the remedy if the list is
   * wrong. This is the same repair the assertion below already made for a different pair, callers
   * against mentioners, and for the same reason.
   *
   * **What would move a file from here to [[Foundation]]:** asserting a proposition of its own,
   * rather than one handed to it. If `Session.scala` ever gains a default axiom, a starter theory
   * or anything asserted without a caller naming it, it belongs in the first list and this comment
   * is what says so.
   */
  // **Sorted, and the order is load-bearing rather than tidiness.** The assertion below that filters
  // the scan against this list compares the two as sequences, and the scan comes back sorted, so a
  // list written in any other order fails on the order alone once it holds more than one entry. It
  // held one until 2026-09-16 and the constraint was invisible; `modules/tactics` sorts before
  // `modules/theories`.
  private val OnRequest: Vector[String] = Vector(
    "modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Session.scala",
    // 2026-09-16, and it arrived as a RED rather than as a line added beside the call, which is
    // this assertion doing its job and the author not running the module's suite. `Domain.build`
    // asserts the axioms of a domain theory a caller described: the propositions are the caller's
    // texts, parsed against the caller's base, so the trusted base does not move and
    // `DomainCompositionSpec` asserts that by reading the composed theory's axiom count against
    // the foundation's.
    "modules/theories/src/main/scala/garden/xeno/symbolum/theories/Domain.scala"
  )

  "The operation that asserts an axiom" should "be called by the files that believe and those that offer" in {
    // `Kernel.assertAxiom` is the non-conservative operation. Any main source that CALLS it is
    // trusted base, so the claim that the base is the kernel plus three files is checked here
    // rather than stated in a document. The kernel's own file is where it is defined.
    //
    // **The scan strips comments, and that is the whole repair of 2026-09-12.** It used to read
    // `Files.readString(path)`, the file entire, so a source that merely *explained* the rule was
    // counted as trusted base. That is not a hypothetical: `Register.scala` was written that day
    // with a docstring that had to name the operation in order to say why the register needs it,
    // the suite went red, and the author worked around it by not writing the name -- leaving
    // fourteen words of periphrasis where an identifier belonged. The guard did not catch a defect;
    // it made an explanation worse. In a repository where the prose is half the value, a scan that
    // does not strip comments measures the documentation and believes it is measuring the code.
    //
    // `Sources.code` already existed and already strips them, one function along in the object this
    // test was already using. So the tool was not missing; it was not reached for.
    val using = Sources
      .main()
      .map(Sources.relative)
      .filter(relative => Sources.code(relative).contains("assertAxiom"))
      .sorted

    // Four files from 2026-09-10 until phase 5 took `Real.scala` off the list by proving its sixteen,
    // and three since. The two that arrived on that first day are what `docs/adr/0007` starts: the
    // choice operator, which is the first thing this system asks anyone to believe about the
    // formalism rather than about a domain, and infinity, which is asked of a type nothing else
    // interprets. The list grows by one file per axiom, in the commit that adds it, so the trusted
    // base cannot grow without this line changing beside it. It grew twice on the day it was
    // written, and both times this assertion is what said so.
    //
    // The naturals themselves add nothing here: `num` is defined and `Kernel.defineType` asserts
    // nothing, which is the whole reason that rule is in the kernel.
    // Split by what the file asserts rather than read as one list, which is the change of
    // 2026-09-13 and is explained on [[OnRequest]]. Both halves are asserted, so a file that
    // appeared in neither still turns this red naming itself, and a file that moved between them
    // turns it red too.
    withClue("a source asserts an axiom of its own and is in neither list: ") {
      using shouldBe (Foundation ++ OnRequest).sorted
    }

    withClue("the trusted base grew: ") {
      using.filterNot(OnRequest.contains) shouldBe Foundation
    }

    withClue("a source that asserts on request went missing: ") {
      using.filter(OnRequest.contains) shouldBe OnRequest
    }
  }

  it should "be discussed only in sources that say so by name" in {
    // The second half, and the reason tightening the scan above is not by itself the repair.
    // Stripping comments and stopping there would make a file that discusses the rule **invisible**
    // where it used to be forbidden, and neither is what a reader wants. The question they are
    // actually asking is *which files can make the trusted base grow*, and a file that talks about
    // the rule is neither one of those nor irrelevant to it.
    //
    // So: two assertions instead of one. Above, the files that call it. Here, the files that only
    // name it, listed explicitly, growing in the commit that adds one exactly as the four above do.
    // That is the discipline `DocumentationSpec` already applies to the kernel directory, where
    // every file is in one of two lists and neither list is "whatever is left".
    val naming = Sources
      .main()
      .map(Sources.relative)
      .filter(relative => Sources.code(relative).contains("assertAxiom"))
      .toSet

    val mentioning = Sources
      .main()
      .map(Sources.relative)
      .filter(relative => Files.readString(Sources.repositoryRoot().resolve(relative)).contains("assertAxiom"))
      .filterNot(naming.contains)
      .sorted

    // Each of these is here for the same reason, which is that it has to name the operation in
    // order to make its own argument. How many there are is the list below rather than a number
    // written beside it.
    //
    // `Register.scala` produces `docs/reading-register.md`, and its docstring explains why that
    // document is worth anything: a scan over this operation says that an axiom outside the chain's
    // signature would have to come from one of the files the assertion above names. It is also
    // the file the old guard drove into fourteen words of periphrasis where an identifier belonged,
    // which is the defect this second assertion exists to keep repaired.
    //
    // `Notebook.scala` argues that a cell running arbitrary Scala could reach `Kernel.assertAxiom`
    // and `Term.variable` unrecorded, which is the reason its command language is small and is not
    // Scala. That argument is unwritable without the name either.
    mentioning shouldBe Vector(
      "modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Notebook.scala",
      "modules/theories/src/main/scala/garden/xeno/symbolum/theories/Register.scala"
    )
  }

  "The notation" should "bind multiplication tighter than addition" in {
    // A term rather than a proposition: `x + y * z` is a real, and asking for a proposition here
    // is how this test failed the first time.
    val direct = force(reals.term("x:real + y:real * z:real"))
    val explicit = force(reals.term("x:real + (y:real * z:real)"))

    direct shouldBe explicit
    reals.show(direct) shouldBe "x + y * z"
  }

  it should "bind arithmetic tighter than equality" in {
    val direct = force(reals.proposition("x:real + y:real = y + x"))
    val explicit = force(reals.proposition("(x:real + y:real) = (y + x)"))

    direct shouldBe explicit
  }

  it should "read a minus as negation in front of a term and as subtraction between two" in {
    val negated = force(reals.proposition("-x:real = 0"))
    val subtracted = force(reals.proposition("x:real - y:real = 0"))

    reals.show(negated) shouldBe "-x = 0"
    reals.show(subtracted) shouldBe "x - y = 0"
  }

  it should "print an axiom the way it was written" in {
    reals.show(force(reals.law("ADD_SYM")).conclusion) shouldBe
      "!x:real. !y:real. x + y = y + x"
  }

  "An axiom" should "be usable through the derived rules" in {
    val rules = reals.logic.rules
    val a = Term.variable("a", TyApp(Real.TypeName, Nil))
    val b = Term.variable("b", TyApp(Real.TypeName, Nil))

    val theorem = force(
      for {
        commutativity <- reals.law("ADD_SYM")
        atA <- rules.spec(a, commutativity)
        atB <- rules.spec(b, atA)
      } yield atB
    )

    reals.show(theorem.conclusion) shouldBe "a + b = b + a"
    theorem.hypotheses shouldBe empty
  }

  /* ----------------------------------------------------------------- helpers */

  private def constantsIn(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

}
