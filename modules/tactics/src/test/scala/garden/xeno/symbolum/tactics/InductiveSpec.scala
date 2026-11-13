package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.Derivation
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Datatypes, functions defined by recursion over them, and `simp`, from the language
 * (`docs/adr/0080`): the sixth increment of `docs/adr/0070`.
 *
 * Each feature is asserted by a proof that needs it and could not close without it, and beside a
 * refusal of the input that would make the assertion empty: a `simp` that closed every goal would
 * pass a test asking for one closed goal, so a goal it must leave open is asked too; a definition
 * that accepted any equations would pass a test of a well-formed one, so a call that is not
 * structural is asked too, and refused on its line.
 */
class InductiveSpec extends AnyFlatSpec with Matchers {

  private lazy val elaborate: Elaborate = Elaborate.standard

  private def entries(text: String): Vector[Elaborate.Entry] = {
    val report = elaborate.check(text)
    report.syntax shouldBe empty
    report.entries
  }

  private def entry(text: String, name: String): Elaborate.Entry =
    entries(text).find(_.name == name).getOrElse(fail(s"no declaration $name"))

  private def proved(text: String, name: String): Elaborate.Entry = {
    val found = entry(text, name)
    withClue(found.problems.map(p => s"line ${p.line}: ${p.reason}\n${p.detail.mkString("\n")}").mkString("\n")) {
      found.status shouldBe Elaborate.Status.Proved
    }
    found
  }

  private val trees =
    """datatype tree = LEAF
      |  | NODE tree num tree
      |
      |define SIZE : tree -> num
      |  SIZE LEAF = 0
      |  SIZE (NODE l x r) = SIZE l + 1 + SIZE r
      |end
      |
      |define MIRROR : tree -> tree
      |  MIRROR LEAF = LEAF
      |  MIRROR (NODE l x r) = NODE (MIRROR r) x (MIRROR l)
      |end
      |""".stripMargin

  private val lists =
    """datatype nlist = NIL | CONS num nlist
      |
      |define APPEND : nlist -> nlist -> nlist
      |  APPEND NIL ys = ys
      |  APPEND (CONS x xs) ys = CONS x (APPEND xs ys)
      |end
      |
      |define MAPN : (num -> num) -> nlist -> nlist
      |  MAPN f NIL = NIL
      |  MAPN f (CONS x xs) = CONS (f x) (MAPN f xs)
      |end
      |""".stripMargin

  /* ------------------------------------------------------------------ datatypes */

  "A datatype" should "be defined with its facts, the freeness of its constructors in the simp set" in {
    val declared = entry(trees, "tree")
    declared.kind shouldBe Elaborate.Kind.Datatype
    declared.status shouldBe Elaborate.Status.Defined
    declared.provides.map(_._1) shouldBe Vector("TREE_INDUCT", "TREE_CASES", "TREE_RECURSION", "NODE_INJECTIVE", "LEAF_NOT_NODE")
    declared.simp shouldBe Vector("NODE_INJECTIVE", "LEAF_NOT_NODE")
    // Nothing is asserted: the type costs what the chain's three axioms cost and no more.
    declared.provides.foreach { case (_, theorem) => theorem.hypotheses shouldBe empty }
    elaborate.check(trees).render should include("facts: TREE_INDUCT, TREE_CASES, TREE_RECURSION, NODE_INJECTIVE, LEAF_NOT_NODE")
  }

  it should "take parameters, and refuse to recurse at other ones" in {
    val option = entry("datatype opt('a) = NONE | SOME 'a\ntheorem SOME_NOT_NONE : !x:num. ~(SOME x = NONE) by simp", "SOME_NOT_NONE")
    option.status shouldBe Elaborate.Status.Proved
    val nested = entry("datatype weird('a) = STOP | MORE weird(num)", "weird")
    nested.status shouldBe Elaborate.Status.Refused
    nested.problems.head.reason should include("recurses only at its own")
  }

  it should "give `induction` its principle, with the branches named by the constructors" in {
    val text = trees +
      """
        |theorem MIRROR_MIRROR : !t. MIRROR (MIRROR t) = t
        |proof
        |  fix t
        |  induction t
        |  case LEAF:
        |    simp
        |  case NODE l x r ihl ihr:
        |    simp [ihl, ihr]
        |  end
        |qed
        |""".stripMargin
    val found = proved(text, "MIRROR_MIRROR")
    found.price.map(_.document).getOrElse(Vector.empty) should contain allOf ("MIRROR", "TREE_INDUCT")
    // A branch named by a label the principle does not have is refused, naming the ones it has.
    val wrong = entry(text.replace("case LEAF:", "case leaf:"), "MIRROR_MIRROR")
    wrong.problems.map(_.reason).mkString should include("the cases are LEAF (or 1), NODE (or 2)")
  }

  it should "refuse a name one of its facts would take" in {
    val clash = entry("theorem TREE_CASES : T by auto\n" + trees, "tree")
    clash.status shouldBe Elaborate.Status.Refused
    clash.problems.head.reason should include("TREE_CASES")
  }

  /* ------------------------------------------------------------------ recursion */

  "A function defined by recursion" should "have its equations as written, and nothing asserted" in {
    val size = entry(trees, "SIZE")
    size.status shouldBe Elaborate.Status.Defined
    // The printer names a bound variable by its type, so the names are its and not the equation's.
    size.statement shouldBe "SIZE LEAF = 0 /\\ (!x:tree. !n:num. !y:tree. SIZE (NODE x n y) = SIZE x + 1 + SIZE y)"
    size.simp shouldBe Vector("SIZE")
    val theorem = size.theorem.getOrElse(fail("no equations"))
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem).size shouldBe 3
  }

  it should "take parameters before the argument it matches and anything after it" in {
    val text = lists +
      """
        |theorem APPEND_NIL : !l. APPEND l NIL = l
        |proof
        |  fix l
        |  induction l
        |  case NIL:
        |    simp
        |  case CONS x xs ih:
        |    simp [ih]
        |  end
        |qed
        |
        |theorem MAPN_APPEND : !f l m. MAPN f (APPEND l m) = APPEND (MAPN f l) (MAPN f m)
        |proof
        |  fix f l m
        |  induction l
        |  case NIL:
        |    simp
        |  case CONS x xs ih:
        |    simp [ih]
        |  end
        |qed
        |""".stripMargin
    proved(text, "APPEND_NIL")
    proved(text, "MAPN_APPEND")
  }

  it should "refuse a call that is not on an argument of the constructor, on its line" in {
    val looping = entry("datatype nlist = NIL | CONS num nlist\ndefine FN : nlist -> num\n  FN NIL = 0\n  FN (CONS x xs) = FN (CONS x xs)\nend", "FN")
    looping.status shouldBe Elaborate.Status.Refused
    looping.problems.head.line shouldBe 4
    looping.problems.head.reason should include("one of the arguments CONS takes of the type itself: xs")
  }

  it should "refuse a constructor with no equation, a nested pattern and a parameter that moves" in {
    val missing = entry("datatype nlist = NIL | CONS num nlist\ndefine FN : nlist -> num\n  FN NIL = 0\nend", "FN")
    missing.problems.head.reason should include("has no equation for CONS")
    val nested = entry(
      "datatype nlist = NIL | CONS num nlist\ndefine FN : nlist -> num\n  FN NIL = 0\n  FN (CONS x NIL) = 1\n  FN (CONS x (CONS y ys)) = 2\nend", "FN")
    nested.status shouldBe Elaborate.Status.Refused
    nested.problems.head.reason should include("a constructor applied to variables")
    val moving = entry(
      "datatype nlist = NIL | CONS num nlist\ndefine G : num -> nlist -> num\n  G k NIL = k\n  G k (CONS x xs) = G (k + 1) xs\nend", "G")
    moving.status shouldBe Elaborate.Status.Refused
    moving.problems.head.reason should include("passes its parameters unchanged")
  }

  it should "refuse every equation that is not structural recursion, on the line that is not" in {
    // One row per refusal `Recursive.define` gives a document, each with the line it must name.
    // The datatype is on line 1 and the `define` on line 2, so the equations start on line 3.
    val header = "datatype nlist = NIL | CONS num nlist\n"
    val rows = Vector(
      ("define SUC : nlist -> num\n  SUC NIL = 0\n  SUC (CONS x xs) = 1\nend", "SUC", 2, "SUC is already a constant of the theory"),
      ("define FN : nlist -> num\n  0 = FN NIL\n  FN (CONS x xs) = 1\nend", "FN", 3, "the left side of an equation of FN is FN applied to its arguments"),
      ("define FB : nlist -> bool\n  FB NIL\n  FB (CONS x xs) = T\nend", "FB", 3, "an equation of FB is an equation"),
      ("define FN : nlist -> num\n  FN xs = 0\nend", "FN", 3, "no argument of FN here is a constructor of a datatype"),
      ("define G : nlist -> nlist -> num\n  G NIL NIL = 0\nend", "G", 3, "more than one argument of G here is a constructor"),
      ("define G : nlist -> nlist -> num\n  G NIL ys = 0\n  G xs (CONS y ys) = 1\nend", "G", 4,
        "this equation matches argument 2 of G, and the first one matches argument 1"),
      ("define G : nlist -> num -> num\n  G NIL = \\k. k\n  G (CONS x xs) k = k\nend", "G", 4,
        "this equation gives G 2 arguments and the first one 1"),
      ("define G : num -> nlist -> num -> num\n  G k NIL m = k\n  G j (CONS x xs) k = G j xs k\nend", "G", 4,
        "this equation names the parameters j and the first one k, and the names collide here"),
      ("define FN : nlist -> num\n  FN NIL = 0\n  FN NIL = 1\n  FN (CONS x xs) = 2\nend", "FN", 4, "NIL has an equation already"),
      ("define G : num -> nlist -> num\n  G 0 NIL = 0\n  G k (CONS x xs) = k\nend", "G", 3,
        "the argument 0 of G is not a variable"),
      ("define G : num -> nlist -> num\n  G k NIL = k\n  G x (CONS x xs) = x\nend", "G", 4,
        "a variable is named twice on the left side of this equation")
    )
    rows.foreach { case (definition, name, line, reason) =>
      val refused = entry(header + definition, name)
      withClue(s"$definition\n${refused.problems.map(p => s"line ${p.line}: ${p.reason}").mkString("\n")}\n") {
        refused.status shouldBe Elaborate.Status.Refused
        refused.problems.head.line shouldBe line
        refused.problems.head.reason should include(reason)
      }
    }
    // The control: parameters named otherwise in a later equation, with no collision, are renamed
    // to the first equation's rather than refused.
    entry(header + "define G : num -> nlist -> num\n  G k NIL = k\n  G j (CONS x xs) = G j xs\nend", "G").status shouldBe
      Elaborate.Status.Defined
  }

  it should "recurse under a binder, the value of the call being a function of what follows" in {
    val text = lists +
      """
        |define SUMACC : nlist -> num -> num
        |  SUMACC NIL = \k. k
        |  SUMACC (CONS x xs) = \k. SUMACC xs (k + x)
        |end
        |
        |theorem SUMACC_NIL : !k. SUMACC NIL k = k by simp
        |""".stripMargin
    entry(text, "SUMACC").status shouldBe Elaborate.Status.Defined
    proved(text, "SUMACC_NIL")
  }

  it should "refuse a name the document already holds" in {
    val both = entries("define SIZE := 0:num\n" + trees).filter(_.name == "SIZE")
    both.map(_.status) shouldBe Vector(Elaborate.Status.Defined, Elaborate.Status.Refused)
    both(1).problems.head.line shouldBe 5
    both(1).problems.head.reason should include("SIZE")
  }

  "A datatype" should "refuse an argument that is not a type, and a name that is already a type" in {
    val unknown = entry("datatype bag = EMPTY | ADD widget bag", "bag")
    unknown.status shouldBe Elaborate.Status.Refused
    unknown.problems.head.reason should include("widget is not a type here")
    val existing = entry("datatype real = RZ", "real")
    existing.status shouldBe Elaborate.Status.Refused
    existing.problems.head.reason should include("real is already a type of the theory")
  }

  /* ------------------------------------------------------------------ simp */

  "`simp`" should "close what its set normalises to truth, and leave what it does not, saying what is left" in {
    proved(trees + "theorem SIZE_LEAF : SIZE LEAF = 0 by simp", "SIZE_LEAF")
    // The same goal with nothing in the set that rewrites SIZE: the base and the clauses alone.
    val bare = entry("theorem ADDS : !n:num. n + 0 = n by simp", "ADDS")
    bare.status shouldBe Elaborate.Status.Proved
    val left = entry(trees + "theorem POSITIVE : !l x r. 0 < SIZE (NODE l x r) by simp", "POSITIVE")
    left.status shouldBe Elaborate.Status.Incomplete
    // The claim is closed, so what is left is still under its quantifiers, named by the printer.
    left.problems.head.reason should include("`simp` leaves !x:tree. !n:num. !y:tree. 0 < SIZE x + 1 + SIZE y")
    proved(trees + "theorem POSITIVE : !l x r. 0 < SIZE (NODE l x r)\nproof\n  fix l x r\n  by simp then arith\nqed", "POSITIVE")
  }

  it should "decide equalities and disequalities of constructors" in {
    proved(lists + "theorem DIFFERENT : !a l. ~(NIL = CONS a l) by simp", "DIFFERENT")
    proved(lists + "theorem OTHER_WAY : !a l. ~(CONS a l = NIL) by simp", "OTHER_WAY")
    proved(lists + "theorem SAME : !a b. CONS a NIL = CONS b NIL ==> a = b by simp", "SAME")
  }

  it should "take a theorem marked `[simp]` into the set from its declaration on, and refuse a conditional one" in {
    val text = trees +
      """
        |theorem SIZE_MIRROR [simp] : !t. SIZE (MIRROR t) = SIZE t
        |proof
        |  fix t
        |  induction t
        |  case LEAF:
        |    simp
        |  case NODE l x r ihl ihr:
        |    by simp [ihl, ihr] then arith
        |  end
        |qed
        |
        |theorem TWICE : !t. SIZE (MIRROR (MIRROR t)) = SIZE t by simp
        |""".stripMargin
    proved(text, "SIZE_MIRROR").simp shouldBe Vector("SIZE_MIRROR")
    proved(text, "TWICE")
    // Unmarked, the same theorem is not in the set and the second proof has nothing to close with.
    entry(text.replace("SIZE_MIRROR [simp]", "SIZE_MIRROR"), "TWICE").status shouldBe Elaborate.Status.Incomplete
    val conditional = entry("theorem COND_EQ [simp] : !a:num. !b:num. a = b ==> a + 0 = b by arith", "COND_EQ")
    conditional.status shouldBe Elaborate.Status.Refused
    conditional.problems.head.reason should include("cannot be in the simp set")
  }

  it should "take the facts named in brackets, as a method and as a step, and refuse one that is not a rule" in {
    val text = trees +
      """
        |theorem SIZE_MIRROR : !t. SIZE (MIRROR t) = SIZE t
        |proof
        |  fix t
        |  induction t
        |  case LEAF:
        |    simp
        |  case NODE l x r ihl ihr:
        |    by simp [ihl, ihr] then arith
        |  end
        |qed
        |
        |theorem BY_METHOD : !t. SIZE (MIRROR (MIRROR t)) = SIZE t by simp [SIZE_MIRROR]
        |
        |theorem BY_STEP : !t. SIZE (MIRROR (MIRROR t)) = SIZE t
        |proof
        |  simp [SIZE_MIRROR]
        |qed
        |
        |theorem STEP_THEN : !t. 0 < SIZE (NODE (MIRROR t) 1 LEAF)
        |proof
        |  fix t
        |  simp [SIZE_MIRROR]
        |  by arith
        |qed
        |
        |theorem COND_ADD : !a:num. !b:num. a = b ==> a + 0 = b by simp
        |
        |theorem NOT_A_RULE : !n:num. n + 0 = n
        |proof
        |  simp [COND_ADD]
        |qed
        |""".stripMargin
    proved(text, "BY_METHOD")
    proved(text, "BY_STEP")
    proved(text, "STEP_THEN")
    proved(text, "COND_ADD")
    val refused = entry(text, "NOT_A_RULE")
    refused.status should not be Elaborate.Status.Proved
    refused.problems.head.reason should include("COND_ADD cannot be a rule of `simp`")
    // The control: without the bracket the same goal has nothing that rewrites the MIRROR inside SIZE.
    entry(text + "\ntheorem BARE : !t. SIZE (MIRROR (MIRROR t)) = SIZE t by simp", "BARE").status shouldBe
      Elaborate.Status.Incomplete
  }

  it should "say so when the set changes nothing" in {
    val unchanged = entry("theorem STILL : !n:num. n < SUC n by simp", "STILL")
    unchanged.problems.head.reason should include("`simp` changes nothing in the goal")
  }

  "`rewrite`" should "rewrite with each equation of a conjunction of them, and refuse a fact that is not one" in {
    proved(trees + "theorem BY_REWRITE : SIZE (NODE LEAF 3 LEAF) = 1\nproof\n  rewrite SIZE\n  by arith\nqed", "BY_REWRITE")
    val hypothesis = entry(lists + "theorem NOT_AN_EQUATION : !a l. ~(NIL = CONS a l) by rewrite NIL_NOT_CONS", "NOT_AN_EQUATION")
    hypothesis.problems.head.reason should include("an equation, or a conjunction of equations")
  }

  /* ------------------------------------------------------------------ imports */

  "A document importing one with a datatype" should "read the type, its induction, its functions and its simp set" in {
    val sources = Map(
      "Trees" -> trees,
      "Uses" ->
        """import Trees
          |
          |theorem SIZE_MIRROR : !t. SIZE (MIRROR t) = SIZE t
          |proof
          |  fix t
          |  induction t
          |  case LEAF:
          |    simp
          |  case NODE l x r ihl ihr:
          |    by simp [ihl, ihr] then arith
          |  end
          |qed
          |""".stripMargin
    )
    val checked = new Workspace(elaborate, sources.get).check(Vector("Uses"))
    val uses = checked.find("Uses").getOrElse(fail("Uses was not checked")).report
    withClue(uses.render) { uses.ok shouldBe true }
    uses.entries.head.price.map(_.imported).getOrElse(Vector.empty) should contain allOf ("Trees.MIRROR", "Trees.SIZE", "Trees.TREE_INDUCT")
  }

  "The checker's JSON" should "name a datatype's kind" in {
    elaborate.check(trees).json should include(""""kind":"datatype"""")
  }
}
