package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Datatype.{Argument, Constructor, Specification}

/**
 * The builder of inductive types, asked about types chosen to reach the parts of it a single
 * example would leave alone.
 *
 * `btree('a, 'b)` has two type parameters and a constructor whose fixed and recursive arguments
 * alternate, so it is where the order of arguments, the order of type parameters and the choice
 * of a result type that does not collide with either are tested. `item` has three fixed slots of
 * two types in one constructor and one in another, which is where the labels' tuples are tested:
 * a slot read from the wrong position would give an injectivity that equates the wrong
 * arguments, and the statement comparison below would read it.
 *
 * == What would make these assertions empty ==
 *
 * An inductive type with one element satisfies every injectivity and every induction principle
 * there is, and a recursion theorem nobody detaches is an existential that reads like a function.
 * So the distinctness of two constructors is **detached** at concrete arguments, not only read,
 * and a function is defined through [[Datatype.defineRecursive]] and its equation used.
 */
class DatatypeSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val ground = Datatype.Ground.of(chain)
  private val base = chain.widest
  private val num = TyApp(Natural.TypeName, Nil)

  private def build(specification: Specification): Either[LogicError, Datatype] =
    Datatype.define(ground, base.theory, base.notation, specification)

  private val trees = Specification(
    "btree",
    List(
      Constructor("LEAF", Nil),
      Constructor("BRANCH", List(Argument.Of(TyVar("a")), Argument.Recursive, Argument.Of(TyVar("b")), Argument.Recursive))
    )
  )

  private val items = Specification(
    "item",
    List(
      Constructor("PAIRED", List(Argument.Of(num), Argument.Of(Type.Bool), Argument.Of(num))),
      Constructor("SINGLE", List(Argument.Of(Type.Bool)))
    )
  )

  private lazy val tree = force(build(trees))
  private lazy val item = force(build(items))

  private lazy val foundation: Set[Term] = Set(
    force(chain.classical.axiom(Classical.Choice)).conclusion,
    force(chain.classical.axiom(Classical.Eta)).conclusion,
    force(chain.naturals.axiom(Natural.Infinity)).conclusion
  )

  private def statement(datatype: Datatype, text: String): Term = force(datatype.proposition(text))

  /* ------------------------------------------------------------------ the statements */

  "A polymorphic type" should "have the induction principle its constructors describe" in {
    force(tree.fact(Datatype.induction("btree"))).conclusion shouldBe statement(
      tree,
      "!P:btree('a,'b) -> bool. P LEAF /\\ " +
        "(!x:'a. !l:btree('a,'b). !y:'b. !r:btree('a,'b). P l ==> P r ==> P (BRANCH x l y r)) ==> " +
        "(!t:btree('a,'b). P t)"
    )
  }

  it should "take its arguments in the order they were declared, fixed and recursive alternating" in {
    force(tree.fact(Datatype.injective("BRANCH"))).conclusion shouldBe statement(
      tree,
      "!x:'a. !l:btree('a,'b). !y:'b. !r:btree('a,'b). !x':'a. !l':btree('a,'b). !y':'b. !r':btree('a,'b). " +
        "BRANCH x l y r = BRANCH x' l' y' r' ==> x = x' /\\ l = l' /\\ y = y' /\\ r = r'"
    )
  }

  it should "recurse into a result type that collides with neither parameter" in {
    // The parameters are `'a` and `'b`, so the result is `'b1`: a result named `'b` would make the
    // recursion theorem say that every function into the tree's second parameter exists, which is a
    // different and weaker theorem, and the comparison below is what would tell.
    force(tree.fact(Datatype.recursion("btree"))).conclusion shouldBe statement(
      tree,
      "!e:'b1. !f:'a -> btree('a,'b) -> 'b -> btree('a,'b) -> 'b1 -> 'b1 -> 'b1. " +
        "?h:btree('a,'b) -> 'b1. h LEAF = e /\\ " +
        "(!x:'a. !l:btree('a,'b). !y:'b. !r:btree('a,'b). h (BRANCH x l y r) = f x l y r (h l) (h r))"
    )
  }

  "A type with several fixed slots" should "read each argument from its own slot" in {
    force(item.fact(Datatype.injective("PAIRED"))).conclusion shouldBe statement(
      item,
      "!m:num. !p:bool. !n:num. !m':num. !p':bool. !n':num. " +
        "PAIRED m p n = PAIRED m' p' n' ==> m = m' /\\ p = p' /\\ n = n'"
    )
    force(item.fact(Datatype.distinct("PAIRED", "SINGLE"))).conclusion shouldBe statement(
      item,
      "!m:num. !p:bool. !n:num. !q:bool. ~(PAIRED m p n = SINGLE q)"
    )
    force(item.fact(Datatype.cases("item"))).conclusion shouldBe statement(
      item,
      "!t:item. (?m:num. ?p:bool. ?n:num. t = PAIRED m p n) \\/ (?q:bool. t = SINGLE q)"
    )
  }

  it should "publish one distinctness per pair of constructors and nothing unlisted" in {
    tree.facts.keySet shouldBe Set(
      "BTREE_INDUCT", "BTREE_CASES", "BTREE_RECURSION", "BRANCH_INJECTIVE", "LEAF_NOT_BRANCH"
    )
    item.facts.keySet shouldBe Set(
      "ITEM_INDUCT", "ITEM_CASES", "ITEM_RECURSION", "PAIRED_INJECTIVE", "SINGLE_INJECTIVE", "PAIRED_NOT_SINGLE"
    )
    tree.facts.values.foreach(_.hypotheses shouldBe empty)
  }

  /* ------------------------------------------------------------------ what it declares */

  "The builder" should "declare the type, its two bijections and the constructors, and nothing else" in {
    (tree.theory.constants.keySet -- base.theory.constants.keySet) shouldBe
      Set("mk_btree", "dest_btree", "LEAF", "BRANCH")
  }

  it should "cost nothing for induction and exactly choice, eta and infinity for the rest" in {
    // Induction and case analysis rest on `INDUCTIVE_INDUCT`, the type definition and
    // `Intuitionistic`, none of which asserts anything; the rest reach choice through `COND` and
    // the graph's witness, eta through the node's extensionality, and infinity through `num`.
    // Equalities, not ceilings: an injectivity that stopped reaching infinity would mean the labels
    // stopped carrying the constructor's index, and a ceiling would not notice.
    Derivation.axiomsOf(force(tree.fact("BTREE_INDUCT"))) shouldBe empty
    Derivation.axiomsOf(force(tree.fact("BTREE_CASES"))) shouldBe empty
    List("BTREE_RECURSION", "BRANCH_INJECTIVE", "LEAF_NOT_BRANCH").foreach { name =>
      withClue(s"$name: ")(Derivation.axiomsOf(force(tree.fact(name))) shouldBe foundation)
    }
  }

  /* ------------------------------------------------------------------ not empty */

  "Two constructors" should "be told apart at concrete arguments, which a one-point type cannot do" in {
    val separated = force(
      for {
        refusal <- tree.fact(Datatype.distinct("LEAF", "BRANCH"))
        at <- tree.term("(ZERO:num)")
        leaf <- tree.term("LEAF:btree(num,num)")
        typed = Kernel.instType(Map("a" -> num, "b" -> num), refusal)
        result <- tree.logic.rules.specAll(typed, List(at, leaf, at, leaf))
      } yield result
    )
    separated.hypotheses shouldBe empty
    separated.conclusion shouldBe statement(tree, "~(LEAF = BRANCH (ZERO:num) LEAF (ZERO:num) LEAF)")
  }

  "A function defined by recursion" should "come back with the equation its clause describes" in {
    // The number of branches of a tree: nothing at a leaf, one more than both subtrees at a branch.
    // The clauses are at `btree(num, num)`, so the builder has to instantiate the type's own
    // parameters as well as the result, which is what reading them off the clauses is for.
    val (extended, _, equations) = force(
      for {
        leaf <- tree.term("ZERO")
        branch <- tree.term(
          "\\x:num. \\l:btree(num,num). \\y:num. \\r:btree(num,num). \\m:num. \\n:num. SUC (m + n)"
        )
        defined <- Datatype.defineRecursive(tree, ground, tree.theory, "BRANCHES", Nil, List(leaf, branch))
      } yield defined
    )
    equations.map(_.hypotheses) shouldBe List(Nil, Nil)
    equations.map(_.conclusion) shouldBe List(
      force(Parser.proposition(extended, tree.notation, "BRANCHES (LEAF:btree(num,num)) = ZERO")),
      force(
        Parser.proposition(
          extended,
          tree.notation,
          "!x:num. !l:btree(num,num). !y:num. !r:btree(num,num). " +
            "BRANCHES (BRANCH x l y r) = SUC (BRANCHES l + BRANCHES r)"
        )
      )
    )
  }

  /* ------------------------------------------------------------------ refusals */

  "A type whose every constructor recurses" should "be refused, since the least such set is empty" in {
    val refused = build(Specification("loop", List(Constructor("MORE", List(Argument.Recursive)))))
    refused.isLeft shouldBe true
    refused.left.map(_.message).swap.getOrElse("") should include("no recursive argument")
  }

  "Two constructors of one name" should "be refused before anything is declared" in {
    build(Specification("dup", List(Constructor("C", Nil), Constructor("C", Nil)))).left.map(_.message).swap
      .getOrElse("") should include("distinct names")
  }

  "A type with no constructor" should "be refused" in {
    build(Specification("none", Nil)).left.map(_.message).swap.getOrElse("") should include("at least one constructor")
  }
}
