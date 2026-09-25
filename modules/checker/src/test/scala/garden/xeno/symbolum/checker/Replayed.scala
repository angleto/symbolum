package garden.xeno.symbolum.checker

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.*

/**
 * The proofs a second implementation reads, in one place, because they are read from three.
 *
 * `ReplaySpec` checks them in this process, `SerialisedSpec` checks them as text, and
 * `garden.xeno.symbolum.tactics.Evaluation` prints their counts into `docs/evaluation.md`. Until 2026-09-12
 * the first two each held their own list and the document held a third, hand-copied and a row
 * short; the table in the document said six where the suite replayed ten, and every figure in it
 * had to be re-typed when `Conv.refl` changed what a proof costs.
 *
 * A population stated once is also the only way the count in the document can mean anything: "nine
 * theorems replayed" is a claim about a list, and a list nobody can point at is not a measurement.
 *
 * == What is in it ==
 *
 * Every theorem the suite puts to the checker, in the order the document shows them, which is
 * cheapest first with the ones about the naturals last. Those are the finding the record
 * surfaced and the reason the order is not arbitrary: the successor's properties rest on both of
 * the naturals' axioms and induction rests on neither, and a reader meets them next to each other.
 *
 * The forged theorems are **not** here. They are not proofs, they are refusals, and each of them
 * belongs to the test that states what it is refused for.
 */
object Replayed {

  /**
   * One proof, with the theory it is a proof in.
   *
   * The theory is not decoration: the naturals' facts rest on choice and on infinity, and checking
   * them against the theory of the reals is refused, correctly. `ReplaySpec` found that out by
   * passing one theory for everything.
   */
  final case class Entry(label: String, theorem: Kernel.Thm, theory: Theory)

  /**
   * A proof that cannot fail to build, and what happens if one does.
   *
   * A refusal reaching here is not a refusal anybody can act on: it means `Order.standard` or
   * `Ring.standard` stopped proving what this file names, and every test below it is then about
   * nothing. So it is an invariant violation rather than an `Either` a caller threads, which is the
   * same answer `Classical.standard`, `Chain.standard` and `Novelty.standard` give in the main
   * sources and for the same reason. Refusals a caller can act on stay `Either` everywhere here:
   * `Evaluation` returns one when the checker declines a proof rather than typesetting it.
   */
  private def force[T](result: Either[?, T]): T =
    result.fold(
      error => throw new IllegalStateException(s"a replayed proof does not build: $error"),
      identity
    )

  private lazy val reals: Theory = Order.standard.reals.theory

  private lazy val naturals: Natural = Natural.standard

  /** The propositional theorem that costs no axiom, built the way `Minimal` is asked for one. */
  private def conjunctionElimination: Kernel.Thm = {
    val logic = garden.xeno.symbolum.logic.Logic.standard
    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)

    val goal = force(
      for {
        conjunction <- logic.mkConj(p, q)
        implication <- logic.mkImp(conjunction, p)
        outer <- logic.mkForall(q, implication)
        closed <- logic.mkForall(p, outer)
      } yield closed
    )

    force(garden.xeno.symbolum.logic.Minimal.standard.prove(goal))
  }

  /**
   * The classical propositional theorem a **solver** found and the rules re-derived.
   *
   * The entry this file exists for, read from the other end. Everything else here was proved by a
   * procedure that builds its theorem as it goes; this one was found by a conflict-driven search in
   * `modules/sat` that cannot construct a theorem at all, and then re-derived one resolution step at
   * a time. A second implementation replaying it is the whole argument for that arrangement being
   * safe: if the replay were wrong, this is where it would show, in a reader that never heard of
   * the solver.
   *
   * Peirce's law rather than something simpler, because it is the goal that separates this
   * procedure from `Minimal`: no negation in it, classically valid, and intuitionistically out of
   * reach. The entry above it is the one `Minimal` proves on no axiom at all, so the two sit next
   * to each other and a reader meets the price of the difference.
   */
  private def peirce: Kernel.Thm = {
    val classical = garden.xeno.symbolum.logic.Classical.standard
    val goal = force(
      garden.xeno.symbolum.logic.Parser
        .proposition(classical.theory, classical.notation, "!p:bool. !q:bool. ((p ==> q) ==> p) ==> p")
    )

    force(garden.xeno.symbolum.logic.Propositional(classical).prove(goal))
  }

  /**
   * A claim about a domain that is not mathematics, settled by that domain's own machinery.
   *
   * The entry that says the arrangement holds at the far end of the surface. Everything else here
   * is about numbers or about pure logic; this one is a rule somebody could have written in a
   * handbook, turned into a theory, and settled by `Domain.Built.settle`, which specialises the
   * domain's axioms at the subject the claim names and puts the propositional skeleton to
   * `Intuitionistic`. A second implementation that never heard of any of that reads the proof and
   * agrees, which is what makes "a domain claim is a theorem like any other" a measurement.
   *
   * Its axiom column is the point: the conclusion reaches the domain's own axiom and no
   * foundational one. The only other entries that reach no foundational axiom are the ones that
   * reach no axiom at all, because they assume nothing.
   */
  private def onCall: Entry = {
    val classical = garden.xeno.symbolum.logic.Classical.standard
    val alert = TyApp("alert", Nil)

    val rule = Domain(
      name = "the on-call rule",
      typeOperators = Vector("alert" -> 0),
      constants = Vector(
        "Paged" -> Type.fun(alert, Type.Bool),
        "Acknowledged" -> Type.fun(alert, Type.Bool),
        "Escalated" -> Type.fun(alert, Type.Bool)
      ),
      axioms = Vector(
        "EscalatedOnlyUnacknowledged" ->
          "!a:alert. Escalated a ==> Paged a /\\ ~(Acknowledged a)"
      )
    )

    val built = force(Domain.build(classical.theory, classical.notation, rule))

    built.settle(classical, "!a:alert. Acknowledged a ==> ~(Escalated a)") match {
      case Domain.Verdict.Settled(theorem, _) =>
        Entry("an on-call rule's own claim", theorem, built.theory)
      case other =>
        throw new IllegalStateException(s"a replayed proof does not build: $other")
    }
  }

  /** The whole population, built once. */
  lazy val entries: Vector[Entry] = Vector(
    Entry("`0 < 1`", force(Order.standard.zeroLessOne), reals),
    Entry("`0 < 12`", force(Order.standard.positive(12)), reals),
    Entry("`12 * 12 = 144`", force(Arithmetic.standard.multiply(12, 12)), reals),
    Entry(
      "`(x + 1)^2` expanded",
      force(Ring.standard.prove("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1")),
      reals
    ),
    Entry(
      "`x < y /\\ y < z ==> x < z`",
      force(Linarith.standard.prove("!x:real y:real z:real. x < y /\\ y < z ==> x < z")),
      reals
    ),
    Entry("`(x * y) / y = x`", force(Field.standard.prove("!x:real y:real. (x * y) / y = x")), reals),
    Entry("`p /\\ q ==> p`, propositional", conjunctionElimination, reals),
    Entry(
      "`((p ==> q) ==> p) ==> p`, found by a solver",
      peirce,
      garden.xeno.symbolum.logic.Classical.standard.theory
    ),
    onCall,
    Entry("`ADD_SYM`, an axiom of the reals", force(Real.standard.axiom("ADD_SYM")), reals),
    Entry(
      "the successor's properties",
      force(naturals.fact(Natural.SuccessorProperties)),
      naturals.theory
    ),
    Entry("induction over the naturals", force(naturals.fact(Natural.Induction)), naturals.theory)
  )

  /** One of them by label, for a test that has something to say about a single proof. */
  def entry(label: String): Entry =
    entries
      .find(_.label == label)
      .getOrElse(throw new IllegalStateException(s"no replayed proof is labelled $label"))

  /** The proof the serialised figures in `docs/evaluation.md` are measured on. */
  val Serialised: String = "`12 * 12 = 144`"

  /** How many nodes a term is, which is the cost of writing it out once. */
  private def sizeOf(term: Term): Int = term match {
    case App(function, argument) => 1 + sizeOf(function) + sizeOf(argument)
    case Abs(_, body) => 1 + sizeOf(body)
    case _ => 1
  }

  /**
   * How many term nodes the steps of a proof would write if each wrote its own.
   *
   * The number the format is compared against, and it lives here rather than in `SerialisedSpec`
   * because `docs/evaluation.md` quotes it and the generator that writes the document has to
   * measure the same thing the test does.
   *
   * Walked by identity rather than by equality, for the reason [[Check.ByIdentity]] gives, and walked
   * with an explicit worklist rather than by recursing into the premises: a proof is as deep as the
   * derivation that built it, the numeral procedures chain hundreds of steps, and a recursion over
   * the premises meets the stack before it meets a long one. `Derivation.walk` says the same of
   * itself.
   */
  def nodesOf(theorem: Kernel.Thm): Int = {
    @scala.annotation.tailrec
    def walk(pending: List[Kernel.Thm], seen: Set[Check.ByIdentity], written: Int): Int =
      pending match {
        case Nil => written
        case node :: rest =>
          val key = Check.ByIdentity(node)
          if (seen.contains(key)) walk(rest, seen, written)
          else
            walk(
              Derivation.premises(node.derivation) ++ rest,
              seen + key,
              written + sizeOf(node.conclusion) + node.hypotheses.map(sizeOf).sum
            )
      }

    walk(List(theorem), Set.empty, 0)
  }
}
