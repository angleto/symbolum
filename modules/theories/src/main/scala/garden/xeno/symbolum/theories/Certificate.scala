package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*

/**
 * What the search returns: whole multipliers for the hypotheses, a constant, and a scale.
 *
 * This and [[Region]] are the search of [[Linarith]], which held them until 2026-09-11. Three
 * questions about one set of facts: [[Certificate.find]] asks whether a target follows,
 * [[Region.satisfying]] asks whether the facts can hold at once, [[Region.largest]] asks how large
 * a form gets where they do. The last two share an encoding that the first does not use, which is
 * why they are two objects and not one.
 *
 * All of it is ordinary arithmetic over [[Rational]] with no theorem anywhere in it. A wrong answer
 * makes the checking side fail; it cannot make the checking side agree.
 *
 * It says that the hypotheses weighed by the multipliers, plus the constant, come to `scale`
 * times the target. The multipliers are whole because the rational solution was cleared of its
 * denominators, and the scale is what it was cleared by. A multiplier is non-negative except on
 * an equality, where either sign is sound.
 */
final case class Certificate(multipliers: Vector[BigInt], slack: BigInt, scale: BigInt)

object Certificate {

  /**
   * The multipliers that make the target out of the hypotheses, if there are any.
   *
   * That is Farkas' lemma read in the useful direction, and it replaced an enumeration of the
   * subsets: every hypothesis used once or not at all decides only the goals that happen to be a
   * plain sum, which left `2 * x < 2 * y ==> x < y` outside for wanting the multiplier one half.
   *
   * `strict` says whether the target has to be reached strictly. When it does, the combination has
   * to weigh at least one strict fact or the constant above zero, since nothing else can make a
   * strict statement, and a feasible point chosen without asking may weigh none of them: that is
   * what the second phase of the search is for. The zero form as a target with `strict` set is how
   * a contradiction among the hypotheses is looked for, because a combination of positive things
   * that comes to nothing is one.
   */
  def find(facts: Vector[LinearFact], target: LinearForm, strict: Boolean): Option[Certificate] = {
    val atoms = (target.atoms ++ facts.flatMap(_.form.atoms).toSet).toVector.sorted(Term.ordering)

    // An equality gets two columns, one for each sign, and what it is weighed by is the
    // difference: a simplex works over non-negative unknowns and this is the ordinary way to give
    // one a free sign.
    val plan = facts.zipWithIndex.flatMap {
      case (fact, index) if fact.kind == LinearFact.Kind.Equal =>
        Vector((index, BigInt(1)), (index, BigInt(-1)))
      case (_, index) => Vector((index, BigInt(1)))
    }

    val slack = atoms.map(_ => Rational.zero) :+ Rational.one
    val columns =
      plan.map { case (index, sign) => column(facts(index).form.scaled(Rational.of(sign)), atoms) }
        :+ slack

    val solution =
      if (!strict) Farkas.nonNegativeSolution(columns, column(target, atoms))
      else {
        val weights = plan.map { case (index, _) =>
          if (facts(index).kind == LinearFact.Kind.Strict) Rational.one else Rational.zero
        } :+ Rational.one
        Farkas.nonNegativeSolution(columns, column(target, atoms), weights)
      }

    solution.map { values =>
      val (whole, scale) = Farkas.cleared(values)
      val multipliers = Array.fill(facts.length)(BigInt(0))
      plan.zip(whole.init).foreach { case ((index, sign), value) =>
        multipliers(index) = multipliers(index) + sign * value
      }
      Certificate(multipliers.toVector, whole.last, scale)
    }
  }

  /** A form as a column of the system: one row per atom, and the constant last. */
  private def column(form: LinearForm, atoms: Vector[Term]): Vector[Rational] =
    atoms.map(form.at) :+ form.constant
}

/**
 * Where a set of linear facts holds, as a linear program in standard form.
 *
 * Two questions about the same region, and the one thing they disagree about is the margin: see
 * [[Region.systemOf]]. Held apart from [[Certificate]] because they share an encoding that
 * [[Certificate.find]] does not use.
 */
object Region {

  /**
   * A point where every one of these facts holds, if there is one.
   *
   * The other question the same machinery answers, and the one a set of premises has to survive
   * before what it implies is worth reading: `h1..hn |- c` is vacuously true when the premises
   * contradict each other, and over a domain of declared constants that is easy to write and
   * invisible. Sampling cannot settle it, because a premise like `x = 1` holds on a set a sampler
   * lands on with probability zero; solving can, exactly, and what comes back is the point.
   *
   * The system is the ordinary one. Each unknown becomes a difference of two non-negative unknowns,
   * because a simplex works over non-negative ones and the atoms here are not; each inequality gets
   * a slack; and every strict fact is asked to clear a margin that the search then pushes above
   * zero. Bounding that margin at one is what keeps the program from running off to infinity, and
   * costs nothing: a point where every strict fact is positive can be scaled until the smallest of
   * them is one.
   *
   * `None` means there is no such point, and it is a decision rather than a failure to find one.
   */
  def satisfying(facts: Vector[LinearFact]): Option[Map[Term, Rational]] = {
    val system = systemOf(facts)
    val weights =
      Vector.fill(system.columns.length)(Rational.zero).updated(system.margin, Rational.one)

    Farkas
      .nonNegativeSolution(system.columns, system.target, weights)
      .map(values =>
        system.atoms.zipWithIndex.map { case (atom, index) =>
          atom -> (values(index) - values(system.atoms.length + index))
        }.toMap
      )
  }

  /**
   * How large a linear form can be where every one of these facts holds.
   *
   * The other question the same system answers, and the one that turns proposing a premise into
   * solving for one. `Abduce` used to offer bounds at the numerals the goal happened to write, so a
   * goal needing `x >= 2/3` was offered `x > 2` and a goal needing `y >= 2` was offered `y > 2`:
   * both close it, both are stronger than necessary, and the first is stronger by an unbounded
   * amount. Told the largest value the form takes on the region, a caller knows the exact threshold
   * and can offer it.
   *
   * **The supremum over the closure**, which is what the encoding gives and is what a caller wants.
   * A strict fact is encoded with a margin the search is free to set to zero, so the region here is
   * the one with `<` weakened to `<=`. That makes the answer the least upper bound rather than a
   * value attained, and whether a bound **at** it closes the goal is a separate question with a
   * separate answer: `f > sup` always closes, and `f >= sup` closes exactly when the supremum is not
   * attained. `Abduce` offers both and lets its own check decide, which is cheaper and more honest
   * than deciding it here.
   *
   * `Farkas.Extreme.Infeasible` means no point satisfies the facts **with their strict inequalities
   * weakened**, which is a narrower thing than the facts being unsatisfiable: `{0 < x, x < 0}` comes
   * back `At(0)` rather than `Infeasible`, because zero is in the closure of both. That is not a
   * defect to repair here. The one caller only asks this about a region it has already established
   * is non-empty, since a goal that already follows is refused before any of this; and a caller who
   * wanted the open question has [[satisfying]], which answers exactly that.
   *
   * `Unbounded` means the form grows without limit on the region, so no bound of that shape can
   * close anything.
   */
  def largest(facts: Vector[LinearFact], form: LinearForm): Farkas.Extreme = {
    val system = systemOf(facts)
    val width = system.atoms.length
    val rest = system.columns.length - 2 * width

    val objective =
      system.atoms.map(form.at) ++ system.atoms.map(atom => -form.at(atom)) ++
        Vector.fill(rest)(Rational.zero)

    Farkas.maximum(system.columns, system.target, objective) match {
      // The objective the simplex maximised is the form without its constant term, because the
      // constant is not a function of the unknowns. Adding it back here is what makes the answer a
      // value of the form rather than of its variable part.
      case Farkas.Extreme.At(value) => Farkas.Extreme.At(value + form.constant)
      case other => other
    }
  }

  /**
   * The facts as a linear program in standard form.
   *
   * One place rather than two, since 2026-09-11, when [[largest]] began asking the same system a
   * different question. Each unknown becomes a difference of two non-negative ones, because a
   * simplex works over non-negative ones and the atoms here are not; each inequality gets a slack;
   * every strict fact is asked to clear a margin, and the margin is bounded at one so that the
   * program cannot run off to infinity along it. Bounding it costs nothing: a point where every
   * strict fact is positive can be scaled until the smallest of them is one.
   *
   * What the two callers do with the margin is the whole difference between them. [[satisfying]]
   * pushes it above zero, which asks for a point of the **open** region. [[largest]] leaves it
   * alone, which maximises over the closure.
   */
  private def systemOf(facts: Vector[LinearFact]): System = {
    val atoms = facts.flatMap(_.form.atoms).toSet.toVector.sorted(Term.ordering)
    val width = atoms.length
    val slacked = facts.zipWithIndex.collect {
      case (fact, index) if fact.kind != LinearFact.Kind.Equal => index
    }
    val rows = facts.length + 1

    def column(entries: (Int, Rational)*): Vector[Rational] =
      entries.foldLeft(Vector.fill(rows)(Rational.zero)) { case (acc, (row, value)) =>
        acc.updated(row, value)
      }

    val positive = atoms.map { atom =>
      column(facts.zipWithIndex.map { case (fact, row) => row -> fact.form.at(atom) }*)
    }
    val negative = positive.map(values => values.map(-_))

    val slacks = slacked.map(fact => column(fact -> -Rational.one))
    val margins = column(
      (facts.zipWithIndex.collect {
        case (fact, row) if fact.kind == LinearFact.Kind.Strict => row -> -Rational.one
      } :+ (facts.length -> Rational.one))*
    )
    val bound = column(facts.length -> Rational.one)

    System(
      columns = positive ++ negative ++ slacks :+ margins :+ bound,
      target = facts.map(fact => -fact.form.constant) :+ Rational.one,
      atoms = atoms,
      margin = 2 * width + slacked.length
    )
  }

  /** The system, with the one column index its two callers disagree about. */
  private final case class System(
    columns: Vector[Vector[Rational]],
    target: Vector[Rational],
    atoms: Vector[Term],
    margin: Int
  )
}
