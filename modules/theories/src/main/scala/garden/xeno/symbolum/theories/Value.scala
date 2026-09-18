package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A defined constant of `num` at concrete arguments, as an equation the kernel built.
 *
 * `NUM_DIV`, `NUM_MOD`, `NUM_GCD`, `NUM_FLOOR` and `NUM_CEIL` denote and are characterised by
 * lemmas, and nothing computed one: until 2026-09-18 `NUM_DIV 17 5 = 3` was not a theorem anything
 * here produced, and a caller wanting the value derived it by hand through
 * `NUM_DIV_MOD_UNIQUE`, one number at a time.
 *
 * == What a value is here, and why it is an equation rather than a number ==
 *
 * Every method below returns a theorem. A procedure that returned `3` would be a second
 * arithmetic, believed because it is written in Scala, and the whole arrangement this repository
 * describes is that the fast side proposes and the kernel checks. So the answer to "what is
 * `NUM_DIV 17 5`" is `|- NUM_DIV 17 5 = 3`, and the value is read off it.
 *
 * == The table, and why it is a table ==
 *
 * [[Value.Routes]] is one entry per constant: the characterisation it is read off, how many
 * arguments it takes, and what proves it. A constant is added by adding a row, which is the
 * property the card that asked for this made a condition: a procedure that named its constants in
 * its own control flow would be rewritten by every addition.
 *
 * `NUM_DIV` and `NUM_MOD` are one route because they are one lemma. `NUM_DIV_MOD_UNIQUE` says that
 * `m = n * q + r` with `r < n` determines **both**, so the two rows differ by which half of the
 * conclusion they keep.
 *
 * == What it costs, and why that was the whole design question ==
 *
 * Two axioms: choice and infinity, which is what the naturals cost and what every characterisation
 * lemma spent here already costs. The route that suggests itself — embed into the reals, compute
 * there, come back — was measured on the day this was written and produces the same equations at
 * **sixteen**, because `NUM_REAL_INJECTIVE` rests on the reals. `Digits` exists so that this one
 * does not have to. `ValueSpec` asserts the two rather than describing them.
 *
 * == What it refuses ==
 *
 * A constant with no row, by name, and an argument that is not a numeral of `num`, by value. It is
 * not a decision procedure for anything: handed `NUM_GCD` today it says it has no route, which is
 * a statement about this table and not about the constant.
 */
final class Value private (val digits: Digits, val modular: Modular, val linarith: Linarith) {

  /** The constants this can evaluate, which is what a caller should ask before asking for one. */
  def reachable: Vector[String] = Value.Routes.keys.toVector.sorted

  /**
   * `|- <constant> <arguments> = <value>`, or a refusal naming what stopped it.
   *
   * The arguments are values rather than terms, which is the same decision `Arithmetic.add` makes
   * one floor down: a caller holding a term holds a numeral it read from somewhere, and reading it
   * back is `Notation.valueOfNumeral`. What this takes is what it can compute with.
   */
  def of(constant: String, arguments: Vector[BigInt]): Either[LogicError, Kernel.Thm] =
    Value.Routes.get(constant) match {
      // `TypeError` and not `MissingDefinition`, which is what this said first and which reads
      // "no definition of NUM_GCD in this theory": there is one, and saying otherwise sends a
      // caller to look for a constant that is right where they left it. What is missing is a row
      // in this table, and the message says which rows there are.
      case None => Left(Value.noRow(constant))

      case Some(route) =>
        if (route.arity != arguments.size) Left(Value.wrongArity(constant, route, arguments.size))
        else route.prove(this, arguments)
    }

  /**
   * `|- t = v`, for a term `t` that is one of this table's constants applied to numerals.
   *
   * [[of]] takes a constant and a vector of values, which is what a caller who already knows both
   * holds. This is for the caller who holds a **term** and nothing else, which is every consumer on
   * the tactic surface: a goal arrives as `NUM_DIV 17 5 = 3` and what has to happen first is
   * reading `NUM_DIV`, `17` and `5` off it.
   *
   * **The reading belongs here and not at the call site**, and that is the whole reason this method
   * exists rather than a helper in `Prove`. Three of the five rows take the term's arguments as
   * their own and two do not: `NUM_FLOOR` takes one argument, a real, where its row takes a
   * numerator and a denominator. A caller reading [[Route.arity]] against the term's argument count
   * gets those two wrong, and gets them wrong silently, because two is a plausible number of
   * arguments for a term to have. [[Shape]] is what the table says about that, and the match below
   * does not compile if a row is added with a third shape.
   *
   * **What it refuses, by name.** A term whose head is not a constant, a constant with no row (with
   * the rows there are named, which is [[of]]'s refusal), a wrong number of arguments, and an
   * argument that is not a numeral — the last naming the argument, because "not a numeral" about a
   * term the caller wrote is the one refusal they can act on without reading this file.
   */
  def at(term: Term): Either[LogicError, Kernel.Thm] =
    Value.readingOf(modular.notation, term) match {
      case Right((name, arguments)) => of(name, arguments)
      case Left(why) => Left(why)
    }

  /**
   * `|- NUM_FLOOR (p / q) = c`, and the ceiling beside it, for a rational somebody wrote down.
   *
   * == Why this row takes two numbers for one argument ==
   *
   * The constant takes a **real** where every row above takes naturals, which is the widening the
   * card that asked for this predicted. It is made as small as it can be: the row is given a
   * numerator and a denominator and builds `p / q` itself, so what it answers about is the
   * rationals anybody can write. `NUM_FLOOR (exp 1)` stays **inexpressible** through this table
   * rather than being answered badly — a caller cannot even form the question — and that is the
   * honest shape of the limit.
   *
   * == Why it costs the reals, and why that is the constant's price and not this file's ==
   *
   * Every other row rests on the naturals' two axioms and this one cannot: the argument is a real,
   * the characterisation is about reals, and the bounds on a written rational are settled by
   * `Linarith`, a decision procedure over the ordered field. Measured on 2026-09-18, a ground goal
   * through `Linarith` costs fifteen axioms by itself, and `NUM_FLOOR_LE` reaches the sixteenth
   * through the Archimedean property. `ValueSpec` therefore asserts the price **per row**, which is
   * the assertion this row would otherwise have broken quietly.
   *
   * == The derivation, which is the uniqueness of the floor written out ==
   *
   * The two characterisations put `NUM_FLOOR x` in a window of width one, `f <= x < f + 1`, and the
   * candidate sits in the same window, which `Linarith` settles about two written numbers. That
   * does **not** give `f = c`: two reals in a window of width one can differ. What closes it is
   * that both are naturals. `NUM_LT_TOTAL` splits the three cases and `NUM_REAL_LT` turns `f < c`
   * into `real_of_num f + 1 <= real_of_num c`, a step of a whole unit, which leaves the window. So
   * the discreteness of `num` does the work and the reals only carry the inequalities.
   *
   * == One equation, handed to `Linarith` as a hypothesis rather than rewritten in ==
   *
   * `real_of_num c` is an atom to `Linarith` and `c` is a numeral it can read, and the two have to
   * meet. They meet as a **premise**: every goal below opens with `real_of_num c = c`, which the
   * three numeral bridges prove and which the procedure reads as two inequalities between an atom
   * and a number. The alternative is to rewrite the theorem, which is a congruence per statement
   * and a second door onto the rewriter for this file to be asked about.
   */
  private[theories] def rounded(
    numerator: BigInt,
    denominator: BigInt,
    wantCeiling: Boolean
  ): Either[LogicError, Kernel.Thm] =
    // Before anything, and as its own method rather than a line inside the derivation: the value
    // this row is about is `numerator / denominator` in Scala as well as in the theory, so a
    // denominator of zero throws where every other refusal here returns. The first version had the
    // check inside the comprehension, which is after the division that computes the answer.
    if (denominator <= 0 || numerator < 0)
      modular
        .term(s"($numerator:${Real.TypeName})")
        .flatMap(term =>
          Left(
            NotOfForm(
              s"a non-negative numerator over a positive denominator, and " +
                s"$numerator over $denominator is not one",
              term
            )
          )
        )
    else roundedWithin(numerator, denominator, wantCeiling)

  /** [[rounded]] once the arguments are known to name a non-negative rational. */
  private def roundedWithin(
    numerator: BigInt,
    denominator: BigInt,
    wantCeiling: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    val name = if (wantCeiling) Peano.Ceiling else Peano.Floor
    val point = s"(($numerator:${Real.TypeName}) / $denominator)"
    val applied = s"($name $point)"
    val image = s"real_of_num $applied"
    val answer =
      if (wantCeiling) (numerator + denominator - 1) / denominator
      else numerator / denominator
    val candidate = s"real_of_num ($answer:${Natural.TypeName})"
    val meeting = s"$candidate = $answer"

    val insideText = if (wantCeiling) s"$point <= $image" else s"$image <= $point"
    val outsideText = if (wantCeiling) s"$image < $point + 1" else s"$point < $image + 1"
    val lowerText = if (wantCeiling) s"$point <= $candidate" else s"$candidate <= $point"
    val upperText = if (wantCeiling) s"$candidate < $point + 1" else s"$point < $candidate + 1"

    def settle(text: String): Either[LogicError, Kernel.Thm] =
      modular.proposition(text).flatMap(linarith.prove)

    def once(bridge: Kernel.Thm, text: String): Either[LogicError, Kernel.Thm] =
      settle(s"$meeting ==> $text").flatMap(rules.mp(_, bridge))

    def characterisation(fact: String, nonNegative: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        held <- modular.peano.fact(fact)
        argument <- modular.term(point)
        result <- rules.spec(argument, held).flatMap(rules.mp(_, nonNegative))
      } yield result

    for {
      // `0 <= x` is what both characterisations ask for, and `Peano` writes it rather than hiding
      // it: `num` has no negative numbers, so a floor below zero would be right above zero and
      // silently wrong under it.
      nonNegative <- settle(s"(0:${Real.TypeName}) <= $point")
      inside <- characterisation(
        if (wantCeiling) Peano.CeilingAtLeast else Peano.FloorAtMost, nonNegative)
      outside <- characterisation(
        if (wantCeiling) Peano.CeilingBelow else Peano.FloorAbove, nonNegative)

      bridge <- embedding(answer)
      lower <- once(bridge, lowerText)
      upper <- once(bridge, upperText)

      subject <- modular.term(applied)
      answerTerm <- digits.numeral(answer)

      below <- refuses(
        subject, answerTerm, bridge, meeting,
        s"$image + 1 <= $candidate",
        if (wantCeiling) insideText else outsideText,
        if (wantCeiling) s"~($candidate < $point + 1)" else s"~($candidate <= $point)",
        if (wantCeiling) inside else outside,
        if (wantCeiling) upper else lower
      )
      above <- refuses(
        answerTerm, subject, bridge, meeting,
        s"$candidate + 1 <= $image",
        if (wantCeiling) outsideText else insideText,
        if (wantCeiling) s"~($point <= $candidate)" else s"~($point < $candidate + 1)",
        if (wantCeiling) outside else inside,
        if (wantCeiling) lower else upper
      )

      trichotomy <- modular.peano.fact(Peano.Trichotomy)
      cases <- rules.specAll(trichotomy, List(subject, answerTerm))
      result <- byCases(cases, below, above)
    } yield result
  }

  /**
   * `|- ~(NUM_LT a b)`, which is each of the two bad branches of the trichotomy.
   *
   * One shape used twice, and the only thing in it that knows the two numbers are naturals is
   * `NUM_REAL_LT`: what it turns `a < b` into is a step of a whole unit, and that is what leaves
   * the window the characterisations put both of them in.
   */
  private def refuses(
    smaller: Term,
    larger: Term,
    bridge: Kernel.Thm,
    meetingText: String,
    stepText: String,
    windowText: String,
    refusedText: String,
    window: Kernel.Thm,
    bound: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    for {
      order <- LogicError.lift(
        modular.theory.constant(
          Peano.StrictOrder,
          Type.fun(Value.Numbers, Type.fun(Value.Numbers, Type.Bool))
        )
      )
      claim <- LogicError.lift(Term.appAll(order, List(smaller, larger)))
      assumed <- LogicError.lift(Kernel.assume(claim))
      embeds <- modular.peano.fact(Peano.EmbedsStrictOrder)
      stepped <- rules.specAll(embeds, List(smaller, larger)).flatMap(rules.mp(_, assumed))
      // The meeting is passed as the text the caller wrote rather than printed off the bridge and
      // read back. What that buys is where a mismatch shows up: if the rewriting that built the
      // bridge had stopped short, `mp` below refuses because the premise is not the theorem, where
      // a goal rebuilt from the bridge's own sides would have accepted it and failed later.
      shape <- modular.proposition(
        s"$meetingText ==> $stepText ==> $windowText ==> $refusedText"
      )
      linear <- linarith.prove(shape)
      denied <- rules
        .mp(linear, bridge)
        .flatMap(rules.mp(_, stepped))
        .flatMap(rules.mp(_, window))
      falsity <- rules.notElim(denied, bound)
      result <- rules.notIntro(claim, falsity)
    } yield result
  }

  /** `|- real_of_num c = c`, the numeral of `num` and the real numeral with the same digits. */
  private def embedding(value: BigInt): Either[LogicError, Kernel.Thm] = {
    val peano = modular.peano

    for {
      one <- peano.fact(Peano.EmbedsNumeralOne)
      bit0 <- peano.fact(Peano.EmbedsNumeralBit0)
      bit1 <- peano.fact(Peano.EmbedsNumeralBit1)
      zero <- peano.fact(Peano.EmbedsZero)
      rules <- Rewrite.Rule.all(peano.logic, Vector(one, bit0, bit1, zero))
      term <- modular.term(s"real_of_num ($value:${Natural.TypeName})")
      result <- Rewrite.rewrite(rules, term)
    } yield result
  }

  /**
   * `|- a = b` out of the trichotomy and the two denials, which is the case analysis written out.
   *
   * The middle disjunct is the answer and the other two are refused, so what this is is
   * `NUM_LT_TOTAL` with two of its three branches closed by contradiction.
   */
  private def byCases(
    cases: Kernel.Thm,
    below: Kernel.Thm,
    above: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    for {
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (first, rest) = split
      pair <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equality, last) = pair

      assumedFirst <- LogicError.lift(Kernel.assume(first))
      firstBranch <- rules
        .notElim(below, assumedFirst)
        .flatMap(rules.falsityElim(equality, _))

      assumedEquality <- LogicError.lift(Kernel.assume(equality))
      assumedLast <- LogicError.lift(Kernel.assume(last))
      lastBranch <- rules
        .notElim(above, assumedLast)
        .flatMap(rules.falsityElim(equality, _))
      assumedRest <- LogicError.lift(Kernel.assume(rest))
      secondBranch <- rules.disjElim(assumedRest, assumedEquality, lastBranch)

      result <- rules.disjElim(cases, firstBranch, secondBranch)
    } yield result
  }

  /**
   * `|- NUM_GCD a b = <their greatest common divisor>`, for numerals that are not both zero.
   *
   * The card that asked for this left a decision here and it is taken: **the characterisation and
   * Bezout, not Euclid's algorithm**. Euclid is a definition by well-founded recursion, which this
   * system does not have, so that route waits on a piece of work that is not this one; the
   * characterisation asks for nothing new and costs more per value, which is a trade that only
   * matters to a caller computing many.
   *
   * Two divisibilities meet at `NUM_DIVIDES_ANTISYM`. That the answer divides the gcd is
   * `NUM_GCD_DIVIDES`, which is the greatest-common-divisor property: it divides both, so it
   * divides the gcd. The other direction is where Bezout is spent, and it is spent as a **witness**
   * rather than as a theorem: for `a` and `b` not both zero there are `x` and `y` with
   * `a * x = b * y + c`, [[Value.combination]] finds them by searching, and what the kernel then
   * checks is one equation between numerals. The gcd divides `a`, hence `a * x`, hence
   * `b * y + c`; it divides `b`, hence `b * y`; and `NUM_DIVIDES_SUMMAND` takes the second from the
   * first.
   *
   * `NUM_GCD ZERO ZERO` is refused rather than answered, and the refusal is the one `Modular`
   * already argues for: with both arguments zero there is no greatest common divisor to choose, so
   * every fact about the constant carries "not both zero" and nothing is provable about that term.
   *
   * A zero on **one** side is not that case and is not a special one either, except in the Bezout
   * half: `a * x = b * y + c` has no solution at `a = ZERO`, because `c` is then `b`. It does not
   * need one — the gcd divides the other argument, which **is** the answer, so the side that would
   * have been reached through the combination is reached directly.
   */
  private[theories] def greatestCommonDivisor(
    left: BigInt,
    right: BigInt
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules
    val answer = left.gcd(right)

    for {
      leftTerm <- digits.numeral(left)
      rightTerm <- digits.numeral(right)
      answerTerm <- digits.numeral(answer)
      _ <-
        if (left != 0 || right != 0) Right(())
        else
          // One literal and not two joined, which is a shape `NotationBoundarySpec` asks about: a
          // description assembled from pieces is one nobody can read off the source at the site.
          // What is missing from it, that there is no greatest common divisor of nothing and
          // nothing to have been chosen, is in this method's docstring.
          Left(
            NotOfForm(
              "a pair that is not two zeros, since nothing is provable about NUM_GCD ZERO ZERO",
              leftTerm
            )
          )

      gcdOf <- LogicError.lift(modular.theory.constant(Modular.GcdName, Value.Binary))
      gcdTerm <- LogicError.lift(Term.appAll(gcdOf, List(leftTerm, rightTerm)))
      notBothZero <- either(left != 0, leftTerm, rightTerm, left, right)

      dividesLeft <- divides(answer, left)
      dividesRight <- divides(answer, right)
      greatest <- modular.fact(Modular.GcdDivides)
      answerDividesGcd <- rules
        .specAll(greatest, List(leftTerm, rightTerm, answerTerm))
        .flatMap(rules.mp(_, notBothZero))
        .flatMap(step => rules.conjIntro(dividesLeft, dividesRight).flatMap(rules.mp(step, _)))

      gcdDividesLeft <- modular
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(leftTerm, rightTerm)))
        .flatMap(rules.mp(_, notBothZero))
      gcdDividesRight <- modular
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(leftTerm, rightTerm)))
        .flatMap(rules.mp(_, notBothZero))

      gcdDividesAnswer <-
        if (left == 0) Right(gcdDividesRight)
        else if (right == 0) Right(gcdDividesLeft)
        else throughCombination(left, right, answer, gcdTerm, gcdDividesLeft, gcdDividesRight)

      antisymmetric <- modular.fact(Modular.DividesAntisym)
      same <- rules
        .specAll(antisymmetric, List(answerTerm, gcdTerm))
        .flatMap(step => rules.conjIntro(answerDividesGcd, gcdDividesAnswer).flatMap(rules.mp(step, _)))
      result <- Conv.sym(same)
    } yield result
  }

  /**
   * `|- NUM_DIVIDES g c` from the gcd dividing both arguments, through one Bezout combination.
   *
   * The combination is found by searching and checked by the kernel, which is this repository's
   * arrangement at its smallest: what is believed is the equation `a * x = b * y + c` between four
   * numerals, and how `x` and `y` were come by is nobody's business.
   */
  private def throughCombination(
    left: BigInt,
    right: BigInt,
    answer: BigInt,
    gcdTerm: Term,
    gcdDividesLeft: Kernel.Thm,
    gcdDividesRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    for {
      pair <- Value.combination(left, right, answer)
      (multiplier, counter) = pair

      leftTerm <- digits.numeral(left)
      rightTerm <- digits.numeral(right)
      answerTerm <- digits.numeral(answer)
      multiplierTerm <- digits.numeral(multiplier)
      counterTerm <- digits.numeral(counter)

      dividesProduct <- modular.fact(Modular.DividesMul)
      timesMultiplier <- rules
        .specAll(dividesProduct, List(gcdTerm, leftTerm, multiplierTerm))
        .flatMap(rules.mp(_, gcdDividesLeft))
      timesCounter <- rules
        .specAll(dividesProduct, List(gcdTerm, rightTerm, counterTerm))
        .flatMap(rules.mp(_, gcdDividesRight))

      identity <- combined(left, multiplier, right, counter, answer)
      divisibility <- LogicError.lift(
        modular.theory.constant(Modular.DividesName, Type.fun(Value.Numbers, Type.fun(Value.Numbers, Type.Bool)))
      )
      partial <- LogicError.lift(Term.app(divisibility, gcdTerm))
      moved <- Conv.apTerm(partial, identity).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, timesMultiplier)))

      summand <- modular.fact(Modular.DividesSummand)
      product <- LogicError.lift(
        modular.theory.constant(Peano.Multiplication, Value.Binary)
      )
      rightProduct <- LogicError.lift(Term.appAll(product, List(rightTerm, counterTerm)))
      result <- rules
        .specAll(summand, List(gcdTerm, rightProduct, answerTerm))
        .flatMap(rules.mp(_, timesCounter))
        .flatMap(rules.mp(_, moved))
    } yield result
  }

  /** `|- a * x = b * y + c`, which is the combination with its three numeral computations in it. */
  private def combined(
    left: BigInt,
    multiplier: BigInt,
    right: BigInt,
    counter: BigInt,
    answer: BigInt
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftSide <- digits.multiply(left, multiplier)
      rightSide <- digits.multiply(right, counter)
      answerTerm <- digits.numeral(answer)
      sum <- digits.add(right * counter, answer)
      addition <- LogicError.lift(modular.theory.constant(Peano.Addition, Value.Binary))
      shifted <- Conv.apTerm(addition, rightSide).flatMap(Conv.apThm(_, answerTerm))
      settled <- Conv.trans(shifted, sum).flatMap(Conv.sym)
      result <- Conv.trans(leftSide, settled)
    } yield result

  /** `|- NUM_DIVIDES d m`, for numerals where the first divides the second. */
  private def divides(divisor: BigInt, multiple: BigInt): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    for {
      divisorTerm <- digits.numeral(divisor)
      multipleTerm <- digits.numeral(multiple)
      _ <-
        if (divisor != 0 && multiple % divisor == 0) Right(())
        else if (divisor == 0 && multiple == 0) Right(())
        else Left(NotOfForm(s"a multiple of $divisor, and $multiple is not one", multipleTerm))

      factor = if (divisor == 0) BigInt(0) else multiple / divisor
      factorTerm <- digits.numeral(factor)
      product <- digits.multiply(divisor, factor)
      equation <- Conv.sym(product)
      introduction <- modular.fact(Modular.DividesIntro)
      result <- rules
        .specAll(introduction, List(divisorTerm, multipleTerm, factorTerm))
        .flatMap(rules.mp(_, equation))
    } yield result
  }

  /** `|- ~(a = ZERO) \/ ~(b = ZERO)`, from whichever of the two is not zero. */
  private def either(
    onTheLeft: Boolean,
    leftTerm: Term,
    rightTerm: Term,
    left: BigInt,
    right: BigInt
  ): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    for {
      zero <- LogicError.lift(modular.theory.constant(Natural.NumberZero, Value.Numbers))
      leftEquation <- LogicError.lift(Term.eq(leftTerm, zero))
      rightEquation <- LogicError.lift(Term.eq(rightTerm, zero))
      leftDenial <- LogicError.lift(Term.app(logic.negation, leftEquation))
      rightDenial <- LogicError.lift(Term.app(logic.negation, rightEquation))
      held <- if (onTheLeft) notZero(left) else notZero(right)
      result <-
        if (onTheLeft) rules.disjIntro1(rightDenial, held)
        else rules.disjIntro2(leftDenial, held)
    } yield result
  }

  /**
   * `|- ~(v = ZERO)` for a positive numeral, which is `0 < v` read as a refusal.
   *
   * `Digits.below` is what says the number is positive, and nothing is below zero, so a number that
   * were zero would be below itself. The same two lines are in `Collatz`, about the empty word, and
   * they are here rather than shared because what they are about is a different constant.
   */
  private def notZero(value: BigInt): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    for {
      term <- digits.numeral(value)
      zero <- LogicError.lift(modular.theory.constant(Natural.NumberZero, Value.Numbers))
      order <- LogicError.lift(
        modular.theory.constant(Peano.StrictOrder, Type.fun(Value.Numbers, Type.fun(Value.Numbers, Type.Bool)))
      )
      positive <- digits.below(0, value)
      equation <- LogicError.lift(Term.eq(term, zero))
      assumed <- LogicError.lift(Kernel.assume(equation))
      partial <- LogicError.lift(Term.app(order, zero))
      absurd <- Conv
        .apTerm(partial, assumed)
        .flatMap(congruent => LogicError.lift(Kernel.eqMp(congruent, positive)))
      refused <- digits.peano.fact(Peano.NotBelowZero).flatMap(rules.spec(zero, _))
      falsity <- rules.notElim(refused, absurd)
      result <- rules.notIntro(equation, falsity)
    } yield result
  }

  /** `|- NUM_DIV m n = m/n`, and `|- NUM_MOD m n = m%n`, which are one derivation. */
  private[theories] def division(
    numerator: BigInt,
    divisor: BigInt,
    wantQuotient: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    // Division by zero is not a hole in the table: both constants are total and `Modular` publishes
    // what they are there, so the case is a specialisation rather than a refusal. It is also the
    // one case the uniqueness lemma cannot cover, since `r < n` is unmeetable at `n = ZERO`.
    if (divisor == 0)
      for {
        term <- digits.numeral(numerator)
        fact <- modular.fact(if (wantQuotient) Modular.DivAtZero else Modular.ModAtZero)
        result <- rules.spec(term, fact)
      } yield result
    else {
      val quotient = numerator / divisor
      val remainder = numerator % divisor

      for {
        numeratorTerm <- digits.numeral(numerator)
        divisorTerm <- digits.numeral(divisor)
        quotientTerm <- digits.numeral(quotient)
        remainderTerm <- digits.numeral(remainder)

        product <- digits.multiply(divisor, quotient)
        sum <- digits.add(divisor * quotient, remainder)
        addition <- LogicError.lift(
          modular.theory.constant(Peano.Addition, Value.Binary)
        )
        shifted <- Conv.apTerm(addition, product).flatMap(Conv.apThm(_, remainderTerm))
        identity <- Conv.trans(shifted, sum).flatMap(Conv.sym)

        smaller <- digits.below(remainder, divisor)
        determined <- modular.fact(Modular.DivisionDetermined)
        instance <- rules.specAll(
          determined,
          List(numeratorTerm, divisorTerm, quotientTerm, remainderTerm)
        )
        both <- rules.conjIntro(identity, smaller).flatMap(rules.mp(instance, _))
        half <- if (wantQuotient) rules.conjElim1(both) else rules.conjElim2(both)
        result <- Conv.sym(half)
      } yield result
    }
  }
}

object Value {

  /**
   * One constant, with what it is read off and what proves it.
   *
   * `note` is what a reader wants before trusting a row: which lemma the value rests on, and what
   * about the constant made that lemma the one to spend. It is carried here rather than written in
   * a comment beside the row so that a row cannot be added without one.
   */
  final case class Route(
    arity: Int,
    shape: Shape,
    characterisation: String,
    note: String,
    prove: (Value, Vector[BigInt]) => Either[LogicError, Kernel.Thm]
  )

  /**
   * How a row's arguments sit in a term, which is the one thing a caller holding a term needs and
   * cannot work out from [[Route.arity]].
   *
   * [[Value.of]] takes a vector of values because that is what it computes with, and for three of
   * the five rows that vector is the term's arguments read as numerals. For the other two it is
   * not: `NUM_FLOOR` takes **one** argument, a real, and its row takes **two** numbers, a numerator
   * and a denominator, so a caller matching `arity` against the term's argument count reads that
   * row as taking two arguments and finds a term that has one.
   *
   * It lives here rather than at the call site because the table is the place that knows: adding a
   * row whose arguments are shaped a third way is then a case added here and a compile error at
   * [[Value.at]], rather than a silent misreading in whoever holds the term.
   */
  enum Shape {

    /** Every argument of the term is a numeral of `num`, and they are the row's arguments. */
    case Naturals

    /**
     * One argument of the term, a quotient of two numerals of `real`, read as the pair.
     *
     * `NUM_FLOOR (7 / 2)` is the shape, and a real that is not written as one quotient of two
     * numerals is refused rather than approximated: `NUM_FLOOR (exp 1)` cannot be asked of this
     * table at all, which is the limit the row's own note states.
     */
    case WrittenRational
  }

  /**
   * What this evaluates, which is two of the five the card that asked for it names.
   *
   * The other three are rows nobody has written rather than constants this refuses on principle,
   * and the difference is what [[Value.of]]'s refusal says. `NUM_FLOOR` and `NUM_CEIL` carry
   * `0 <= x` as a written hypothesis and their arguments are reals, so their row needs an
   * obligation this table has no shape for yet; `NUM_GCD` is characterised rather than computed,
   * and its row spends Bezout rather than a uniqueness.
   */
  val Routes: Map[String, Route] = Map(
    Modular.DivName -> Route(
      2,
      Shape.Naturals,
      Modular.DivisionDetermined,
      "the quotient is determined by `m = n * q + r` with `r < n`, and at a zero divisor by " +
        "`NUM_DIV_ZERO`, which is where the uniqueness cannot reach because `r < ZERO` is unmeetable",
      (value, arguments) => value.division(arguments(0), arguments(1), wantQuotient = true)
    ),
    Modular.ModName -> Route(
      2,
      Shape.Naturals,
      Modular.DivisionDetermined,
      "the remainder of the same division, which is the other half of the same conclusion",
      (value, arguments) => value.division(arguments(0), arguments(1), wantQuotient = false)
    ),
    Modular.GcdName -> Route(
      2,
      Shape.Naturals,
      Modular.GcdDivides,
      "the answer divides the gcd because it divides both, and the gcd divides the answer through " +
        "one Bezout combination found by searching and checked as an equation between numerals; " +
        "the two meet at `NUM_DIVIDES_ANTISYM`, and two zeros are refused because nothing is " +
        "provable about `NUM_GCD ZERO ZERO`",
      (value, arguments) => value.greatestCommonDivisor(arguments(0), arguments(1))
    ),
    Peano.Floor -> Route(
      2,
      Shape.WrittenRational,
      Peano.FloorAtMost,
      "the greatest natural not above a written rational, read off the window `NUM_FLOOR_LE` and " +
        "`NUM_FLOOR_LT` put it in; the two arguments are a numerator and a denominator, because " +
        "the constant takes a real and this table's other rows take naturals",
      (value, arguments) => value.rounded(arguments(0), arguments(1), wantCeiling = false)
    ),
    Peano.Ceiling -> Route(
      2,
      Shape.WrittenRational,
      Peano.CeilingAtLeast,
      "the least natural not below the same rational, by the same window the other way up",
      (value, arguments) => value.rounded(arguments(0), arguments(1), wantCeiling = true)
    )
  )

  /**
   * Whether a term is one this table evaluates, which is the question an address asks.
   *
   * A boolean rather than the reading, because a caller deciding where to send a goal has not
   * decided to spend anything on it yet, and because the two questions have different answers on
   * the same term: `NUM_DIV m n` is an application of a constant with a row and is **not**
   * evaluable, its arguments being variables.
   */
  def reads(notation: Notation, term: Term): Boolean = readingOf(notation, term).isRight

  /**
   * The constant and the argument values a term names, or why it names none.
   *
   * One implementation with two callers, which is the reason it is here rather than on the class:
   * [[Value.at]] spends it to prove, [[reads]] spends it to decide an address, and a second reading
   * written for the second caller is how a procedure and the address that feeds it come to disagree
   * about which goals the procedure takes.
   */
  def readingOf(
    notation: Notation,
    term: Term
  ): Either[LogicError, (String, Vector[BigInt])] = {
    def spine(current: Term, collected: Vector[Term]): (Term, Vector[Term]) = current match {
      case App(fn, argument) => spine(fn, argument +: collected)
      case head => (head, collected)
    }

    val (head, arguments) = spine(term, Vector.empty)

    head match {
      case Const(constant, _) =>
        Routes.get(constant) match {
          // The same sentence [[Value.of]] refuses a missing row with, in the same words, because
          // it is the same fact: there is no row for this constant, and a caller who arrived with a
          // term rather than a name learns nothing extra from a second wording of it. Written once
          // and reached from both is what `NotationBoundarySpec`'s census is for.
          case None => Left(noRow(constant))
          case Some(route) => readArguments(notation, route, constant, arguments).map((constant, _))
        }
      case other =>
        Left(NotOfForm("an application of a constant this table evaluates", other))
    }
  }

  /** The constants this table has a row for, which is what a refusal about a missing one names. */
  private def reachable: Vector[String] = Routes.keys.toVector.sorted

  /** `constant has no row in this table`, in one place because two callers refuse with it. */
  private[theories] def noRow(constant: String): LogicError =
    TypeError(s"$constant has no row in this table; what it evaluates is ${reachable.mkString(", ")}")

  /** `constant takes n and was given m`, likewise. */
  private[theories] def wrongArity(constant: String, route: Route, supplied: Int): LogicError =
    TypeError(s"$constant takes ${route.arity} argument(s) and was given $supplied")

  /** The values of a term's arguments, as the row's [[Shape]] reads them. */
  private def readArguments(
    notation: Notation,
    route: Route,
    constant: String,
    arguments: Vector[Term]
  ): Either[LogicError, Vector[BigInt]] =
    route.shape match {
      case Shape.Naturals =>
        if (arguments.size != route.arity) Left(wrongArity(constant, route, arguments.size))
        else
          arguments.foldLeft(Right(Vector.empty): Either[LogicError, Vector[BigInt]]) {
            (accumulated, argument) =>
              for {
                done <- accumulated
                read <- notation.valueOfNumeral(argument).toRight(NotOfForm("a numeral", argument))
              } yield done :+ read
          }

      // One argument in the term and two in the row, which is what [[Shape]] is about, so the
      // arity refusal above would name the wrong number here and this branch says its own.
      case Shape.WrittenRational =>
        arguments.toList match {
          case single :: Nil => rational(notation, single)
          case _ => Left(wrongArity(constant, route.copy(arity = 1), arguments.size))
        }
    }

  /**
   * The numerator and the denominator of a term written as one quotient of two numerals.
   *
   * A bare numeral is taken as itself over one, because `NUM_FLOOR 3` is a question somebody will
   * ask and refusing it for carrying no denominator would be an answer about the notation rather
   * than about the floor.
   */
  private def rational(notation: Notation, term: Term): Either[LogicError, Vector[BigInt]] =
    notation.valueOfNumeral(term) match {
      case Some(whole) => Right(Vector(whole, BigInt(1)))
      case None =>
        term match {
          case App(App(Const(Real.Division, _), numerator), denominator) =>
            for {
              above <- notation
                .valueOfNumeral(numerator)
                .toRight(NotOfForm("a numeral", numerator))
              below <- notation
                .valueOfNumeral(denominator)
                .toRight(NotOfForm("a numeral", denominator))
            } yield Vector(above, below)
          case other =>
            Left(NotOfForm("a numeral, or one numeral over another", other))
        }
    }

  /**
   * `x` and `y` with `a * x = b * y + c`, found by searching rather than by an algorithm.
   *
   * Bezout says the pair exists for `c` the greatest common divisor, and the classical route to it
   * is the extended Euclidean algorithm, which produces a coefficient that may be negative and then
   * needs its sign argued about over a type with no negative numbers. Searching `x` upwards avoids
   * that entirely: the solutions are a residue class modulo `b / c`, so one is found within that
   * many steps, and what leaves this function is a pair of numbers the derivation proves an
   * equation about. Nothing downstream trusts the search.
   */
  private[theories] def combination(
    left: BigInt,
    right: BigInt,
    answer: BigInt
  ): Either[LogicError, (BigInt, BigInt)] = {
    val bound = if (answer == 0) BigInt(1) else right / answer + 1

    val found = (BigInt(0) to bound).view
      .map(multiplier => (multiplier, left * multiplier - answer))
      .collectFirst {
        case (multiplier, remainder) if remainder >= 0 && right != 0 && remainder % right == 0 =>
          (multiplier, remainder / right)
      }

    found.toRight(
      TypeError(
        s"no combination a * x = b * y + c for a = $left, b = $right and c = $answer within $bound steps"
      )
    )
  }

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  private val Binary: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /** Over a chain, which is where both halves it needs are built. */
  def construct(chain: Chain): Either[LogicError, Value] =
    for {
      semiring <- Semiring.construct(chain.peano)
      digits <- Digits.construct(semiring)
      linarith <- Linarith.construct(chain.order)
    } yield new Value(digits, chain.modular, linarith)

  /** The same, for a caller that has already built the three procedures it stands on. */
  def over(digits: Digits, modular: Modular, linarith: Linarith): Value =
    new Value(digits, modular, linarith)
}
