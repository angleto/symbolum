package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Finite distributions, the value of an experiment to a Bayesian decision maker, and the easy
 * direction of Blackwell's theorem: an experiment obtained from another by a random garbling is
 * worth no more in any decision problem.
 *
 * `docs/adr/0063` is the decision. A distribution on `n` outcomes is a function `num -> real` read
 * on `[0, n)`, a channel from `n` states to `m` signals is one distribution of signals per state,
 * and the probabilities are reals, so a rational instance is written in numerals:
 *
 * {{{
 *   DISTRIBUTION n p  =  (!i. i < n ==> 0 <= p i) /\ Sum p n = 1
 *   CHANNEL n m k     =  !y. y < n ==> DISTRIBUTION m (k y)
 *   Maximum f n       =  max (f 0) ... (f n), by recursion
 *   Argmax f n        =  the first i <= n with f i = Maximum f n, by recursion
 *   VALUE n m top prior k u
 *                     =  Sum (\s. Maximum (\a. Sum (\y. prior y * k y s * u a y) n) top) m
 * }}}
 *
 * `VALUE` is the expected utility of the Bayes-optimal action among `top + 1`, written before
 * conditioning on the signal, so a signal of probability zero asks for no case.
 * [[Decision.ValueByPosterior]] is the agreement with the textbook's posterior form wherever every
 * signal has positive probability.
 *
 * == Blackwell ==
 *
 * {{{
 *   BLACKWELL_GARBLING
 *     !n m r top prior k g u. CHANNEL m r g ==>
 *       VALUE n r top prior (\y t. Sum (\s. k y s * g s t) m) u <= VALUE n m top prior k u
 * }}}
 *
 * with the one hypothesis the proof reads. Writing `X a s` for the inner sum of `VALUE` at `k`,
 * the garbled experiment's inner sum is `Sum (\s. g s t * X a s) m` ([[Decision.GarbledTerm]]), so
 * its value is `sum_t max_a sum_s g s t X a s`, which is at most `sum_t sum_s g s t max_a X a s`
 * because `g` is non-negative, and that is `sum_s max_a X a s` because each row of `g` sums to one.
 * Nothing in it reads the prior or `k`, so neither is asked to be a distribution.
 *
 * == What it spends ==
 *
 * Choice, eta and infinity, as every fact about the constructed reals does. It declares five
 * constants and asserts nothing.
 */
final class Decision private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm],
  /** The steps the derivations here are written in, over this link's theory: what an instance reuses. */
  private[theories] val kit: ComplexKit,
  held: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** A fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] = facts.get(name).toRight(MissingDefinition(name))

  /** The steps of [[Decision.Proofs]] over this link's facts, for an instance written in them. */
  private[theories] def steps: Decision.Proofs = new Decision.Proofs(kit, held)

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))
}

object Decision {

  type R[A] = Either[LogicError, A]

  /** `Maximum f n` is the greatest of `f 0, ..., f n`: the interval is closed, so it is never empty. */
  val MaximumName: String = "Maximum"

  /** `DISTRIBUTION n p`: `p` is non-negative on `[0, n)` and sums to one there. */
  val DistributionName: String = "DISTRIBUTION"

  /** `CHANNEL n m k`: every row `k y` with `y < n` is a distribution on `[0, m)`. */
  val ChannelName: String = "CHANNEL"

  /** `VALUE n m top prior k u`: the expected utility of the Bayes-optimal action. */
  val ValueName: String = "VALUE"

  /** `|- !f. Maximum f 0 = f 0` */
  val MaximumAtZero: String = "MAXIMUM_ZERO"

  /** `|- !f n. Maximum f (SUC n) = max (Maximum f n) (f (SUC n))` */
  val MaximumAtSuccessor: String = "MAXIMUM_SUC"

  /** `|- !f n i. i <= n ==> f i <= Maximum f n`: it bounds every term. */
  val MaximumUpper: String = "MAXIMUM_UPPER"

  /** `|- !f n c. (!i. i <= n ==> f i <= c) ==> Maximum f n <= c`: and is the least bound. */
  val MaximumLeast: String = "MAXIMUM_LEAST"

  /** `|- !f n. ?i. i <= n /\ Maximum f n = f i`: it is one of the terms. */
  val MaximumAttained: String = "MAXIMUM_ATTAINED"

  /** `|- !f g n. (!i. i <= n ==> f i <= g i) ==> Maximum f n <= Maximum g n` */
  val MaximumMonotone: String = "MAXIMUM_MONOTONE"

  /** `|- !f g n. (!i. i <= n ==> f i = g i) ==> Maximum f n = Maximum g n`: it reads only `[0, n]`. */
  val MaximumCongruenceBelow: String = "MAXIMUM_CONGRUENCE_BELOW"

  /** `|- !f c n. 0 <= c ==> Maximum (\a. c * f a) n = c * Maximum f n` */
  val MaximumScale: String = "MAXIMUM_SCALE"

  /** `Argmax f n` is the first index of `[0, n]` where `f` takes its [[MaximumName]]: the optimal rule. */
  val ArgmaxName: String = "Argmax"

  /** `|- !f. Argmax f 0 = 0` */
  val ArgmaxAtZero: String = "ARGMAX_ZERO"

  /** `|- !f n. Argmax f (SUC n) = COND (Maximum f n < f (SUC n)) (SUC n) (Argmax f n)` */
  val ArgmaxAtSuccessor: String = "ARGMAX_SUC"

  /** `|- !f n. Argmax f n <= n /\ f (Argmax f n) = Maximum f n`: the rule attains the maximum. */
  val ArgmaxAttains: String = "ARGMAX_ATTAINS"

  /** `|- !f w j. Sum f (w * j) = Sum (\s. Sum (\g. f (w * s + g)) w) j`: a sum read in blocks of `w`. */
  val SumGroups: String = "SUM_GROUPS"

  /** `|- !f n g. g < n ==> Sum (\y. f y * COND (y = g) 1 0) n = f g`: an indicator picks one term. */
  val SumIndicator: String = "SUM_INDICATOR"

  /** `|- !x z n g. g < n ==> Sum (\s. COND (s = g) x z) n = x + (real_of_num n - 1) * z` */
  val SumCondCount: String = "SUM_COND_COUNT"

  /** `|- !f n j. j <= n ==> (!i. i <= n ==> ~(i = j) ==> f i < f j) ==> Argmax f n = j`: a strict maximum is the rule. */
  val ArgmaxUnique: String = "ARGMAX_UNIQUE"

  /** The inner sum of the garbled experiment, rewritten as a mixture of the original's. */
  val GarbledTerm: String = "VALUE_GARBLED_TERM"

  /** Blackwell's easy direction. */
  val Blackwell: String = "BLACKWELL_GARBLING"

  /** The value agrees with the posterior form where every signal has positive probability. */
  val ValueByPosterior: String = "VALUE_POSTERIOR"

  /** The bodies of the three constants defined outright, as text. */
  val Bodies: Vector[(String, String)] = Vector(
    DistributionName ->
      "\\n:num. \\p:num->real. (!i:num. i < n ==> (0:real) <= p i) /\\ Sum p n = 1",
    ChannelName ->
      "\\n:num. \\m:num. \\k:num->num->real. !y:num. y < n ==> DISTRIBUTION m (k y)",
    ValueName ->
      ("\\n:num. \\m:num. \\top:num. \\prior:num->real. \\k:num->num->real. \\u:num->num->real. " +
        "Sum (\\s:num. Maximum (\\a:num. Sum (\\y:num. prior y * k y s * u a y) n) top) m")
  )

  /** What this development publishes, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    MaximumAtZero -> "!f:num->real. Maximum f 0 = f 0",
    ArgmaxAtZero -> "!f:num->real. Argmax f 0 = 0",
    ArgmaxAtSuccessor ->
      "!f:num->real. !n:num. Argmax f (SUC n) = COND (Maximum f n < f (SUC n)) (SUC n) (Argmax f n)",
    MaximumAtSuccessor -> "!f:num->real. !n:num. Maximum f (SUC n) = max (Maximum f n) (f (SUC n))",
    MaximumUpper -> "!f:num->real. !n:num. !i:num. i <= n ==> f i <= Maximum f n",
    MaximumLeast -> "!f:num->real. !n:num. !c:real. (!i:num. i <= n ==> f i <= c) ==> Maximum f n <= c",
    MaximumAttained -> "!f:num->real. !n:num. ?i:num. i <= n /\\ Maximum f n = f i",
    MaximumMonotone ->
      "!f:num->real. !g:num->real. !n:num. (!i:num. i <= n ==> f i <= g i) ==> Maximum f n <= Maximum g n",
    SumGroups -> "!f:num->real. !w:num. !j:num. Sum f (w * j) = Sum (\\s:num. Sum (\\g:num. f (w * s + g)) w) j",
    SumIndicator -> "!f:num->real. !n:num. !g:num. g < n ==> Sum (\\y:num. f y * COND (y = g) (1:real) 0) n = f g",
    SumCondCount ->
      "!x:real. !z:real. !n:num. !g:num. g < n ==> Sum (\\s:num. COND (s = g) x z) n = x + (real_of_num n - 1) * z",
    MaximumCongruenceBelow ->
      "!f:num->real. !g:num->real. !n:num. (!i:num. i <= n ==> f i = g i) ==> Maximum f n = Maximum g n",
    MaximumScale -> "!f:num->real. !c:real. !n:num. 0 <= c ==> Maximum (\\a:num. c * f a) n = c * Maximum f n",
    ArgmaxAttains -> "!f:num->real. !n:num. Argmax f n <= n /\\ f (Argmax f n) = Maximum f n",
    ArgmaxUnique ->
      "!f:num->real. !n:num. !j:num. j <= n ==> (!i:num. i <= n ==> ~(i = j) ==> f i < f j) ==> Argmax f n = j",
    ValueByPosterior ->
      ("!n:num. !m:num. !top:num. !prior:num->real. !k:num->num->real. !u:num->num->real. " +
        "(!s:num. s < m ==> 0 < Sum (\\y:num. prior y * k y s) n) ==> " +
        "VALUE n m top prior k u = Sum (\\s:num. Sum (\\y:num. prior y * k y s) n * " +
        "Maximum (\\a:num. Sum (\\y:num. prior y * k y s * inv (Sum (\\z:num. prior z * k z s) n) * u a y) n) top) m"),
    GarbledTerm ->
      ("!n:num. !m:num. !prior:num->real. !k:num->num->real. !g:num->num->real. !u:num->num->real. " +
        "!a:num. !t:num. " +
        "Sum (\\y:num. prior y * Sum (\\s:num. k y s * g s t) m * u a y) n = " +
        "Sum (\\s:num. g s t * Sum (\\y:num. prior y * k y s * u a y) n) m"),
    Blackwell ->
      ("!n:num. !m:num. !r:num. !top:num. !prior:num->real. !k:num->num->real. !g:num->num->real. " +
        "!u:num->num->real. CHANNEL m r g ==> " +
        "VALUE n r top prior (\\y:num. \\t:num. Sum (\\s:num. k y s * g s t) m) u <= VALUE n m top prior k u")
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  /** The steps, in the order each may use the ones before it. */
  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    MaximumUpper -> (_.upper),
    MaximumLeast -> (_.least),
    MaximumAttained -> (_.attained),
    MaximumMonotone -> (_.monotone),
    MaximumCongruenceBelow -> (_.congruenceBelow),
    MaximumScale -> (_.scale),
    SumGroups -> (_.groups),
    SumIndicator -> (_.indicator),
    SumCondCount -> (_.condCount),
    ArgmaxAttains -> (_.argmaxAttains),
    ArgmaxUnique -> (_.argmaxUnique),
    GarbledTerm -> (_.garbledTerm),
    Blackwell -> (_.blackwell),
    ValueByPosterior -> (_.byPosterior)
  )

  /**
   * The development over the end of the chain, extending `base`.
   *
   * `lookup` answers a fact of any link below by name: the sums of `Series`, `max` of `Magnitude`,
   * the order of `num` and the complex numbers' extensionality, which the shared driver carries and
   * no real goal here reaches.
   */
  def construct(
    classical: Classical,
    naturals: Natural,
    ring: Ring,
    magnitude: Magnitude,
    lookup: String => R[Kernel.Thm],
    reals: RealTheory,
    within: Kernel.Thm,
    base: Theory,
    notation: Notation
  ): R[Decision] = {
    val reals_ = TyApp(Real.TypeName, Nil)
    val f = Term.variable("f", Type.fun(TyApp(Natural.TypeName, Nil), reals_))

    def define(theory: Theory, name: String, text: String): R[(Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, notation, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    for {
      narrow <- classical.logic.over(base)
      recursion <- naturals.recursion
      maximised <- Recursion.define(
        narrow, naturals, base, notation, recursion, MaximumName, reals_,
        "(f:num->real) 0", "\\v:real. \\i:num. max v ((f:num->real) (SUC i))", Some(f)
      )
      (withMaximum, maximumDefinition, atZero, atSuccessor) = maximised
      afterMaximum <- classical.logic.over(withMaximum)
      chosen <- Recursion.define(
        afterMaximum, naturals, withMaximum, notation, recursion, ArgmaxName, TyApp(Natural.TypeName, Nil),
        "0:num", "\\v:num. \\i:num. COND (Maximum (f:num->real) i < f (SUC i)) (SUC i) v", Some(f)
      )
      (withArgmax, argmaxDefinition, argmaxAtZero, argmaxAtSuccessor) = chosen
      introduced <- Bodies.foldLeft[R[(Theory, Map[String, Kernel.Thm])]](Right((withArgmax, Map.empty))) {
        case (acc, (name, text)) =>
          for {
            state <- acc
            made <- define(state._1, name, text)
          } yield (made._1, state._2 + (name -> made._2))
      }
      (theory, bodies) = introduced
      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      induction <- naturals.fact(Natural.Induction)
      extensional <- lookup(Complex.Extensional)
      driver = Complex.Driver(logic, ring, linarith, theory, notation, extensional, Vector.empty)
      definitions = bodies + (MaximumName -> maximumDefinition) + (ArgmaxName -> argmaxDefinition)
      held = Map(MaximumAtZero -> atZero, MaximumAtSuccessor -> atSuccessor,
        ArgmaxAtZero -> argmaxAtZero, ArgmaxAtSuccessor -> argmaxAtSuccessor) ++
        bodies.map { case (name, equation) => (s"$name/definition", equation) }
      kit = ComplexKit(logic, classical, theory, notation, ring, linarith, driver, induction,
        name => held.get(name).toRight(MissingDefinition(name)).orElse(lookup(name)), within, reals, definitions)
      facts <- ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, known))

      _ <- Statements.foldLeft[R[Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Decision(theory, notation, logic, definitions, facts,
      kit.copy(lookup = name => facts.get(name).orElse(held.get(name)).toRight(MissingDefinition(name)).orElse(lookup(name))),
      held ++ facts)
  }

  /**
   * The derivations, and the steps they are written in. Package-visible so an instance, the
   * essay's E5 in the test scope, is written in the same steps over the same theory rather than in
   * a copy of them.
   */
  private[theories] final class Proofs(val kit: ComplexKit, known: Map[String, Kernel.Thm]) {
    import kit.*

    val Numbers: Type = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", Numbers)

    def k(name: String): Kernel.Thm = known(name)

    /** A number variable as text the parser reads back as the same variable. */
    def v(x: FVar): String = s"(${x.name}:num)"

    /** `!x. A ==> ... ==> B` proved by `body` from the variables and the antecedents assumed. */
    def every(goal: Term)(body: (Vector[FVar], Vector[Kernel.Thm], Term) => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        stripped <- Logic.stripForall(goal)
        (vars, inner) = stripped
        proved <- underHyps(inner)((hyps, conclusion) => body(vars, hyps, conclusion))
        out <- rules.genAll(proved, vars.toList)
      } yield out

    /** `G |- p \/ q` eliminated by a proof of the conclusion under each disjunct. */
    def byCases(disjunction: Kernel.Thm)(left: Kernel.Thm => R[Kernel.Thm], right: Kernel.Thm => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        halves <- logic.destDisj(disjunction.conclusion).toRight(NotOfForm("a disjunction", disjunction.conclusion))
        l <- LogicError.lift(Kernel.assume(halves._1)).flatMap(left)
        r <- LogicError.lift(Kernel.assume(halves._2)).flatMap(right)
        out <- rules.disjElim(disjunction, l, r)
      } yield out

    /** `f a = f b` from `a = b`. */
    def under(fn: String, equation: Kernel.Thm): R[Kernel.Thm] =
      term(fn, Type.fun(Numbers, TyApp(Real.TypeName, Nil))).flatMap(Conv.apTerm(_, equation))

    /** [[MaximumUpper]], by induction on `n` with `i` inside. */
    def upper: R[Kernel.Thm] =
      for {
        body <- prop("!i:num. i <= (n:num) ==> (f:num->real) i <= Maximum f n")
        proved <- induct(n, body)(
          base =>
            every(base) { (vs, hs, goal) =>
              val i = vs(0)
              for {
                zero <- at(fact("NUM_LE_ZERO"), s"${v(i)} <= 0 ==> ${v(i)} = 0").flatMap(mp(_, hs(0)))
                fi <- under("f:num->real", zero)
                out <- linAfter(Seq(k(MaximumAtZero)), Seq(fi), goal)
              } yield out
            },
          (kv, hypothesis, step) =>
            every(step) { (vs, hs, goal) =>
              val i = vs(0)
              for {
                split <- at(fact("NUM_LE_CASES"), s"${v(i)} <= SUC ${v(kv)} ==> ${v(i)} < SUC ${v(kv)} \\/ ${v(i)} = SUC ${v(kv)}")
                  .flatMap(mp(_, hs(0)))
                out <- byCases(split)(
                  below =>
                    for {
                      le <- at(fact("NUM_LE_OF_LT_SUC"), s"${v(i)} < SUC ${v(kv)} ==> ${v(i)} <= ${v(kv)}").flatMap(mp(_, below))
                      ih <- rules.spec(i, hypothesis).flatMap(mp(_, le))
                      left <- at(fact("MAX_ABOVE_LEFT"), s"Maximum (f:num->real) ${v(kv)} <= max (Maximum f ${v(kv)}) (f (SUC ${v(kv)}))")
                      out <- linAfter(Seq(k(MaximumAtSuccessor)), Seq(ih, left), goal)
                    } yield out,
                  same =>
                    for {
                      fi <- under("f:num->real", same)
                      right <- at(fact("MAX_ABOVE_RIGHT"), s"(f:num->real) (SUC ${v(kv)}) <= max (Maximum f ${v(kv)}) (f (SUC ${v(kv)}))")
                      out <- linAfter(Seq(k(MaximumAtSuccessor)), Seq(fi, right), goal)
                    } yield out
                )
              } yield out
            }
        )
        f <- term("f:num->real", Type.fun(Numbers, TyApp(Real.TypeName, Nil))).flatMap {
          case x: FVar => Right(x)
          case other => Left(NotOfForm("a variable", other))
        }
        out <- gen(proved, f)
      } yield out

    def variable(text: String, ty: Type): R[FVar] =
      term(text, ty).flatMap {
        case x: FVar => Right(x)
        case other => Left(NotOfForm("a variable", other))
      }

    val Functions: Type = Type.fun(Numbers, TyApp(Real.TypeName, Nil))

    /** [[MaximumLeast]], by induction on `n` with the bound `c` fixed. */
    def least: R[Kernel.Thm] =
      for {
        body <- prop("(!i:num. i <= (n:num) ==> (f:num->real) i <= (c:real)) ==> Maximum f n <= c")
        proved <- induct(n, body)(
          base =>
            underHyps(base) { (hs, goal) =>
              for {
                refl <- at(fact("NUM_LE_REFL"), "(0:num) <= 0")
                f0 <- at(hs(0), "(0:num) <= 0 ==> (f:num->real) 0 <= (c:real)").flatMap(mp(_, refl))
                out <- linAfter(Seq(k(MaximumAtZero)), Seq(f0), goal)
              } yield out
            },
          (kv, hypothesis, step) =>
            underHyps(step) { (hs, goal) =>
              val K = v(kv)
              for {
                below <- prop(s"!i:num. i <= $K ==> (f:num->real) i <= (c:real)")
                bounded <- every(below) { (vs, ks, _) =>
                  val i = v(vs(0))
                  for {
                    suc <- at(fact("NUM_LE_SUC"), s"$K <= SUC $K")
                    both <- conj(ks(0), suc)
                    wider <- at(fact("NUM_LE_TRANS"), s"$i <= $K /\\ $K <= SUC $K ==> $i <= SUC $K").flatMap(mp(_, both))
                    out <- at(hs(0), s"$i <= SUC $K ==> (f:num->real) $i <= (c:real)").flatMap(mp(_, wider))
                  } yield out
                }
                ih <- mp(hypothesis, bounded)
                refl <- at(fact("NUM_LE_REFL"), s"SUC $K <= SUC $K")
                top <- at(hs(0), s"SUC $K <= SUC $K ==> (f:num->real) (SUC $K) <= (c:real)").flatMap(mp(_, refl))
                joined <- at(fact("MAX_LEAST"),
                  s"Maximum (f:num->real) $K <= (c:real) ==> f (SUC $K) <= c ==> max (Maximum f $K) (f (SUC $K)) <= c")
                  .flatMap(mp(_, ih, top))
                out <- linAfter(Seq(k(MaximumAtSuccessor)), Seq(joined), goal)
              } yield out
            }
        )
        f <- variable("f:num->real", Functions)
        c <- variable("c:real", TyApp(Real.TypeName, Nil))
        out <- gen(proved, f, c).flatMap(reordered(_, MaximumLeast))
      } yield out

    /** `thm` with its quantifiers in the order [[Statements]] writes them, by matching. */
    def reordered(thm: Kernel.Thm, name: String): R[Kernel.Thm] =
      for {
        wanted <- prop(StatementsMap(name))
        stripped <- Logic.stripForall(wanted)
        (vars, body) = stripped
        opened <- rules.specTo(thm, body)
        out <- rules.genAll(opened, vars.toList)
      } yield out

    /** [[MaximumAttained]], by induction on `n`, and a case on which side `max` takes. */
    def attained: R[Kernel.Thm] =
      for {
        body <- prop("?i:num. i <= (n:num) /\\ Maximum (f:num->real) n = f i")
        proved <- induct(n, body)(
          base =>
            for {
              refl <- at(fact("NUM_LE_REFL"), "(0:num) <= 0")
              zero <- at(k(MaximumAtZero), "Maximum (f:num->real) 0 = f 0")
              both <- conj(refl, zero)
              zeroTerm <- nm("0")
              out <- existsIntro("?i:num. i <= 0 /\\ Maximum (f:num->real) 0 = f i", zeroTerm, both)
            } yield out,
          (kv, hypothesis, step) =>
            val K = v(kv)
            for {
              unfolded <- at(k(MaximumAtSuccessor), s"Maximum (f:num->real) (SUC $K) = max (Maximum f $K) (f (SUC $K))")
              sides <- at(fact("MAX_CASES"),
                s"max (Maximum (f:num->real) $K) (f (SUC $K)) = Maximum f $K \\/ max (Maximum f $K) (f (SUC $K)) = f (SUC $K)")
              wanted = s"?i:num. i <= SUC $K /\\ Maximum (f:num->real) (SUC $K) = f i"
              out <- byCases(sides)(
                left =>
                  choose(hypothesis, "j") { (j, held) =>
                    val J = v(j)
                    for {
                      parts <- split(held)
                      suc <- at(fact("NUM_LE_SUC"), s"$K <= SUC $K")
                      both <- conj(parts(0), suc)
                      wider <- at(fact("NUM_LE_TRANS"), s"$J <= $K /\\ $K <= SUC $K ==> $J <= SUC $K").flatMap(mp(_, both))
                      equal <- trans(unfolded, left, parts(1))
                      witness <- conj(wider, equal)
                      out <- existsIntro(wanted, j, witness)
                    } yield out
                  },
                right =>
                  for {
                    refl <- at(fact("NUM_LE_REFL"), s"SUC $K <= SUC $K")
                    equal <- trans(unfolded, right)
                    witness <- conj(refl, equal)
                    point <- nm(s"SUC $K")
                    out <- existsIntro(wanted, point, witness)
                  } yield out
              )
            } yield out
        )
        f <- variable("f:num->real", Functions)
        out <- gen(proved, f).flatMap(reordered(_, MaximumAttained))
      } yield out

    /** [[MaximumMonotone]], from the two above: every `f i` is below `g i`, which is below the top. */
    def monotone: R[Kernel.Thm] =
      for {
        goal <- prop(StatementsMap(MaximumMonotone))
        out <- every(goal) { (vs, hs, conclusion) =>
          val N = v(vs(2))
          for {
            pointwise <- prop(s"!i:num. i <= $N ==> (f:num->real) i <= Maximum (g:num->real) $N")
            bounded <- every(pointwise) { (is, ks, _) =>
              val i = v(is(0))
              for {
                fg <- at(hs(0), s"$i <= $N ==> (f:num->real) $i <= (g:num->real) $i").flatMap(mp(_, ks(0)))
                gtop <- at(k(MaximumUpper), s"$i <= $N ==> (g:num->real) $i <= Maximum g $N").flatMap(mp(_, ks(0)))
                out <- lin(Seq(fg, gtop), s"(f:num->real) $i <= Maximum (g:num->real) $N")
              } yield out
            }
            out <- at(k(MaximumLeast),
              s"(!i:num. i <= $N ==> (f:num->real) i <= Maximum (g:num->real) $N) ==> Maximum f $N <= Maximum g $N")
              .flatMap(mp(_, bounded))
          } yield out
        }
      } yield out

    /** `max x y = y` from `x <= y`, and `max x y = x` from `y <= x`. */
    def maxRight(x0: String, y0: String, le: Kernel.Thm): R[Kernel.Thm] =
      val (x, y) = (s"($x0)", s"($y0)")
      for {
        refl <- lemma(s"!z:real. z <= z").flatMap(at(_, s"$y <= $y"))
        least <- at(fact("MAX_LEAST"), s"$x <= $y ==> $y <= $y ==> max $x $y <= $y").flatMap(mp(_, le, refl))
        above <- at(fact("MAX_ABOVE_RIGHT"), s"$y <= max $x $y")
        out <- lin(Seq(least, above), s"max $x $y = $y")
      } yield out

    def maxLeft(x0: String, y0: String, le: Kernel.Thm): R[Kernel.Thm] =
      val (x, y) = (s"($x0)", s"($y0)")
      for {
        refl <- lemma(s"!z:real. z <= z").flatMap(at(_, s"$x <= $x"))
        least <- at(fact("MAX_LEAST"), s"$x <= $x ==> $y <= $x ==> max $x $y <= $x").flatMap(mp(_, refl, le))
        above <- at(fact("MAX_ABOVE_LEFT"), s"$x <= max $x $y")
        out <- lin(Seq(least, above), s"max $x $y = $x")
      } yield out

    /** [[MaximumCongruenceBelow]]: monotone both ways. */
    def congruenceBelow: R[Kernel.Thm] =
      for {
        goal <- prop(StatementsMap(MaximumCongruenceBelow))
        out <- every(goal) { (vs, hs, conclusion) =>
          val N = v(vs(2))
          def one(left: String, right: String): R[Kernel.Thm] =
            for {
              each <- prop(s"!i:num. i <= $N ==> ($left:num->real) i <= ($right:num->real) i")
              pointwise <- every(each) { (is, ks, _) =>
                val I = v(is(0))
                for {
                  equal <- at(hs(0), s"$I <= $N ==> (f:num->real) $I = (g:num->real) $I").flatMap(mp(_, ks(0)))
                  out <- lin(Seq(equal), s"($left:num->real) $I <= ($right:num->real) $I")
                } yield out
              }
              out <- at(k(MaximumMonotone),
                s"(!i:num. i <= $N ==> ($left:num->real) i <= ($right:num->real) i) ==> Maximum $left $N <= Maximum $right $N")
                .flatMap(mp(_, pointwise))
            } yield out
          for {
            up <- one("f", "g")
            down <- one("g", "f")
            out <- lin(Seq(up, down), s"Maximum (f:num->real) $N = Maximum (g:num->real) $N")
          } yield out
        }
      } yield out

    /** [[SumGroups]], by induction on the number of blocks: one more block is `SUM_REINDEX` at its start. */
    def groups: R[Kernel.Thm] = {
      val j = Term.variable("j", Numbers)
      for {
        body <- prop("Sum (f:num->real) ((w:num) * (j:num)) = Sum (\\s:num. Sum (\\g:num. f (w * s + g)) w) j")
        proved <- induct(j, body)(
          base =>
            for {
              zero <- at(fact("NUM_MUL_ZERO"), "(w:num) * 0 = 0")
              empty <- fact("SUM_ZERO")
              out <- linAfter(Seq(zero, empty), Seq.empty, base)
            } yield out,
          (jv, hypothesis, step) =>
            val J = v(jv)
            for {
              suc <- at(fact("NUM_MUL_SUC"), s"(w:num) * SUC $J = w * $J + w")
              last <- at(fact("SUM_SUC"),
                s"Sum (\\s:num. Sum (\\g:num. (f:num->real) ((w:num) * s + g)) w) (SUC $J) = " +
                  s"Sum (\\s:num. Sum (\\g:num. f (w * s + g)) w) $J + Sum (\\g:num. f (w * $J + g)) w")
              block <- at(fact("SUM_REINDEX"),
                s"Sum (\\g:num. (f:num->real) ((w:num) * $J + g)) w = Sum f (w * $J + w) - Sum f (w * $J)")
              out <- linAfter(Seq(suc, last), Seq(block, hypothesis), step)
            } yield out
        )
        f <- variable("f:num->real", Functions)
        w <- variable("w:num", Numbers)
        out <- gen(proved, f, w).flatMap(reordered(_, SumGroups))
      } yield out
    }

    /** `~(y = g)` from `g < y`: were they equal, the order would be irreflexive at `g`. */
    def apart(y: String, g: String, below: Kernel.Thm): R[Kernel.Thm] =
      for {
        equation <- prop(s"$y = $g")
        assumed <- LogicError.lift(Kernel.assume(equation))
        moved <- rw(assumed, below)
        irreflexive <- at(fact("NUM_LT_IRREFL"), s"~($g < $g)")
        absurd <- rules.notElim(irreflexive, moved)
        out <- rules.notIntro(equation, absurd)
      } yield out

    val Indicator = "Sum (\\y:num. (f:num->real) y * COND (y = (g:num)) (1:real) 0)"

    /** Every term below `n` vanishes when the indicator's point is not below it: `Sum ... n = 0` for `n <= g`. */
    def indicatorBelow(nText: String, gText: String, apartBelow: (FVar, Kernel.Thm) => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        each <- prop(s"!y:num. y < $nText ==> (f:num->real) y * COND (y = $gText) (1:real) 0 = 0")
        zero <- every(each) { (ys, yhs, goal) =>
          val Y = v(ys(0))
          for {
            ne <- apartBelow(ys(0), yhs(0))
            off <- at(fact("COND_FALSE"), s"~($Y = $gText) ==> COND ($Y = $gText) (1:real) 0 = 0").flatMap(mp(_, ne))
            out <- linAfter(Seq(off), Seq.empty, goal)
          } yield out
        }
        same <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!y:num. y < $nText ==> (f:num->real) y * COND (y = $gText) (1:real) 0 = (\\y:num. (0:real)) y) ==> " +
            s"Sum (\\y:num. f y * COND (y = $gText) 1 0) $nText = Sum (\\y:num. 0) $nText")
          .flatMap(thm => mp(thm, zero))
        nothing <- at(fact("SUM_OF_ZERO"), s"Sum (\\y:num. (0:real)) $nText = 0")
        out <- trans(same, nothing)
      } yield out

    /** [[SumIndicator]], by induction on `n` with the point `g` inside. */
    def indicator: R[Kernel.Thm] =
      for {
        body <- prop(s"!g:num. g < (n:num) ==> $Indicator n = (f:num->real) g")
        proved <- induct(n, body)(
          base =>
            every(base) { (gs, ghs, _) =>
              for {
                never <- at(fact("NUM_NOT_LT_ZERO"), s"~(${v(gs(0))} < 0)")
                absurd <- rules.notElim(never, ghs(0))
                goal <- prop(s"Sum (\\y:num. (f:num->real) y * COND (y = ${v(gs(0))}) (1:real) 0) 0 = f ${v(gs(0))}")
                out <- rules.falsityElim(goal, absurd)
              } yield out
            },
          (kv, hypothesis, step) =>
            val K = v(kv)
            every(step) { (gs, ghs, goal) =>
              val G = v(gs(0))
              for {
                split <- at(fact("NUM_LT_SUC_CASES"), s"$G < SUC $K ==> $G < $K \\/ $G = $K").flatMap(mp(_, ghs(0)))
                last <- at(fact("SUM_SUC"),
                  s"Sum (\\y:num. (f:num->real) y * COND (y = $G) (1:real) 0) (SUC $K) = " +
                    s"Sum (\\y:num. f y * COND (y = $G) 1 0) $K + f $K * COND ($K = $G) 1 0")
                out <- byCases(split)(
                  below =>
                    for {
                      ih <- at(hypothesis, s"$G < $K ==> Sum (\\y:num. (f:num->real) y * COND (y = $G) (1:real) 0) $K = f $G")
                        .flatMap(mp(_, below))
                      // `K = G` turns `G < K` into `G < G`
                      ne <- apart(K, G, below)
                      off <- at(fact("COND_FALSE"), s"~($K = $G) ==> COND ($K = $G) (1:real) 0 = 0").flatMap(mp(_, ne))
                      out <- linAfter(Seq(last, off), Seq(ih), goal)
                    } yield out,
                  same =>
                    for {
                      empty <- indicatorBelow(K, G, (y, yBelow) =>
                        for {
                          equation <- prop(s"${v(y)} = $G")
                          assumed <- LogicError.lift(Kernel.assume(equation))
                          toK <- trans(assumed, same)
                          moved <- rw(toK, yBelow)
                          irreflexive <- at(fact("NUM_LT_IRREFL"), s"~($K < $K)")
                          absurd <- rules.notElim(irreflexive, moved)
                          out <- rules.notIntro(equation, absurd)
                        } yield out)
                      back <- Conv.sym(same)
                      on <- at(fact("COND_TRUE"), s"$K = $G ==> COND ($K = $G) (1:real) 0 = 1").flatMap(mp(_, back))
                      fg <- under("f:num->real", same)
                      out <- linAfter(Seq(last, on, empty), Seq(fg), goal)
                    } yield out
                )
              } yield out
            }
        )
        f <- variable("f:num->real", Functions)
        out <- gen(proved, f).flatMap(reordered(_, SumIndicator))
      } yield out

    /** [[SumCondCount]]: the conditional is the constant plus a scaled indicator, and each is summed. */
    def condCount: R[Kernel.Thm] = {
      val sv = Term.variable("s", Numbers)
      for {
        hyp <- assume("(g:num) < (n:num)")
        pointwise <- cases("(s:num) = (g:num)")(
          on =>
            for {
              a <- at(fact("COND_TRUE"), "(s:num) = (g:num) ==> COND (s = g) (x:real) (z:real) = x").flatMap(mp(_, on))
              b <- at(fact("COND_TRUE"), "(s:num) = (g:num) ==> COND (s = g) (1:real) 0 = 1").flatMap(mp(_, on))
              out <- linAfterText(Seq(a, b), Seq.empty,
                "COND ((s:num) = (g:num)) (x:real) (z:real) = z + (x - z) * COND (s = g) (1:real) 0")
            } yield out,
          off =>
            for {
              a <- at(fact("COND_FALSE"), "~((s:num) = (g:num)) ==> COND (s = g) (x:real) (z:real) = z").flatMap(mp(_, off))
              b <- at(fact("COND_FALSE"), "~((s:num) = (g:num)) ==> COND (s = g) (1:real) 0 = 0").flatMap(mp(_, off))
              out <- linAfterText(Seq(a, b), Seq.empty,
                "COND ((s:num) = (g:num)) (x:real) (z:real) = z + (x - z) * COND (s = g) (1:real) 0")
            } yield out
        )
        summed <- cong("Sum", sv, pointwise, "(n:num)")
        split <- at(fact("SUM_ADD"),
          "Sum (\\s:num. (z:real) + ((x:real) - z) * COND (s = (g:num)) (1:real) 0) (n:num) = " +
            "Sum (\\s:num. z) n + Sum (\\s:num. (x - z) * COND (s = g) 1 0) n")
        constant <- at(fact("SUM_CONSTANT"), "Sum (\\s:num. (z:real)) (n:num) = real_of_num n * z")
        picked <- at(k(SumIndicator),
          "(g:num) < (n:num) ==> Sum (\\y:num. ((x:real) - (z:real)) * COND (y = g) (1:real) 0) n = x - z").flatMap(mp(_, hyp))
        out <- linAfterText(Seq(summed, split, constant, picked), Seq.empty,
          "Sum (\\s:num. COND (s = (g:num)) (x:real) (z:real)) (n:num) = x + (real_of_num n - 1) * z")
        discharged <- disch("(g:num) < (n:num)", out)
        result <- closed(discharged, SumCondCount)
      } yield result
    }

    /** [[MaximumScale]], by induction on `n`: a non-negative scale keeps the side `max` takes. */
    def scale: R[Kernel.Thm] =
      for {
        body <- prop("(0:real) <= (c:real) ==> Maximum (\\a:num. c * (f:num->real) a) (n:num) = c * Maximum f n")
        proved <- induct(n, body)(
          base => underHyps(base)((_, goal) => linAfter(Seq(k(MaximumAtZero)), Seq.empty, goal)),
          (kv, hypothesis, step) =>
            underHyps(step) { (hs, goal) =>
              val K = v(kv)
              val M = s"Maximum (f:num->real) $K"
              val Y = s"(f:num->real) (SUC $K)"
              for {
                ih <- mp(hypothesis, hs(0))
                out <- cases(s"$M <= $Y")(
                  le =>
                    for {
                      plain <- maxRight(M, Y, le)
                      scaledLe <- lin(Seq(hs(0), le), s"(c:real) * $M <= c * $Y")
                      scaled <- maxRight(s"((c:real) * $M)", s"((c:real) * $Y)", scaledLe)
                      out <- linAfter(Seq(k(MaximumAtSuccessor), ih, plain, scaled), Seq.empty, goal)
                    } yield out,
                  notLe =>
                    for {
                      strict <- at(fact("LT_OF_NOT_LE"), s"~($M <= $Y) ==> $Y < $M").flatMap(mp(_, notLe))
                      ge <- lin(Seq(strict), s"$Y <= $M")
                      plain <- maxLeft(M, Y, ge)
                      scaledGe <- lin(Seq(hs(0), ge), s"(c:real) * $Y <= c * $M")
                      scaled <- maxLeft(s"((c:real) * $M)", s"((c:real) * $Y)", scaledGe)
                      out <- linAfter(Seq(k(MaximumAtSuccessor), ih, plain, scaled), Seq.empty, goal)
                    } yield out
                )
              } yield out
            }
        )
        f <- variable("f:num->real", Functions)
        c <- variable("c:real", TyApp(Real.TypeName, Nil))
        out <- gen(proved, f, c).flatMap(reordered(_, MaximumScale))
      } yield out

    /** [[ArgmaxAttains]], by induction on `n`, on the side the comparison in the step took. */
    def argmaxAttains: R[Kernel.Thm] =
      for {
        body <- prop("Argmax (f:num->real) (n:num) <= n /\\ f (Argmax f n) = Maximum f n")
        proved <- induct(n, body)(
          base =>
            for {
              zero <- at(k(ArgmaxAtZero), "Argmax (f:num->real) 0 = 0")
              refl <- at(fact("NUM_LE_REFL"), "(0:num) <= 0")
              low <- closedBy(Seq(zero), "Argmax (f:num->real) 0 <= 0", refl)
              valueGoal <- prop("(f:num->real) (Argmax f 0) = Maximum f 0")
              value <- linAfter(Seq(zero, k(MaximumAtZero)), Seq.empty, valueGoal)
              out <- conj(low, value)
            } yield out,
          (kv, hypothesis, step) =>
            val K = v(kv)
            val M = s"Maximum (f:num->real) $K"
            val Y = s"(f:num->real) (SUC $K)"
            for {
              unfolded <- at(k(ArgmaxAtSuccessor), s"Argmax (f:num->real) (SUC $K) = COND ($M < $Y) (SUC $K) (Argmax f $K)")
              held <- split(hypothesis)
              valueGoal <- prop(s"(f:num->real) (Argmax f (SUC $K)) = Maximum f (SUC $K)")
              out <- cases(s"$M < $Y")(
                less =>
                  for {
                    chosen <- at(fact("COND_TRUE"), s"$M < $Y ==> COND ($M < $Y) (SUC $K) (Argmax f $K) = SUC $K")
                      .flatMap(mp(_, less))
                    picked <- trans(unfolded, chosen)
                    refl <- at(fact("NUM_LE_REFL"), s"SUC $K <= SUC $K")
                    low <- closedBy(Seq(picked), s"Argmax (f:num->real) (SUC $K) <= SUC $K", refl)
                    le <- lin(Seq(less), s"$M <= $Y")
                    top <- maxRight(M, Y, le)
                    value <- linAfter(Seq(picked, k(MaximumAtSuccessor), top), Seq.empty, valueGoal)
                    out <- conj(low, value)
                  } yield out,
                notLess =>
                  for {
                    kept <- at(fact("COND_FALSE"), s"~($M < $Y) ==> COND ($M < $Y) (SUC $K) (Argmax f $K) = Argmax f $K")
                      .flatMap(mp(_, notLess))
                    picked <- trans(unfolded, kept)
                    suc <- at(fact("NUM_LE_SUC"), s"$K <= SUC $K")
                    both <- conj(held(0), suc)
                    wider <- at(fact("NUM_LE_TRANS"), s"Argmax (f:num->real) $K <= $K /\\ $K <= SUC $K ==> Argmax f $K <= SUC $K")
                      .flatMap(mp(_, both))
                    low <- closedBy(Seq(picked), s"Argmax (f:num->real) (SUC $K) <= SUC $K", wider)
                    ge <- at(fact("LE_OF_NOT_LT"), s"~($M < $Y) ==> $Y <= $M").flatMap(mp(_, notLess))
                    top <- maxLeft(M, Y, ge)
                    value <- linAfter(Seq(picked, k(MaximumAtSuccessor), top, held(1)), Seq.empty, valueGoal)
                    out <- conj(low, value)
                  } yield out
              )
            } yield out
        )
        f <- variable("f:num->real", Functions)
        out <- gen(proved, f).flatMap(reordered(_, ArgmaxAttains))
      } yield out

    /** [[ArgmaxUnique]]: the rule attains the maximum, and anywhere but `j` it would fall short of `f j`. */
    def argmaxUnique: R[Kernel.Thm] =
      for {
        goal <- prop(StatementsMap(ArgmaxUnique))
        out <- every(goal) { (vs, hs, conclusion) =>
          val F = s"(${vs(0).name}:num->real)"
          val N = v(vs(1))
          val J = v(vs(2))
          val A = s"Argmax $F $N"
          for {
            attains <- spec(k(ArgmaxAttains), vs(0), vs(1)).flatMap(split)
            upper <- spec(k(MaximumUpper), vs(0), vs(1), vs(2)).flatMap(mp(_, hs(0)))
            out <- cases(s"$A = $J")(
              same => Right(same),
              other =>
                for {
                  short <- at(hs(1), s"$A <= $N ==> ~($A = $J) ==> $F ($A) < $F $J").flatMap(mp(_, attains(0), other))
                  absurd <- lin(Seq(short, upper, attains(1)), "F")
                  out <- rules.falsityElim(conclusion, absurd)
                } yield out
            )
          } yield out
        }
      } yield out

    /** `goal`, rewritten with `equations` until it is what `known` says, then read back. */
    def closedBy(equations: Seq[Kernel.Thm], goal: String, known: Kernel.Thm): R[Kernel.Thm] =
      for {
        g <- prop(goal)
        set <- Rewrite.Rule.all(logic, equations.toVector)
        forward <- Rewrite.rewrite(set, g)
        back <- Conv.sym(forward)
        out <- LogicError.lift(Kernel.eqMp(back, known))
      } yield out

    val Reals: Type = TyApp(Real.TypeName, Nil)
    val Sequences: Type = Type.fun(Type.fun(Numbers, Reals), Type.fun(Numbers, Reals))

    /** `C F n = C G n` for `C` either `Sum` or `Maximum`, from `F x = G x` at a variable nothing assumes. */
    def cong(name: String, x: FVar, pointwise: Kernel.Thm, length: String): R[Kernel.Thm] =
      for {
        lambdas <- LogicError.lift(Kernel.abs(x, pointwise))
        constant <- term(name, Sequences)
        len <- nm(length)
        out <- Conv.apTerm(constant, lambdas).flatMap(Conv.apThm(_, len)).flatMap(beta)
      } yield out

    /** A defined constant applied to `arguments`, unfolded and beta-reduced. */
    def unfold(name: String, arguments: String*): R[Kernel.Thm] =
      for {
        args <- arguments.toList.foldLeft[R[List[Term]]](Right(Nil))((acc, a) =>
          for { done <- acc; t <- prop0(a) } yield done :+ t)
        applied <- args.foldLeft[R[Kernel.Thm]](Right(k(s"$name/definition")))((acc, a) => acc.flatMap(Conv.apThm(_, a)))
        out <- beta(applied)
      } yield out

    /** A term written with its type annotations inside, read as it stands. */
    def prop0(text: String): R[Term] = Parser.term(theory, notation, text).flatMap(normal)

    def fresh(name: String, ty: Type): FVar = Term.variable(name, ty)

    /** [[ComplexKit.linAfter]] at a goal written as text. */
    def linAfterText(equations: Seq[Kernel.Thm], facts: Seq[Kernel.Thm], goal: String): R[Kernel.Thm] =
      prop(goal).flatMap(linAfter(equations, facts, _))

    val Kernels = Type.fun(Numbers, Type.fun(Numbers, Reals))
    val P = "(prior:num->real)"
    val Kt = "(k:num->num->real)"
    val G = "(g:num->num->real)"
    val U = "(u:num->num->real)"

    /** [[GarbledTerm]]: the scale pushed in, the sums exchanged, the garbling pulled out. */
    def garbledTerm: R[Kernel.Thm] = {
      val y = fresh("y", Numbers)
      val s = fresh("s", Numbers)
      for {
        // at each y: prior y * (sum_s k y s * g s t) * u a y = sum_s prior y * k y s * u a y * g s t
        scaled <- at(fact("SUM_SCALE"),
          s"Sum (\\s:num. ($P (y:num) * $U (a:num) y) * ($Kt y s * $G s (t:num))) (m:num) = " +
            s"($P y * $U a y) * Sum (\\s:num. $Kt y s * $G s t) m")
        inner <- identity(s"$P (y:num) * $U (a:num) y * ($Kt y (s:num) * $G s (t:num)) = $P y * $Kt y s * $U a y * $G s t")
        reshaped <- cong("Sum", s, inner, "(m:num)")
        outerForm <- identity(
          s"$P (y:num) * Sum (\\s:num. $Kt y s * $G s (t:num)) (m:num) * $U (a:num) y = " +
            s"($P y * $U a y) * Sum (\\s:num. $Kt y s * $G s t) m")
        back <- Conv.sym(scaled)
        atY <- trans(outerForm, back, reshaped)
        summedY <- cong("Sum", y, atY, "(n:num)")
        swapped <- at(fact("SUM_SWAP"),
          s"Sum (\\y:num. Sum (\\s:num. $P y * $Kt y s * $U (a:num) y * $G s (t:num)) (m:num)) (n:num) = " +
            s"Sum (\\s:num. Sum (\\y:num. $P y * $Kt y s * $U a y * $G s t) n) m")
        pulled <- at(fact("SUM_SCALE_RIGHT"),
          s"Sum (\\y:num. ($P y * $Kt y (s:num) * $U (a:num) y) * $G s (t:num)) (n:num) = " +
            s"Sum (\\y:num. $P y * $Kt y s * $U a y) n * $G s t")
        commuted <- identity(s"Sum (\\y:num. $P y * $Kt y (s:num) * $U (a:num) y) (n:num) * $G s (t:num) = " +
          s"$G s t * Sum (\\y:num. $P y * $Kt y s * $U a y) n")
        atS <- trans(pulled, commuted)
        summedS <- cong("Sum", s, atS, "(m:num)")
        equal <- trans(summedY, swapped, summedS)
        out <- closed(equal, GarbledTerm)
      } yield out
    }

    /** An equation or inequality with free variables, generalised in the order [[Statements]] writes. */
    def closed(thm: Kernel.Thm, name: String): R[Kernel.Thm] =
      for {
        general <- rules.genAll(thm, Term.freeVariables(thm.conclusion).toList)
        out <- reordered(general, name)
      } yield out

    /** [[Blackwell]]: the garbled value is below a mixture of maxima, which is the original value. */
    def blackwell: R[Kernel.Thm] = {
      val t = fresh("t", Numbers)
      val a = fresh("a", Numbers)
      val s = fresh("s", Numbers)
      def X(av: String, sv: String) = s"Sum (\\y:num. $P y * $Kt y $sv * $U $av y) (n:num)"
      val M = (sv: String) => s"Maximum (\\a:num. ${X("a", sv)}) (top:num)"
      for {
        channel <- assume(s"CHANNEL (m:num) (r:num) $G")
        channelOpen <- unfold(ChannelName, "m:num", "r:num", G).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, channel)))

        // a row of g, below m, is non-negative and sums to one
        row = (sv: String, below: Kernel.Thm) =>
          for {
            dist <- at(channelOpen, s"$sv < (m:num) ==> DISTRIBUTION (r:num) ($G $sv)").flatMap(mp(_, below))
            opened <- unfold(DistributionName, "r:num", s"$G $sv").flatMap(eq => LogicError.lift(Kernel.eqMp(eq, dist)))
            parts <- split(opened)
          } yield parts

        garbled <- unfold(ValueName, "n:num", "r:num", "top:num", P,
          s"\\y:num. \\t:num. Sum (\\s:num. $Kt y s * $G s t) (m:num)", U)
        original <- unfold(ValueName, "n:num", "m:num", "top:num", P, Kt, U)

        // the garbled inner sum is the mixture, under the maximum and the outer sum
        mixed <- at(k(GarbledTerm),
          s"Sum (\\y:num. $P y * Sum (\\s:num. $Kt y s * $G s (t:num)) (m:num) * $U (a:num) y) (n:num) = " +
            s"Sum (\\s:num. $G s t * ${X("a", "s")}) m")
        underMax <- cong("Maximum", a, mixed, "(top:num)")
        underSum <- cong("Sum", t, underMax, "(r:num)")

        // at each t below r, the maximum of the mixtures is below the mixture of the maxima
        pointwise <- prop(s"!t:num. t < (r:num) ==> " +
          s"Maximum (\\a:num. Sum (\\s:num. $G s t * ${X("a", "s")}) (m:num)) (top:num) <= " +
          s"Sum (\\s:num. $G s t * ${M("s")}) m")
        bounded <- every(pointwise) { (ts, ths, _) =>
          val T = v(ts(0))
          for {
            each <- prop(s"!a:num. a <= (top:num) ==> Sum (\\s:num. $G s $T * ${X("a", "s")}) (m:num) <= " +
              s"Sum (\\s:num. $G s $T * ${M("s")}) m")
            termwise <- every(each) { (as, ahs, _) =>
              val A = v(as(0))
              for {
                below <- prop(s"!s:num. s < (m:num) ==> $G s $T * ${X(A, "s")} <= $G s $T * ${M("s")}")
                each2 <- every(below) { (ss, shs, _) =>
                  val S = v(ss(0))
                  for {
                    parts <- row(S, shs(0))
                    nonneg <- at(parts(0), s"$T < (r:num) ==> (0:real) <= $G $S $T").flatMap(mp(_, ths(0)))
                    // by the arguments and not by the instance: `f m` with both unknown is not a pattern
                    fT <- prop0(s"\\a:num. ${X("a", S)}")
                    topT <- nm("top:num")
                    upper <- spec(k(MaximumUpper), fT, topT, as(0)).flatMap(mp(_, ahs(0)))
                    out <- lin(Seq(nonneg, upper), s"$G $S $T * ${X(A, S)} <= $G $S $T * ${M(S)}")
                  } yield out
                }
                out <- at(fact("SUM_MONOTONE_BELOW"),
                  s"(!s:num. s < (m:num) ==> $G s $T * ${X(A, "s")} <= $G s $T * ${M("s")}) ==> " +
                    s"Sum (\\s:num. $G s $T * ${X(A, "s")}) m <= Sum (\\s:num. $G s $T * ${M("s")}) m")
                  .flatMap(mp(_, each2))
              } yield out
            }
            out <- at(k(MaximumLeast),
              s"(!a:num. a <= (top:num) ==> Sum (\\s:num. $G s $T * ${X("a", "s")}) (m:num) <= " +
                s"Sum (\\s:num. $G s $T * ${M("s")}) m) ==> " +
                s"Maximum (\\a:num. Sum (\\s:num. $G s $T * ${X("a", "s")}) m) top <= Sum (\\s:num. $G s $T * ${M("s")}) m")
              .flatMap(mp(_, termwise))
          } yield out
        }
        summed <- at(fact("SUM_MONOTONE_BELOW"),
          s"(!t:num. t < (r:num) ==> Maximum (\\a:num. Sum (\\s:num. $G s t * ${X("a", "s")}) (m:num)) (top:num) <= " +
            s"Sum (\\s:num. $G s t * ${M("s")}) m) ==> " +
            s"Sum (\\t:num. Maximum (\\a:num. Sum (\\s:num. $G s t * ${X("a", "s")}) m) top) r <= " +
            s"Sum (\\t:num. Sum (\\s:num. $G s t * ${M("s")}) m) r")
          .flatMap(mp(_, bounded))

        // the mixture of the maxima, summed over t, is the sum of the maxima: exchange, then each row
        swapped <- at(fact("SUM_SWAP"),
          s"Sum (\\t:num. Sum (\\s:num. $G s t * ${M("s")}) (m:num)) (r:num) = " +
            s"Sum (\\s:num. Sum (\\t:num. $G s t * ${M("s")}) r) m")
        rowSums <- prop(s"!s:num. s < (m:num) ==> Sum (\\t:num. $G s t * ${M("s")}) (r:num) = ${M("s")}")
        eachRow <- every(rowSums) { (ss, shs, _) =>
          val S = v(ss(0))
          for {
            parts <- row(S, shs(0))
            pulled <- at(fact("SUM_SCALE_RIGHT"),
              s"Sum (\\t:num. $G $S t * ${M(S)}) (r:num) = Sum ($G $S) r * ${M(S)}")
            out <- linAfterText(Seq(pulled, parts(1)), Seq.empty, s"Sum (\\t:num. $G $S t * ${M(S)}) (r:num) = ${M(S)}")
          } yield out
        }
        collapsed <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!s:num. s < (m:num) ==> Sum (\\t:num. $G s t * ${M("s")}) (r:num) = ${M("s")}) ==> " +
            s"Sum (\\s:num. Sum (\\t:num. $G s t * ${M("s")}) r) m = Sum (\\s:num. ${M("s")}) m")
          .flatMap(mp(_, eachRow))
        mixture <- trans(swapped, collapsed)
        out <- linAfterText(Seq(garbled, original, underSum), Seq(summed, mixture),
          s"VALUE (n:num) (r:num) (top:num) $P (\\y:num. \\t:num. Sum (\\s:num. $Kt y s * $G s t) (m:num)) $U <= " +
            s"VALUE n m top $P $Kt $U")
        discharged <- disch(s"CHANNEL (m:num) (r:num) $G", out)
        result <- closed(discharged, Blackwell)
      } yield result
    }

    /** [[ValueByPosterior]]: at each signal the posterior's maximum, scaled back by the signal's probability. */
    def byPosterior: R[Kernel.Thm] = {
      val a = fresh("a", Numbers)
      val y = fresh("y", Numbers)
      def Q(sv: String) = s"Sum (\\z:num. $P z * $Kt z $sv) (n:num)"
      def X(av: String, sv: String) = s"Sum (\\y:num. $P y * $Kt y $sv * $U $av y) (n:num)"
      def Post(av: String, sv: String) = s"Sum (\\y:num. $P y * $Kt y $sv * inv (${Q(sv)}) * $U $av y) (n:num)"
      val Positive = s"!s:num. s < (m:num) ==> 0 < Sum (\\y:num. $P y * $Kt y s) (n:num)"
      for {
        positive <- assume(Positive)
        original <- unfold(ValueName, "n:num", "m:num", "top:num", P, Kt, U)
        pointwise <- prop(s"!s:num. s < (m:num) ==> Maximum (\\a:num. ${X("a", "s")}) (top:num) = " +
          s"${Q("s")} * Maximum (\\a:num. ${Post("a", "s")}) top")
        each <- every(pointwise) { (ss, shs, _) =>
          val S = v(ss(0))
          val MX = s"Maximum (\\a:num. ${X("a", S)}) (top:num)"
          for {
            qpos <- at(positive, s"$S < (m:num) ==> 0 < ${Q(S)}").flatMap(mp(_, shs(0)))
            qinv <- at(fact("INV_POSITIVE"), s"0 < ${Q(S)} ==> 0 < inv (${Q(S)})").flatMap(mp(_, qpos))
            nonneg <- lin(Seq(qinv), s"(0:real) <= inv (${Q(S)})")
            // the posterior's inner sum is inv q times the original's
            inner <- identity(s"$P (y:num) * $Kt y $S * inv (${Q(S)}) * $U (a:num) y = " +
              s"inv (${Q(S)}) * ($P y * $Kt y $S * $U a y)")
            reshaped <- cong("Sum", y, inner, "(n:num)")
            scaledSum <- at(fact("SUM_SCALE"), s"Sum (\\y:num. inv (${Q(S)}) * ($P y * $Kt y $S * $U (a:num) y)) (n:num) = " +
              s"inv (${Q(S)}) * ${X("a", S)}")
            atA <- trans(reshaped, scaledSum)
            underMax <- cong("Maximum", a, atA, "(top:num)")
            scaledMax <- at(k(MaximumScale), s"0 <= inv (${Q(S)}) ==> " +
              s"Maximum (\\a:num. inv (${Q(S)}) * ${X("a", S)}) (top:num) = inv (${Q(S)}) * $MX").flatMap(mp(_, nonneg))
            post <- trans(underMax, scaledMax)
            nonzero <- at(fact("POSITIVE_NOT_ZERO"), s"0 < ${Q(S)} ==> ~(${Q(S)} = 0)").flatMap(mp(_, qpos))
            cancel <- at(fact("MUL_INVERSE"), s"~(${Q(S)} = 0) ==> ${Q(S)} * inv (${Q(S)}) = 1").flatMap(mp(_, nonzero))
            assoc <- identity(s"${Q(S)} * (inv (${Q(S)}) * $MX) = (${Q(S)} * inv (${Q(S)})) * $MX")
            out <- linAfterText(Seq(post, assoc, cancel), Seq.empty,
              s"$MX = ${Q(S)} * Maximum (\\a:num. ${Post("a", S)}) top")
          } yield out
        }
        collapsed <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!s:num. s < (m:num) ==> Maximum (\\a:num. ${X("a", "s")}) (top:num) = " +
            s"${Q("s")} * Maximum (\\a:num. ${Post("a", "s")}) top) ==> " +
            s"Sum (\\s:num. Maximum (\\a:num. ${X("a", "s")}) top) m = " +
            s"Sum (\\s:num. ${Q("s")} * Maximum (\\a:num. ${Post("a", "s")}) top) m")
          .flatMap(mp(_, each))
        equal <- trans(original, collapsed)
        discharged <- disch(Positive, equal)
        out <- closed(discharged, ValueByPosterior)
      } yield out
    }
  }
}
