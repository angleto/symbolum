package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Rule 30, twice: as a cellular automaton over rows of cells, and as the map
 * `F n = n XOR (2 n OR 4 n)` on the naturals whose orbit from 1 is the rows read as numbers, with a
 * theorem that the two agree. A second instance of the method of
 * `docs/adr/0062`: nothing is declared, every statement is over the equations that characterise
 * its object, and an existence theorem shows those equations can hold. `docs/adr/0064` is the
 * decision, and Mycelium note 917b3939 is the account a reader without the kernel can follow.
 *
 * Not a development: it declares nothing, and `Complex` publishes what it proves.
 *
 * == The rows ==
 *
 * `run x t i` is cell `i` at time `t` from the row `x`, in a frame that moves one cell per step, so
 * that cell `(t + 1, i)` reads cells `i`, `i + 1` and `i + 2` at time `t` and every position is a
 * natural. A cell is read as a sign, `COND b (0 - 1) 1`, under which XOR is a product and the step is
 * a polynomial (`RULE_THIRTY_SIGNED`). The cone and left permutivity are inductions on `t`; the
 * balance pairs the windows that differ in their first cell.
 *
 * == The map ==
 *
 * The library has no bitwise operations, so `F` is given by two equations on halving through
 * `g p q n`, the map with the two bits below `n` given as `p` and `q`: `g p q (2 m)` and
 * `g p q (2 m + 1)` are the low bit of the value plus twice `g` at `m`. Both hold at `m = 0`, which
 * forces `g F F 0 = 0`, so they need no base case. `G_STEP` folds them into one equation, and every
 * fact about the map is an induction on the number of low bits that goes through it.
 * `RULE_THIRTY_MAP_EXISTS` builds `g` with a counter that halves its argument a given number of
 * times and stops changing once two to that number passes the argument.
 *
 * == The Walsh transform ==
 *
 * `WALSH_INVERSION` is stated as `REAL_DFT_INVERSION` is, at a residue modulo `2^k`, with the
 * characters of the bits in place of the roots of unity, and it is proved from orthogonality. The
 * row form of a cell reaches it through a code of the window as a number, which `ENCODE` reads back.
 *
 * == What it does not say ==
 *
 * Nothing here is about the centre column of a single seed beyond what the bridge states: that it
 * is bit `t` of `F^t(1)`. Its periodicity, the frequency of its ones and the cost of computing it
 * are the three open problems of the Rule 30 prize, and the theorems are the structure they are
 * open against: the low bits of `F^t(n)` depend on the low bits of `n`, `F^t` permutes the residues,
 * and the balance holds over all starts rather than along one orbit.
 */
private[theories] object RuleThirty {

  type R[A] = Either[LogicError, A]

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Rows: Type = Type.fun(Numbers, Type.Bool)
  private val Layers: Type = Type.fun(Rows, Type.fun(Numbers, Type.Bool))
  private val Runs: Type = Type.fun(Rows, Type.fun(Numbers, Type.fun(Numbers, Type.Bool)))

  /** `+1` for a cell that is off and `-1` for one that is on: XOR becomes a product. */
  private def sign(b: String): String = s"COND ($b) (0 - 1) (1:real)"

  /** Bit `j` of `y`. */
  private def bit(j: String, y: String): String = s"NUM_MOD (NUM_DIV ($y) (NUM_POW 2 ($j))) 2 = 1"

  /** The Walsh character of the subset `s` of the first `k` positions, at the row `row`. */
  private def character(s: String, row: String => String, k: String): String =
    s"Prod (\\j:num. COND (${bit("j", s)}) (${sign(row("j"))}) 1) ($k)"

  /** The Walsh character of the subset `s` on the first `k` bits of `n`. */
  private def chi(s: String, n: String, k: String): String =
    s"Prod (\\i:num. COND (${bit("i", s)}) (${sign(bit("i", n))}) 1) ($k)"

  private val Run = "(run:(num->bool)->num->num->bool)"

  /** The evolution, by the two equations that characterise it in the skewed frame. */
  private val Rule: String =
    s"(!x:num->bool. !i:num. $Run x 0 i = x i) /\\ " +
      s"(!x:num->bool. !t:num. !i:num. $Run x (SUC t) i = ~($Run x t i = ($Run x t (i + 1) \\/ $Run x t (i + 2))))"

  private val G = "(g:bool->bool->num->num)"
  private val It = "(iterate:num->num->num)"
  private val Steps: Type = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers)))
  private val Iterates: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /**
   * The map `F n = n XOR (2 n OR 4 n)` and its iterate, by the equations that characterise them.
   * `g p q n` is the map with the two bits below `n` given as `p` (just below) and `q`; `F n = g F F n`.
   */
  private val MapEquations: String =
    s"(!p:bool. !q:bool. !m:num. $G p q (2 * m) = COND (p \\/ q) 1 0 + 2 * $G F p m) /\\ " +
      s"(!p:bool. !q:bool. !m:num. $G p q (2 * m + 1) = COND (p \\/ q) 0 1 + 2 * $G T p m) /\\ " +
      s"(!n:num. $It n 0 = n) /\\ (!n:num. !t:num. $It n (SUC t) = $G F F ($It n t))"

  private def overMap(claim: String): String = s"!g:bool->bool->num->num. !iterate:num->num->num. $MapEquations ==> $claim"

  private def over(claim: String): String = s"!run:(num->bool)->num->num->bool. $Rule ==> $claim"

  private val Width = "2 * t + 1"

  private def transform(k: String, value: String => String): String =
    s"Sum (\\y:num. ${value("y")} * ${character("s", j => bit(j, "y"), k)}) (NUM_POW 2 ($k)) / real_of_num (NUM_POW 2 ($k))"

  private val Signed: String =
    s"${sign("~(l = (c \\/ r))")} = ${sign("l")} * (${sign("c")} + ${sign("r")} + ${sign("c")} * ${sign("r")} - 1) / 2"

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "RULE_THIRTY_SIGNED" -> s"!l:bool. !c:bool. !r:bool. $Signed",
    "RULE_THIRTY_EXISTS" -> s"?run:(num->bool)->num->num->bool. $Rule",
    "RULE_THIRTY_SHIFT" -> over(s"!x:num->bool. !t:num. !i:num. !p:num. $Run x t (i + p) = $Run (\\q:num. x (i + q)) t p"),
    "RULE_THIRTY_CONE" -> over(
      s"!t:num. !i:num. !x:num->bool. !y:num->bool. (!j:num. j < $Width ==> x (i + j) = y (i + j)) ==> $Run x t i = $Run y t i"),
    "RULE_THIRTY_LEFT_PERMUTIVE" -> over(
      s"!t:num. !i:num. !x:num->bool. !y:num->bool. (!j:num. 0 < j /\\ j < $Width ==> x (i + j) = y (i + j)) /\\ ~(x i = y i) ==> " +
        s"~($Run x t i = $Run y t i)"),
    "WALSH_INVERSION" ->
      (s"!f:num->real. !k:num. !n:num. f (NUM_MOD n (NUM_POW 2 k)) = " +
        s"Sum (\\s:num. Sum (\\y:num. f y * ${chi("s", "y", "k")}) (NUM_POW 2 k) / real_of_num (NUM_POW 2 k) * ${chi("s", "n", "k")}) (NUM_POW 2 k)"),
    "RULE_THIRTY_WALSH_FORM" -> over(
      s"!t:num. !i:num. !x:num->bool. ${sign(s"$Run x t i")} = Sum (\\s:num. " +
        s"${transform(Width, y => sign(s"$Run (\\p:num. ${bit("p", y)}) t 0"))} * ${character("s", j => s"x (i + $j)", Width)}) (NUM_POW 2 ($Width))"),
    "RULE_THIRTY_BALANCED" -> over(
      s"!t:num. Sum (\\y:num. ${sign(s"$Run (\\p:num. ${bit("p", "y")}) t 0")}) (NUM_POW 2 ($Width)) = 0"),
    "RULE_THIRTY_MAP_RESIDUES" -> overMap(
      s"!t:num. !k:num. !n:num. NUM_MOD ($It n t) (NUM_POW 2 k) = NUM_MOD ($It (NUM_MOD n (NUM_POW 2 k)) t) (NUM_POW 2 k)"),
    "RULE_THIRTY_MAP_INJECTIVE" -> overMap(
      s"!t:num. !k:num. !m:num. !n:num. NUM_MOD ($It m t) (NUM_POW 2 k) = NUM_MOD ($It n t) (NUM_POW 2 k) ==> NUM_MOD m (NUM_POW 2 k) = NUM_MOD n (NUM_POW 2 k)"),
    "RULE_THIRTY_MAP_EXISTS" -> s"?g:bool->bool->num->num. ?iterate:num->num->num. $MapEquations",
    "RULE_THIRTY_BRIDGE" ->
      (s"!run:(num->bool)->num->num->bool. !g:bool->bool->num->num. !iterate:num->num->num. $Rule ==> $MapEquations ==> " +
        s"!t:num. !k:num. !n:num. !i:num. !j:num. i + j = k ==> " +
        s"$Run (\\p:num. p <= k /\\ (${bit("NUM_SUB k p", "n")})) t i = (${bit("j", s"$It n t")})"),
    "RULE_THIRTY_MAP_ROW_LENGTH" -> overMap(s"!t:num. NUM_POW 2 (2 * t) <= $It 1 t /\\ $It 1 t < NUM_POW 2 (2 * t + 1)"),
    "RULE_THIRTY_MAP_BALANCED" -> overMap(
      s"!t:num. !j:num. Sum (\\n:num. ${sign(bit("j", s"$It n t"))}) (NUM_POW 2 (SUC j)) = 0"),
    "RULE_THIRTY_MAP_WALSH_FORM" -> overMap(
      s"!t:num. !j:num. !n:num. ${sign(bit("j", s"$It n t"))} = Sum (\\s:num. " +
        s"Sum (\\y:num. ${sign(bit("j", s"$It y t"))} * ${chi("s", "y", "SUC j")}) (NUM_POW 2 (SUC j)) / real_of_num (NUM_POW 2 (SUC j)) * " +
        s"${chi("s", "n", "SUC j")}) (NUM_POW 2 (SUC j))")
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "BOOL_EQ_IMP" -> (_.steps.eqImpTheorem),
    "RULE_THIRTY_SIGNED" -> (_.signed),
    "RULE_THIRTY_EXISTS" -> (_.exists),
    "RULE_THIRTY_SHIFT" -> (_.shift),
    "RULE_THIRTY_CONE" -> (_.cone),
    "RULE_THIRTY_LEFT_PERMUTIVE" -> (_.permutive),
    "MOD_TWO_SHIFT" -> (_.modTwoShift),
    "BIT_SHIFT" -> (_.bitShift),
    "BIT_ABOVE" -> (_.bitAbove),
    "BIT_TOP" -> (_.bitTop),
    "BIT_BELOW_TOP" -> (_.bitBelowTop),
    "BIT_OF_MOD" -> (_.bitOfMod),
    "BIT_HALVE" -> (_.bitHalve),
    "PROD_CONGRUENCE_BELOW" -> (_.prodCongruenceBelow),
    "MOD_SPLIT" -> (_.modSplit),
    "MOD_EQ_SPLIT" -> (_.modEqSplit),
    "CHI_TOP_SHIFT" -> (_.chiTopShift),
    "WALSH_ORTHOGONAL" -> (_.orthogonal),
    "PICK" -> (_.pick),
    "WALSH_INVERSION" -> (_.walshInversion),
    "ENCODE" -> (_.encode),
    "RULE_THIRTY_WALSH_FORM" -> (_.walshFormRows),
    "RULE_THIRTY_BALANCED" -> (_.balancedRows),
    "COND_BELOW_TWO" -> (_.condBelowTwo),
    "MOD_ONE" -> (_.modOne),
    "MOD_MOD" -> (_.modMod),
    "MOD_DOUBLE" -> (_.modDouble),
    "DIV_MOD_SHIFT" -> (_.divModShift),
    "G_STEP" -> (_.gStep),
    "G_RESIDUES" -> (_.gResidues),
    "RULE_THIRTY_MAP_RESIDUES" -> (_.mapResidues),
    "G_INJECTIVE" -> (_.gInjective),
    "RULE_THIRTY_MAP_INJECTIVE" -> (_.mapInjective),
    "NUM_NOT_LE" -> (_.steps.notLeTheorem),
    "G_ZERO" -> (_.gZero),
    "G_LENGTH" -> (_.gLength),
    "RULE_THIRTY_MAP_ROW_LENGTH" -> (_.mapRowLength),
    "RULE_THIRTY_MAP_BALANCED" -> (_.mapBalanced),
    "RULE_THIRTY_MAP_WALSH_FORM" -> (_.mapWalshForm),
    "BELOW_POWER" -> (_.belowPower),
    "RULE_THIRTY_MAP_EXISTS" -> (_.mapExists),
    "DIV_ONE" -> (_.divOne),
    "BIT_LOW" -> (_.bitLow),
    "G_BIT_ZERO" -> (_.gBitZero),
    "G_BIT_SUC" -> (_.gBitSuc),
    "G_BIT_RULE" -> (_.gBitRule),
    "ZERO_ROW" -> (_.zeroRow),
    "RULE_THIRTY_BRIDGE" -> (_.bridge)
  )

  /** The facts [[Statements]] names, derived with `kit`. */
  def prove(kit: ComplexKit, semiring: Semiring, recursion: Kernel.Thm, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] = {
    val steps = new NumberSteps(kit, semiring)
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, steps, recursion, known))
  }

  private[theories] final class Proofs(val kit: ComplexKit, val steps: NumberSteps, recursion: Kernel.Thm, known: Map[String, Kernel.Thm]) {
    import kit.*
    import steps.*

    def k(name: String): Kernel.Thm = known(name)


    private val run = Term.variable("run", Runs)
    private val t = Term.variable("t", Numbers)
    private val i = Term.variable("i", Numbers)
    private val p = Term.variable("p", Numbers)
    private val j = Term.variable("j", Numbers)
    private val x = Term.variable("x", Rows)
    private val y = Term.variable("y", Rows)

    private val X = "(x:num->bool)"
    private val Y = "(y:num->bool)"

    /** The two equations of the evolution, assumed, and what `body` proves from them discharged. */
    private def rule(body: Vector[Kernel.Thm] => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        hT <- prop(Rule)
        h <- LogicError.lift(Kernel.assume(hT))
        hs <- split(h)
        proved <- body(hs)
        out <- rules.disch(hT, proved).flatMap(gen(_, run))
      } yield out

    /** A published fact about the evolution, at the evolution assumed. */
    private def under(name: String): R[Kernel.Thm] =
      for {
        hT <- prop(Rule)
        h <- LogicError.lift(Kernel.assume(hT))
        out <- spec(k(name), run).flatMap(mp(_, h))
      } yield out

    /** `COND b (0 - 1) 1 = 0 - 1` or `= 1`, whichever `literals` decide. */
    private def signOf(b: Term, literals: Seq[Kernel.Thm]): R[Kernel.Thm] =
      tauto(literals, b) match {
        case Right(holds) =>
          for {
            target <- prop(s"(b:bool) ==> ${sign("b")} = 0 - 1").flatMap(substituteBool(b, _))
            out <- fact("COND_TRUE").map(atReals).flatMap(rules.specToReduced(_, target)).flatMap(mp(_, holds))
          } yield out
        case Left(_) =>
          for {
            nb <- logic.mkNot(b)
            refuted <- tauto(literals, nb)
            target <- prop(s"~(b:bool) ==> ${sign("b")} = 1").flatMap(substituteBool(b, _))
            out <- fact("COND_FALSE").map(atReals).flatMap(rules.specToReduced(_, target)).flatMap(mp(_, refuted))
          } yield out
      }

    private def substituteBool(b: Term, template: Term): R[Term] = substitute(Map(Term.variable("b", Type.Bool) -> b), template)

    /** The step in signs, by the eight cases of the three cells and arithmetic on numerals. */
    def signed: R[Kernel.Thm] = {
      val l = Term.variable("l", Type.Bool)
      val c = Term.variable("c", Type.Bool)
      val r = Term.variable("r", Type.Bool)
      for {
        body <- prop(Signed)
        xor <- prop("~((l:bool) = ((c:bool) \\/ (r:bool)))")
        leaf = (literals: Seq[Kernel.Thm]) =>
          for {
            values <- Seq(xor, l, c, r).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, b) =>
              for { done <- acc; e <- signOf(b, literals) } yield done :+ e)
            out <- rewriting(values, body)(driver.identity)
          } yield out
        out <- cases("l:bool")(
          la => cases("c:bool")(ca => cases("r:bool")(ra => leaf(Seq(la, ca, ra)), ra => leaf(Seq(la, ca, ra))),
            ca => cases("r:bool")(ra => leaf(Seq(la, ca, ra)), ra => leaf(Seq(la, ca, ra)))),
          la => cases("c:bool")(ca => cases("r:bool")(ra => leaf(Seq(la, ca, ra)), ra => leaf(Seq(la, ca, ra))),
            ca => cases("r:bool")(ra => leaf(Seq(la, ca, ra)), ra => leaf(Seq(la, ca, ra)))))
        general <- gen(out, l, c, r)
      } yield general
    }

    /* ------------------------------------------------------------ the evolution */

    /** An evolution exists for every row: by the recursion theorem at the type of a layer. */
    def exists: R[Kernel.Thm] = {
      val Stepper = "\\g:(num->bool)->num->bool. \\t:num. \\x:num->bool. \\i:num. ~(g x i = (g x (i + 1) \\/ g x (i + 2)))"
      val Fn = "(fn:num->(num->bool)->num->bool)"
      for {
        recursive <- Right(Kernel.instType(Map("a" -> Layers), recursion))
        start <- term("\\x:num->bool. \\i:num. x i", Layers)
        stepper <- term(Stepper, Type.fun(Layers, Type.fun(Numbers, Layers)))
        made <- spec(recursive, start, stepper)
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            runTerm <- term(s"\\x:num->bool. \\t:num. \\i:num. $Fn t x i", Runs)
            atZero <- for {
              applied <- Conv.apThm(parts(0), x).flatMap(Conv.apThm(_, i)).flatMap(beta)
              out <- gen(applied, x, i)
            } yield out
            atSuc <- for {
              opened <- spec(parts(1), t)
              applied <- Conv.apThm(opened, x).flatMap(Conv.apThm(_, i)).flatMap(beta)
              out <- gen(applied, x, t, i)
            } yield out
            both <- conj(atZero, atSuc)
            predicate <- prop(StatementsMap("RULE_THIRTY_EXISTS")).flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))
            out <- introduce(predicate, runTerm, both)
          } yield out
        }
      } yield out
    }

    /** The evolution commutes with a translation of the row. */
    def shift: R[Kernel.Thm] =
      rule { hs =>
        val Moved = s"(\\q:num. $X (${v("i")} + q))"
        for {
          body <- prop(s"!x:num->bool. !i:num. !p:num. $Run x (t:num) (i + p) = $Run (\\q:num. x (i + q)) t p")
          proved <- induct(t, body)(
            _ =>
              for {
                goal <- prop(s"$Run $X 0 (${v("i")} + ${v("p")}) = $Run $Moved 0 ${v("p")}")
                out <- rewriting(Seq(hs(0)), goal)(byBeta).flatMap(gen(_, x, i, p))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name)
              def stepAt(row: String, pos: String) =
                at(hs(1), s"$Run $row (SUC $K) ($pos) = ~($Run $row $K ($pos) = ($Run $row $K ($pos + 1) \\/ $Run $row $K ($pos + 2)))")
              def ih(offset: String) =
                at(hyp, s"$Run $X $K (${v("i")} + ($offset)) = $Run $Moved $K ($offset)")
              for {
                left <- stepAt(X, s"${v("i")} + ${v("p")}")
                right <- stepAt(Moved, v("p"))
                one <- num(s"${v("i")} + ${v("p")} + 1 = ${v("i")} + (${v("p")} + 1)")
                two <- num(s"${v("i")} + ${v("p")} + 2 = ${v("i")} + (${v("p")} + 2)")
                i0 <- ih(v("p"))
                i1 <- ih(s"${v("p")} + 1")
                i2 <- ih(s"${v("p")} + 2")
                goal <- prop(s"$Run $X (SUC $K) (${v("i")} + ${v("p")}) = $Run $Moved (SUC $K) ${v("p")}")
                out <- rewriting(Seq(left, right, one, two, i0, i1, i2), goal)(byBeta).flatMap(gen(_, x, i, p))
              } yield out
            }
          )
          out <- spec(proved, t, x, i, p).flatMap(gen(_, x, t, i, p))
        } yield out
      }

    /** For an offset `d`, the window at `i + d` of length `2 t + 1` read off the window at `i` of length `2 (SUC t) + 1`. */
    private def window(wide: Kernel.Thm, K: String, d: Int, condition: Option[String]): R[Kernel.Thm] = {
      val I = v("i"); val J = v("j")
            val index = if (d == 0) J else s"$J + $d"
      val guard = condition.getOrElse(s"$J < 2 * $K + 1")
      val wideGuard = condition match {
        case None => s"$index < 2 * SUC $K + 1"
        case Some(_) => s"0 < $index /\\ $index < 2 * SUC $K + 1"
      }
      for {
        held <- assumed(guard)
        (guardT, guardHeld) = held
        wider <- numLinText(Seq(guardHeld), wideGuard)
        inst <- at(wide, s"$wideGuard ==> $X ($I + ($index)) = $Y ($I + ($index))")
        agreed <- mp(inst, wider)
        moved <-
          if (d == 0) Right(agreed)
          else num(s"$I + ($J + $d) = $I + $d + $J").flatMap(rw(_, agreed))
        out <- rules.disch(guardT, moved).flatMap(gen(_, j))
      } yield out
    }

    /** Two rows that agree on the `2 t + 1` cells from `i` give the same cell `(t, i)`. */
    def cone: R[Kernel.Thm] =
      rule { hs =>
        val I = v("i")
        for {
          body <- prop(s"!i:num. !x:num->bool. !y:num->bool. (!j:num. j < 2 * (t:num) + 1 ==> x (i + j) = y (i + j)) ==> $Run x t i = $Run y t i")
          proved <- induct(t, body)(
            _ =>
              for {
                held <- assumed(s"!j:num. j < 2 * 0 + 1 ==> $X ($I + j) = $Y ($I + j)")
                (hT, h) = held
                first <- numLinText(Seq.empty, "(0:num) < 2 * 0 + 1")
                atZero <- at(h, s"(0:num) < 2 * 0 + 1 ==> $X ($I + 0) = $Y ($I + 0)").flatMap(mp(_, first))
                agreed <- fact("NUM_ADD_ZERO").flatMap(rw(_, atZero))
                ex <- at(hs(0), s"$Run $X 0 $I = $X $I")
                ey <- at(hs(0), s"$Run $Y 0 $I = $Y $I").flatMap(Conv.sym)
                joined <- trans(ex, agreed, ey)
                out <- rules.disch(hT, joined).flatMap(gen(_, i, x, y))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name)
              def stepOf(row: String) =
                at(hs(1), s"$Run $row (SUC $K) $I = ~($Run $row $K $I = ($Run $row $K ($I + 1) \\/ $Run $row $K ($I + 2)))")
              for {
                held <- assumed(s"!j:num. j < 2 * SUC $K + 1 ==> $X ($I + j) = $Y ($I + j)")
                (hT, h) = held
                agree <- (0 to 2).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, d) =>
                  val at_ = if (d == 0) I else s"$I + $d"
                  for {
                    done <- acc
                    w <- window(h, K, d, None)
                    ih <- at(hyp, s"(!j:num. j < 2 * $K + 1 ==> $X ($at_ + j) = $Y ($at_ + j)) ==> $Run $X $K ($at_) = $Run $Y $K ($at_)")
                    e <- mp(ih, w)
                  } yield done :+ e
                }
                sx <- stepOf(X)
                sy <- stepOf(Y)
                goal <- prop(s"$Run $X (SUC $K) $I = $Run $Y (SUC $K) $I")
                closed <- rewriting(Seq(sx, sy) ++ agree, goal)(byBeta)
                out <- rules.disch(hT, closed).flatMap(gen(_, i, x, y))
              } yield out
            }
          )
        } yield proved
      }

    /** Two rows that differ at `i` and agree on the `2 t` cells to its right differ at `(t, i)`. */
    def permutive: R[Kernel.Thm] =
      rule { hs =>
        val I = v("i")
        val Guard = s"0 < ${v("j")} /\\ ${v("j")} < 2 * "
        for {
          coneHere <- under("RULE_THIRTY_CONE")
          body <- prop(s"!i:num. !x:num->bool. !y:num->bool. (!j:num. 0 < j /\\ j < 2 * (t:num) + 1 ==> x (i + j) = y (i + j)) /\\ ~(x i = y i) ==> " +
            s"~($Run x t i = $Run y t i)")
          proved <- induct(t, body)(
            _ =>
              for {
                held <- assumed(s"(!j:num. 0 < j /\\ j < 2 * 0 + 1 ==> $X ($I + j) = $Y ($I + j)) /\\ ~($X $I = $Y $I)")
                (hT, h) = held
                differ <- rules.conjElim2(h)
                ex <- at(hs(0), s"$Run $X 0 $I = $X $I")
                ey <- at(hs(0), s"$Run $Y 0 $I = $Y $I")
                goal <- prop(s"~($Run $X 0 $I = $Run $Y 0 $I)")
                closed <- rewriting(Seq(ex, ey), goal)(g => if (g == differ.conclusion) Right(differ) else Left(NotOfForm("the difference at i", g)))
                out <- rules.disch(hT, closed).flatMap(gen(_, i, x, y))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name)
              def stepOf(row: String) =
                at(hs(1), s"$Run $row (SUC $K) $I = ~($Run $row $K $I = ($Run $row $K ($I + 1) \\/ $Run $row $K ($I + 2)))")
              for {
                held <- assumed(s"(!j:num. 0 < j /\\ j < 2 * SUC $K + 1 ==> $X ($I + j) = $Y ($I + j)) /\\ ~($X $I = $Y $I)")
                (hT, h) = held
                wide <- rules.conjElim1(h)
                differ <- rules.conjElim2(h)
                narrow <- for {
                  g <- assumed(s"0 < ${v("j")} /\\ ${v("j")} < 2 * $K + 1")
                  (gT, gh) = g
                  wider <- numLinText(Seq(gh), s"0 < ${v("j")} /\\ ${v("j")} < 2 * SUC $K + 1")
                  inst <- at(wide, s"0 < ${v("j")} /\\ ${v("j")} < 2 * SUC $K + 1 ==> $X ($I + ${v("j")}) = $Y ($I + ${v("j")})")
                  out <- mp(inst, wider).flatMap(rules.disch(gT, _)).flatMap(gen(_, j))
                } yield out
                ihAt <- at(hyp, s"(!j:num. 0 < j /\\ j < 2 * $K + 1 ==> $X ($I + j) = $Y ($I + j)) /\\ ~($X $I = $Y $I) ==> ~($Run $X $K $I = $Run $Y $K $I)")
                apart <- conj(narrow, differ).flatMap(mp(ihAt, _))
                right <- (1 to 2).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, d) =>
                  for {
                    done <- acc
                    w <- window(wide, K, d, Some(s"${v("j")} < 2 * $K + 1"))
                    c <- at(coneHere, s"(!j:num. j < 2 * $K + 1 ==> $X ($I + $d + j) = $Y ($I + $d + j)) ==> $Run $X $K ($I + $d) = $Run $Y $K ($I + $d)")
                    e <- mp(c, w)
                  } yield done :+ e
                }
                sx <- stepOf(X)
                sy <- stepOf(Y)
                goal <- prop(s"~($Run $X (SUC $K) $I = $Run $Y (SUC $K) $I)")
                closed <- rewriting(Seq(sx, sy) ++ right, goal)(g => tauto(Seq(apart), g))
                out <- rules.disch(hT, closed).flatMap(gen(_, i, x, y))
              } yield out
            }
          )
        } yield proved
      }

    /** `NUM_MOD (2 * a + q) 2 = NUM_MOD q 2`. */
    def modTwoShift: R[Kernel.Thm] = {
      val a = Term.variable("a", Numbers)
      val q = Term.variable("q", Numbers)
      for {
        dm <- at(fact("NUM_DIV_MOD"), "2 * NUM_DIV (q:num) 2 + NUM_MOD q 2 = q")
        regroup <- num("2 * (a:num) + (2 * NUM_DIV (q:num) 2 + NUM_MOD q 2) = 2 * (a + NUM_DIV q 2) + NUM_MOD q 2")
        split_ <- rw(dm, regroup)
        below <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), "(0:num) < 2 ==> NUM_MOD (q:num) 2 < 2").flatMap(mp(_, t2)))
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          "2 * (a:num) + (q:num) = 2 * (a + NUM_DIV q 2) + NUM_MOD q 2 /\\ NUM_MOD q 2 < 2 ==> " +
            "a + NUM_DIV q 2 = NUM_DIV (2 * a + q) 2 /\\ NUM_MOD q 2 = NUM_MOD (2 * a + q) 2")
        parts <- conj(split_, below).flatMap(mp(unique, _)).flatMap(split)
        out <- Conv.sym(parts(1)).flatMap(gen(_, a, q))
      } yield out
    }

    /** Bit `j` does not see a multiple of `2^(j + SUC d)`. */
    def bitShift: R[Kernel.Thm] = {
      val d = Term.variable("d", Numbers)
      val q = Term.variable("q", Numbers)
      val r = Term.variable("r", Numbers)
      val P = "NUM_POW 2 (j:num)"
      val D = s"NUM_DIV (r:num) ($P)"
      val M = s"NUM_MOD (r:num) ($P)"
      val K = s"2 * (NUM_POW 2 (d:num) * (q:num)) + $D"
      for {
        dm <- at(fact("NUM_DIV_MOD"), s"$P * $D + $M = r")
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $P").flatMap(mp(_, t2)))
        below <- at(fact("NUM_MOD_LT"), s"0 < $P ==> $M < $P").flatMap(mp(_, positive))
        powAdd <- at(fact("NUM_POW_ADD"), "NUM_POW 2 ((j:num) + SUC (d:num)) = NUM_POW 2 j * NUM_POW 2 (SUC d)").flatMap(Conv.sym)
        powSuc <- at(fact("NUM_POW_SUC"), "NUM_POW 2 (SUC (d:num)) = NUM_POW 2 d * 2").flatMap(Conv.sym)
        regroup <- num(s"$P * (NUM_POW 2 (d:num) * 2) * (q:num) + ($P * $D + $M) = $P * ($K) + $M")
        split_ <- rw(dm, regroup).flatMap(rw(powSuc, _)).flatMap(rw(powAdd, _))
        n = s"NUM_POW 2 ((j:num) + SUC (d:num)) * (q:num) + (r:num)"
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"$n = $P * ($K) + $M /\\ $M < $P ==> $K = NUM_DIV ($n) ($P) /\\ $M = NUM_MOD ($n) ($P)")
        quotient <- conj(split_, below).flatMap(mp(unique, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
        shifted <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD ($K) 2 = NUM_MOD ($D) 2")
        goal <- prop(s"(${bit("j:num", n)}) = (${bit("j:num", "r:num")})")
        out <- rewriting(Seq(quotient, shifted), goal)(byBeta).flatMap(gen(_, Term.variable("j", Numbers), d, q, r))
      } yield out
    }

    /** Below `2^k`, bit `k` is off. */
    def bitAbove: R[Kernel.Thm] = {
      val kv = Term.variable("k", Numbers)
      val c = Term.variable("c", Numbers)
      for {
        held <- assumed("(c:num) < NUM_POW 2 (k:num)")
        (belowT, below) = held
        zero <- at(fact("NUM_DIV_MOD_BELOW"), "(c:num) < NUM_POW 2 (k:num) ==> NUM_DIV c (NUM_POW 2 k) = 0 /\\ NUM_MOD c (NUM_POW 2 k) = c")
          .flatMap(mp(_, below)).flatMap(rules.conjElim1)
        modZero <- two.flatMap(t2 => at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)))
          .flatMap(rules.conjElim2)
        apart <- zeroNotOne
        goal <- prop(s"~(${bit("k:num", "c:num")})")
        closed <- rewriting(Seq(zero, modZero), goal)(landsOn(apart))
        out <- rules.disch(belowT, closed).flatMap(gen(_, kv, c))
      } yield out
    }

    /** `2^k + c` has bit `k` on, for `c` below `2^k`. */
    def bitTop: R[Kernel.Thm] = {
      val kv = Term.variable("k", Numbers)
      val c = Term.variable("c", Numbers)
      for {
        held <- assumed("(c:num) < NUM_POW 2 (k:num)")
        (belowT, below) = held
        step <- at(fact("NUM_DIV_MOD_STEP"),
          "(c:num) < NUM_POW 2 (k:num) ==> NUM_DIV (NUM_POW 2 k + c) (NUM_POW 2 k) = SUC 0 /\\ NUM_MOD (NUM_POW 2 k + c) (NUM_POW 2 k) = c")
          .flatMap(mp(_, below)).flatMap(rules.conjElim1)
        oneBelow <- numLinText(Seq.empty, "SUC 0 < 2")
        modOne <- at(fact("NUM_DIV_MOD_BELOW"), "SUC 0 < 2 ==> NUM_DIV (SUC 0) 2 = 0 /\\ NUM_MOD (SUC 0) 2 = SUC 0")
          .flatMap(mp(_, oneBelow)).flatMap(rules.conjElim2)
        one <- fact("NUM_ONE_SUC").flatMap(Conv.sym)
        goal <- prop(bit("k:num", "NUM_POW 2 (k:num) + (c:num)"))
        closed <- rewriting(Seq(step, modOne), goal)(landsOn(one))
        out <- rules.disch(belowT, closed).flatMap(gen(_, kv, c))
      } yield out
    }

    /** `k = j + SUC (k - SUC j)` from `j < k`. */
    private def gap(below: Kernel.Thm, J: String, K: String): R[Kernel.Thm] =
      for {
        le <- numLinText(Seq(below), s"SUC $J <= $K")
        sub <- at(fact("NUM_REAL_SUB"), s"SUC $J <= $K ==> real_of_num (NUM_SUB $K (SUC $J)) = real_of_num $K - real_of_num (SUC $J)").flatMap(mp(_, le))
        out <- numLinText(Seq(sub), s"$K = $J + SUC (NUM_SUB $K (SUC $J))")
      } yield out

    /** Below position `k`, the bits of `2^k + c` are those of `c`. */
    def bitBelowTop: R[Kernel.Thm] = {
      val (jv, kv, c) = (Term.variable("j", Numbers), Term.variable("k", Numbers), Term.variable("c", Numbers))
      val J = "(j:num)"; val K = "(k:num)"
      for {
        held <- assumed(s"$J < $K")
        (belowT, below) = held
        apart <- gap(below, J, K).flatMap(Conv.sym)
        shifted <- at(k("BIT_SHIFT"), s"(${bit(J, s"NUM_POW 2 ($J + SUC (NUM_SUB $K (SUC $J))) * 1 + (c:num)")}) = (${bit(J, "c:num")})")
        one <- num(s"NUM_POW 2 $K * 1 + (c:num) = NUM_POW 2 $K + c")
        moved <- rw(apart, shifted).flatMap(rw(one, _))
        out <- rules.disch(belowT, moved).flatMap(gen(_, jv, kv, c))
      } yield out
    }

    /** Below position `k`, the bits of `n mod 2^k` are those of `n`. */
    def bitOfMod: R[Kernel.Thm] = {
      val (jv, kv, nv) = (Term.variable("j", Numbers), Term.variable("k", Numbers), Term.variable("n", Numbers))
      val J = "(j:num)"; val K = "(k:num)"; val N = "(n:num)"
      val Q = s"NUM_DIV $N (NUM_POW 2 $K)"; val Rm = s"NUM_MOD $N (NUM_POW 2 $K)"
      for {
        held <- assumed(s"$J < $K")
        (belowT, below) = held
        apart <- gap(below, J, K).flatMap(Conv.sym)
        shifted <- at(k("BIT_SHIFT"), s"(${bit(J, s"NUM_POW 2 ($J + SUC (NUM_SUB $K (SUC $J))) * $Q + $Rm")}) = (${bit(J, Rm)})")
        dm <- at(fact("NUM_DIV_MOD"), s"NUM_POW 2 $K * $Q + $Rm = $N")
        moved <- rw(apart, shifted).flatMap(rw(dm, _)).flatMap(Conv.sym)
        out <- rules.disch(belowT, moved).flatMap(gen(_, jv, kv, nv))
      } yield out
    }

    /** Halving moves every bit down by one: `bit (SUC q) (2 m + e) = bit q m` for `e < 2`. */
    def bitHalve: R[Kernel.Thm] = {
      val (qv, mv, ev) = (Term.variable("q", Numbers), Term.variable("m", Numbers), Term.variable("e", Numbers))
      val P = "NUM_POW 2 (q:num)"
      val D = s"NUM_DIV (m:num) ($P)"; val M = s"NUM_MOD (m:num) ($P)"
      val n = "2 * (m:num) + (e:num)"
      for {
        held <- assumed("(e:num) < 2")
        (smallT, small) = held
        dm <- at(fact("NUM_DIV_MOD"), s"$P * $D + $M = m")
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $P").flatMap(mp(_, t2)))
        below <- at(fact("NUM_MOD_LT"), s"0 < $P ==> $M < $P").flatMap(mp(_, positive))
        powSuc <- at(fact("NUM_POW_SUC"), "NUM_POW 2 (SUC (q:num)) = NUM_POW 2 q * 2").flatMap(Conv.sym)
        regroup <- num(s"2 * ($P * $D + $M) + (e:num) = $P * 2 * $D + (2 * $M + e)")
        split_ <- rw(dm, regroup).flatMap(rw(powSuc, _))
        remainder <- numLinText(Seq(below, small), s"2 * $M + (e:num) < $P * 2").flatMap(rw(powSuc, _))
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"$n = NUM_POW 2 (SUC q) * $D + (2 * $M + e) /\\ 2 * $M + e < NUM_POW 2 (SUC q) ==> " +
            s"$D = NUM_DIV ($n) (NUM_POW 2 (SUC q)) /\\ 2 * $M + e = NUM_MOD ($n) (NUM_POW 2 (SUC q))")
        quotient <- conj(split_, remainder).flatMap(mp(unique, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
        goal <- prop(s"(${bit("SUC (q:num)", n)}) = (${bit("q:num", "m:num")})")
        closed <- rewriting(Seq(quotient), goal)(byBeta)
        out <- rules.disch(smallT, closed).flatMap(gen(_, qv, mv, ev))
      } yield out
    }

    /** Two real products over `n` factors agree when the factors below `n` do. */
    def prodCongruenceBelow: R[Kernel.Thm] = {
      val f = Term.variable("f", Type.fun(Numbers, Reals))
      val g = Term.variable("g", Type.fun(Numbers, Reals))
      val nv = Term.variable("n", Numbers)
      for {
        body <- prop("(!m:num. m < (n:num) ==> (f:num->real) m = (g:num->real) m) ==> Prod f n = Prod g n")
        proved <- induct(nv, body)(
          _ =>
            for {
              held <- assumed("!m:num. m < 0 ==> (f:num->real) m = (g:num->real) m")
              (hT, _) = held
              zf <- at(fact("PROD_ZERO"), "Prod (f:num->real) 0 = 1")
              zg <- at(fact("PROD_ZERO"), "Prod (g:num->real) 0 = 1").flatMap(Conv.sym)
              out <- trans(zf, zg).flatMap(rules.disch(hT, _))
            } yield out,
          (kk, hyp, _) => {
            val K = v(kk.name)
            for {
              held <- assumed(s"!m:num. m < SUC $K ==> (f:num->real) m = (g:num->real) m")
              (hT, h) = held
              lower <- for {
                g0 <- assumed(s"${v("m")} < $K")
                (gT, gh) = g0
                wider <- numLinText(Seq(gh), s"${v("m")} < SUC $K")
                out <- at(h, s"${v("m")} < SUC $K ==> (f:num->real) ${v("m")} = (g:num->real) ${v("m")}").flatMap(mp(_, wider))
                  .flatMap(rules.disch(gT, _)).flatMap(gen(_, Term.variable("m", Numbers)))
              } yield out
              ih <- mp(hyp, lower)
              last <- numLinText(Seq.empty, s"$K < SUC $K").flatMap(lt => at(h, s"$K < SUC $K ==> (f:num->real) $K = (g:num->real) $K").flatMap(mp(_, lt)))
              sf <- at(fact("PROD_SUC"), s"Prod (f:num->real) (SUC $K) = Prod f $K * f $K")
              sg <- at(fact("PROD_SUC"), s"Prod (g:num->real) (SUC $K) = Prod g $K * g $K")
              goal <- prop(s"Prod (f:num->real) (SUC $K) = Prod (g:num->real) (SUC $K)")
              closed <- rewriting(Seq(sf, sg, ih, last), goal)(byBeta)
              out <- rules.disch(hT, closed)
            } yield out
          }
        )
        out <- gen(proved, f, g)
      } yield out
    }

    /** The remainder modulo `2^(SUC k)` is the remainder modulo `2^k` plus bit `k` in its place. */
    def modSplit: R[Kernel.Thm] = {
      val yv = Term.variable("y", Numbers); val kv = Term.variable("k", Numbers)
      val M = "NUM_POW 2 (k:num)"; val Q = s"NUM_DIV (y:num) ($M)"; val Rr = s"NUM_MOD (y:num) ($M)"
      val B = s"NUM_MOD ($Q) 2"; val Q2 = s"NUM_DIV ($Q) 2"; val P2 = "NUM_POW 2 (SUC (k:num))"
      for {
        dm1 <- at(fact("NUM_DIV_MOD"), s"$M * $Q + $Rr = y")
        dm2 <- at(fact("NUM_DIV_MOD"), s"2 * $Q2 + $B = $Q")
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
        rLt <- at(fact("NUM_MOD_LT"), s"0 < $M ==> $Rr < $M").flatMap(mp(_, positive))
        bLt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $B < 2").flatMap(mp(_, t2)))
        powSuc <- at(fact("NUM_POW_SUC"), s"$P2 = $M * 2")
        regroup <- num(s"$M * (2 * $Q2 + $B) + $Rr = $M * 2 * $Q2 + ($Rr + $M * $B)")
        split_ <- rw(dm2, regroup).flatMap(rw(dm1, _)).flatMap(e => Conv.sym(powSuc).flatMap(rw(_, e)))
        goalT <- prop(s"$Rr + $M * $B < $P2")
        mulZero <- at(fact("NUM_MUL_ZERO"), s"$M * 0 = 0")
        mulOne <- num(s"$M * 1 = $M")
        bound <- for {
          either <- binary(B, bLt)
          zero <- for {
            h <- assumed(s"$B = 0")
            out <- rewriting(Seq(h._2, mulZero), goalT)(numLin(Seq(rLt, powSuc), _))
          } yield out
          unit <- for {
            h <- assumed(s"$B = 1")
            out <- rewriting(Seq(h._2, mulOne), goalT)(numLin(Seq(rLt, powSuc), _))
          } yield out
          out <- rules.disjElim(either, zero, unit)
        } yield out
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"y = $P2 * $Q2 + ($Rr + $M * $B) /\\ $Rr + $M * $B < $P2 ==> $Q2 = NUM_DIV y ($P2) /\\ $Rr + $M * $B = NUM_MOD y ($P2)")
        out <- conj(split_, bound).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym).flatMap(gen(_, yv, kv))
      } yield out
    }

    /** Two numbers agree modulo `2^(SUC k)` exactly when they agree modulo `2^k` and at bit `k`. */
    def modEqSplit: R[Kernel.Thm] = {
      val (yv, nv, kv) = (Term.variable("y", Numbers), Term.variable("n", Numbers), Term.variable("k", Numbers))
      val M = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
      def Rr(z: String) = s"NUM_MOD ($z:num) ($M)"
      def B(z: String) = s"NUM_MOD (NUM_DIV ($z:num) ($M)) 2"
      val E = s"NUM_MOD (y:num) ($P2) = NUM_MOD (n:num) ($P2)"
      val C = s"${Rr("y")} = ${Rr("n")} /\\ ((${B("y")} = 1) = (${B("n")} = 1))"
      for {
        sy <- at(k("MOD_SPLIT"), s"NUM_MOD (y:num) ($P2) = ${Rr("y")} + $M * ${B("y")}")
        sn <- at(k("MOD_SPLIT"), s"NUM_MOD (n:num) ($P2) = ${Rr("n")} + $M * ${B("n")}")
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
        lowY <- at(fact("NUM_MOD_LT"), s"0 < $M ==> ${Rr("y")} < $M").flatMap(mp(_, positive))
        lowN <- at(fact("NUM_MOD_LT"), s"0 < $M ==> ${Rr("n")} < $M").flatMap(mp(_, positive))
        bY <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> ${B("y")} < 2").flatMap(mp(_, t2)))
        bN <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> ${B("n")} < 2").flatMap(mp(_, t2)))
        forward <- for {
          h <- assumed(E)
          sums <- rw(sy, h._2).flatMap(rw(sn, _))
          swapY <- num(s"${Rr("y")} + $M * ${B("y")} = $M * ${B("y")} + ${Rr("y")}")
          swapN <- num(s"${Rr("n")} + $M * ${B("n")} = $M * ${B("n")} + ${Rr("n")}")
          ordered <- rw(swapY, sums).flatMap(rw(swapN, _))
          unique <- at(fact("NUM_DIVISION_UNIQUE"),
            s"$M * ${B("y")} + ${Rr("y")} = $M * ${B("n")} + ${Rr("n")} /\\ ${Rr("y")} < $M /\\ ${Rr("n")} < $M ==> " +
              s"${B("y")} = ${B("n")} /\\ ${Rr("y")} = ${Rr("n")}")
          parts <- conjs(ordered, lowY, lowN).flatMap(mp(unique, _)).flatMap(split)
          bits <- prop(s"(${B("y")} = 1) = (${B("n")} = 1)").flatMap(g => rewriting(Seq(parts(0)), g)(byBeta))
          out <- conj(parts(1), bits)
        } yield out
        backward <- for {
          h <- assumed(C)
          parts <- split(h._2)
          goal <- prop(E)
          zeroOne <- zeroNotOne
          equalBits <- for {
            ey <- binary(B("y"), bY)
            en <- binary(B("n"), bN)
            wanted <- prop(s"${B("y")} = ${B("n")}")
            same = (a: Kernel.Thm, b: Kernel.Thm) => rewriting(Seq(a, b), wanted)(byBeta)
            mixed = (a: Kernel.Thm, b: Kernel.Thm) =>
              for {
                iff <- rw(a, parts(1)).flatMap(rw(b, _))
                one <- nm("1").map(Conv.refl)
                zeroIsOne <- LogicError.lift(Kernel.eqMp(iff, one)).orElse(Conv.sym(iff).flatMap(s => LogicError.lift(Kernel.eqMp(s, one))))
                contra <- rules.notElim(zeroOne, zeroIsOne)
                out <- rules.falsityElim(wanted, contra)
              } yield out
            out <- for {
              y0 <- assumed(s"${B("y")} = 0"); y1 <- assumed(s"${B("y")} = 1")
              n0 <- assumed(s"${B("n")} = 0"); n1 <- assumed(s"${B("n")} = 1")
              c00 <- same(y0._2, n0._2); c01 <- mixed(y0._2, n1._2)
              c10 <- mixed(y1._2, n0._2); c11 <- same(y1._2, n1._2)
              whenY0 <- rules.disjElim(en, c00, c01)
              whenY1 <- rules.disjElim(en, c10, c11)
              out <- rules.disjElim(ey, whenY0, whenY1)
            } yield out
          } yield out
          out <- rewriting(Seq(sy, sn, parts(0), equalBits), goal)(byBeta)
        } yield out
        out <- gen(Kernel.deductAntisym(backward, forward), yv, nv, kv)
      } yield out
    }

    /* ------------------------------------------------------------ the Walsh transform */

    private def CH(s: String, n: String, k: String): String = chi(s, n, k)

    /** Moving the subset by `2^k` leaves its character on `k` positions unchanged. */
    def chiTopShift: R[Kernel.Thm] = {
      val (kv, av, yv) = (Term.variable("k", Numbers), Term.variable("a", Numbers), Term.variable("y", Numbers))
      val K = "(k:num)"; val A = "NUM_POW 2 (k:num) + (a:num)"
      def factor(s: String) = s"(\\i:num. COND (${bit("i", s)}) (${sign(bit("i", "y:num"))}) 1)"
      for {
        pointwise <- for {
          held <- assumed(s"${v("m")} < $K")
          (mT, m) = held
          same <- at(k("BIT_BELOW_TOP"), s"${v("m")} < $K ==> ((${bit(v("m"), A)}) = (${bit(v("m"), "a:num")}))").flatMap(mp(_, m))
          goal <- prop(s"${factor(A)} ${v("m")} = ${factor("a:num")} ${v("m")}")
          out <- betaThen(goal)(g => rewriting(Seq(same), g)(byBeta)).flatMap(rules.disch(mT, _)).flatMap(gen(_, Term.variable("m", Numbers)))
        } yield out
        congruent <- at(k("PROD_CONGRUENCE_BELOW"),
          s"(!m:num. m < $K ==> ${factor(A)} m = ${factor("a:num")} m) ==> Prod ${factor(A)} $K = Prod ${factor("a:num")} $K")
        out <- mp(congruent, pointwise).flatMap(gen(_, kv, av, yv))
      } yield out
    }

    /** The characters on `k` positions are orthogonal: their products sum to `2^k` on agreeing residues and to 0 otherwise. */
    def orthogonal: R[Kernel.Thm] = {
      val (kv, yv, nv) = (Term.variable("k", Numbers), Term.variable("ya", Numbers), Term.variable("na", Numbers))
      def claim(K: String) =
        s"Sum (\\s:num. ${CH("s", "ya:num", K)} * ${CH("s", "na:num", K)}) (NUM_POW 2 ($K)) = " +
          s"COND (NUM_MOD (ya:num) (NUM_POW 2 ($K)) = NUM_MOD (na:num) (NUM_POW 2 ($K))) (real_of_num (NUM_POW 2 ($K))) 0"
      for {
        body <- prop(s"!ya:num. !na:num. ${claim("k:num")}")
        proved <- induct(kv, body)(
          _ =>
            for {
              goal <- prop(claim("0"))
              powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
              unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
              mods <- Seq("ya", "na").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, z) =>
                for {
                  done <- acc
                  lt <- at(fact("NUM_MOD_LT"), s"(0:num) < SUC 0 ==> NUM_MOD ($z:num) (SUC 0) < SUC 0").flatMap(mp(_, unit))
                  eq <- numLinText(Seq(lt), s"NUM_MOD ($z:num) (SUC 0) = 0")
                } yield done :+ eq
              }
              general <- Seq("SUM_SUC", "SUM_ZERO", "PROD_ZERO").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, n) =>
                for { done <- acc; f <- fact(n) } yield done :+ f)
              out <- rewriting(Seq(powZero) ++ mods ++ general, goal)(deciding(Seq.empty)(arithmetic)).flatMap(gen(_, yv, nv))
            } yield out,
          (kk, hyp, _) => {
            val K = v(kk.name)
            val M = s"NUM_POW 2 $K"
            for {
              goal <- prop(claim(s"SUC $K"))
              split_ <- at(k("MOD_EQ_SPLIT"),
                s"(NUM_MOD (ya:num) (NUM_POW 2 (SUC $K)) = NUM_MOD (na:num) (NUM_POW 2 (SUC $K))) = " +
                  s"(NUM_MOD ya ($M) = NUM_MOD na ($M) /\\ ((${bit(K, "ya")}) = (${bit(K, "na")})))")
              double <- for {
                s1 <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $K) = $M * 2")
                s2 <- num(s"$M * 2 = $M + $M")
                out <- trans(s1, s2)
              } yield out
              prodSuc <- fact("PROD_SUC")
              halves <- fact("SUM_HALVES")
              shiftChi = k("CHI_TOP_SHIFT")
              positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
              ih <- at(hyp, claim(K))
              out <- rewriting(Seq(split_), goal) { g1 =>
                rewriting(Seq(double, prodSuc, halves), g1) { g2 =>
                  betaThen(g2) { g3 =>
                    rewriting(Seq(shiftChi), g3) { g4 =>
                      for {
                        sides <- Term.destEq(g4).toRight(NotOfForm("an equation", g4))
                        (lhs, rhs) = sides
                        parts <- (lhs match {
                          case App(App(_, l1), l2) => Right((l1, l2))
                          case other => Left(NotOfForm("a sum of two sums", other))
                        })
                        (low, high) = parts
                        lowEq <- belowBound(low, s"\\s:num. ${CH("s", "ya:num", K)} * ${CH("s", "na:num", K)}", M) { (s, sBelow) =>
                          for {
                            off <- at(k("BIT_ABOVE"), s"$s < $M ==> ~(${bit(K, s)})").flatMap(mp(_, sBelow))
                          } yield (Seq.empty, Seq(off), Nil)
                        }
                        highEq <- belowBound(high,
                          s"\\s:num. ${sign(bit(K, "ya:num"))} * ${sign(bit(K, "na:num"))} * (${CH("s", "ya:num", K)} * ${CH("s", "na:num", K)})", M) { (s, sBelow) =>
                          for {
                            on <- at(k("BIT_TOP"), s"$s < $M ==> ${bit(K, s"$M + $s")}").flatMap(mp(_, sBelow))
                          } yield (Seq.empty, Seq(on), Nil)
                        }
                        scaled <- at(fact("SUM_SCALE"),
                          s"Sum (\\s:num. ${sign(bit(K, "ya:num"))} * ${sign(bit(K, "na:num"))} * (${CH("s", "ya:num", K)} * ${CH("s", "na:num", K)})) ($M) = " +
                            s"${sign(bit(K, "ya:num"))} * ${sign(bit(K, "na:num"))} * Sum (\\s:num. ${CH("s", "ya:num", K)} * ${CH("s", "na:num", K)}) ($M)")
                        out <- rewriting(Seq(lowEq, highEq, scaled, ih), g4) { g5 =>
                          for {
                            atoms <- Seq(s"NUM_MOD (ya:num) ($M) = NUM_MOD (na:num) ($M)", bit(K, "ya:num"), bit(K, "na:num"))
                              .foldLeft[R[List[Term]]](Right(Nil))((acc, t) => for { d <- acc; p <- prop(t) } yield d :+ p)
                            out <- byCases(atoms)(lits => deciding(lits)(arithmetic))(g5)
                          } yield out
                        }
                      } yield out
                    }
                  }
                }
              }.flatMap(gen(_, yv, nv))
            } yield out
          }
        )
      } yield proved
    }

    /**
     * The inversion of the Walsh transform on `k` bits, in the form `REAL_DFT_INVERSION` has: a
     * function at a residue modulo `2^k` is the sum over the subsets of its transform times their
     * character. By orthogonality: the double sum is swapped, the inner one is `2^k` on the residue
     * and 0 elsewhere, and what is left is `PICK`, this file's own copy of `Decision`'s `SUM_INDICATOR`.
     */
    def walshInversion: R[Kernel.Thm] = {
      val f = Term.variable("f", Type.fun(Numbers, Reals))
      val (kv, nv, sv, yv) = (Term.variable("k", Numbers), Term.variable("n", Numbers), Term.variable("s", Numbers), Term.variable("y", Numbers))
      val F = "(f:num->real)"; val K = "(k:num)"; val N = "(n:num)"
      val M = s"NUM_POW 2 $K"; val Mr = s"real_of_num ($M)"
      def ch(s: String, n: String) = CH(s, n, K)
      def G(s: String, y: String) = s"$F $y * ${ch(s, y)} * (${ch(s, N)} / $Mr)"
      val Wt = (s: String) => s"Sum (\\y:num. $F y * ${ch(s, "y")}) ($M) / $Mr"
      for {
        boundT <- nm(M)
        // (a) each term of the outer sum as a sum over y
        scaled <- for {
          sr <- at(fact("SUM_SCALE_RIGHT"),
            s"Sum (\\y:num. ${G("(s:num)", "y")}) ($M) = Sum (\\y:num. $F y * ${ch("(s:num)", "y")}) ($M) * (${ch("(s:num)", N)} / $Mr)")
          moved <- identity(s"${Wt("(s:num)")} * ${ch("(s:num)", N)} = Sum (\\y:num. $F y * ${ch("(s:num)", "y")}) ($M) * (${ch("(s:num)", N)} / $Mr)")
          pointwise <- Conv.sym(sr).flatMap(trans(moved, _))
          out <- sumCongReal(sv, pointwise, boundT)
        } yield out
        // (b) the double sum swapped
        swapped <- at(fact("SUM_SWAP"),
          s"Sum (\\s:num. Sum (\\y:num. ${G("s", "y")}) ($M)) ($M) = Sum (\\y:num. Sum (\\s:num. ${G("s", "y")}) ($M)) ($M)")
        // (c) the inner sum over s is f y / 2^k times the sum of the products of characters
        factored <- for {
          inner <- identity(s"${G("(s:num)", "(y:num)")} = $F y / $Mr * (${ch("(s:num)", "y")} * ${ch("(s:num)", N)})")
          congruent <- sumCongReal(sv, inner, boundT)
          sc <- at(fact("SUM_SCALE"),
            s"Sum (\\s:num. $F (y:num) / $Mr * (${ch("s", "y")} * ${ch("s", N)})) ($M) = $F y / $Mr * Sum (\\s:num. ${ch("s", "y")} * ${ch("s", N)}) ($M)")
          pointwise <- trans(congruent, sc)
          out <- sumCongReal(yv, pointwise, boundT)
        } yield out
        // (d) orthogonality below 2^k, where the residue of y is y
        factoredT <- Term.destEq(factored.conclusion).map(_._2).toRight(NotOfForm("an equation", factored.conclusion))
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
        indicated <- belowBound(factoredT, s"\\y:num. $F y * ($Mr / $Mr) * COND (y = NUM_MOD $N ($M)) 1 0", M) { (y, yBelow) =>
          for {
            orth <- at(k("WALSH_ORTHOGONAL"),
              s"Sum (\\s:num. ${ch("s", y)} * ${ch("s", N)}) ($M) = COND (NUM_MOD $y ($M) = NUM_MOD $N ($M)) ($Mr) 0")
            own <- at(fact("NUM_DIV_MOD_BELOW"), s"$y < $M ==> NUM_DIV $y ($M) = 0 /\\ NUM_MOD $y ($M) = $y")
              .flatMap(mp(_, yBelow)).flatMap(rules.conjElim2)
            same <- prop(s"$y = NUM_MOD $N ($M)")
          } yield (Seq(orth, own), Seq.empty, List(same))
        }
        // (e) the cancelled factor, then the indicator
        cancelled <- for {
          nonzero <- for {
            above <- at(fact("NUM_REAL_LT"), s"(0:num) < $M ==> real_of_num 0 + 1 <= $Mr").flatMap(mp(_, positive))
            held <- assumed(s"$Mr = 0")
            absurd <- fact("NUM_REAL_ZERO").flatMap(rw(_, above)).flatMap(a => lin(Seq(held._2, a), "F"))
            out <- rules.notIntro(held._1, absurd)
          } yield out
          inverse <- at(fact("MUL_INVERSE"), s"~($Mr = 0) ==> $Mr * inv ($Mr) = 1").flatMap(mp(_, nonzero))
          ratio <- identity(s"$Mr / $Mr = $Mr * inv ($Mr)").flatMap(trans(_, inverse))
          pointwise <- identity(s"$F (y:num) * 1 * COND ((y:num) = NUM_MOD $N ($M)) 1 0 = $F y * COND (y = NUM_MOD $N ($M)) 1 0")
          ones <- prop(s"Sum (\\y:num. $F y * ($Mr / $Mr) * COND (y = NUM_MOD $N ($M)) 1 0) ($M) = Sum (\\y:num. $F y * COND (y = NUM_MOD $N ($M)) 1 0) ($M)")
            .flatMap(g => rewriting(Seq(ratio), g)(g2 => sumCongReal(yv, pointwise, boundT).flatMap(landsOn(_)(g2))))
          below <- at(fact("NUM_MOD_LT"), s"0 < $M ==> NUM_MOD $N ($M) < $M").flatMap(mp(_, positive))
          picked <- at(k("PICK"), s"NUM_MOD $N ($M) < $M ==> Sum (\\y:num. $F y * COND (y = NUM_MOD $N ($M)) 1 0) ($M) = $F (NUM_MOD $N ($M))")
            .flatMap(mp(_, below))
          out <- trans(ones, picked)
        } yield out
        chain <- trans(scaled, swapped, factored, indicated, cancelled)
        out <- Conv.sym(chain).flatMap(gen(_, f, kv, nv))
      } yield out
    }

    /* ------------------------------------------------------------ rows as numbers */

    private def code(row: String, k: String): String = s"NUM_SUM (\\j:num. COND ($row j) (NUM_POW 2 j) 0) ($k)"

    /** The first `k` cells of a row, read as the bits of a number below `2^k`. */
    def encode: R[Kernel.Thm] = {
      val (kv, xv) = (Term.variable("k", Numbers), Term.variable("x", Rows))
      def claim(K: String) =
        s"${code(X, K)} < NUM_POW 2 ($K) /\\ (!j:num. j < $K ==> ((${bit("j", code(X, K))}) = $X j))"
      for {
        body <- prop(s"!x:num->bool. ${claim("k:num")}")
        proved <- induct(kv, body)(
          _ =>
            for {
              goal <- prop(claim("0"))
              zero <- at(fact("NUM_SUM_ZERO"), s"${code(X, "0")} = 0")
              powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
              bound <- numLinText(Seq.empty, "(0:num) < SUC 0")
              vacuous <- for {
                held <- assumed(s"${v("j")} < 0")
                none <- at(fact("NUM_NOT_LT_ZERO"), s"~(${v("j")} < 0)")
                contra <- rules.notElim(none, held._2)
                wanted <- prop(s"(${bit(v("j"), code(X, "0"))}) = $X ${v("j")}")
                out <- rules.falsityElim(wanted, contra).flatMap(rules.disch(held._1, _)).flatMap(gen(_, j))
              } yield out
              leftT <- prop(s"${code(X, "0")} < NUM_POW 2 0")
              left <- rewriting(Seq(zero, powZero), leftT)(landsOn(bound))
              first <- conj(left, vacuous)
              out <- gen(first, x)
            } yield out,
          (kk, hyp, _) => {
            val K = v(kk.name)
            val C = code(X, K)
            val Top = s"COND ($X $K) (NUM_POW 2 $K) 0"
            for {
              goal <- prop(claim(s"SUC $K"))
              ih <- spec(hyp, x)
              ihParts <- split(ih)
              (below, bits) = (ihParts(0), ihParts(1))
              grow <- at(fact("NUM_SUM_SUC"), s"${code(X, s"SUC $K")} = $C + $Top")
              powSuc <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $K) = NUM_POW 2 $K * 2")
              xk <- prop(s"$X $K")
              onCase <- for {
                held <- assumed(s"$X $K")
                topT <- term(Top, Numbers)
                value <- condValue(topT, Seq(held._2)).flatMap(_.toRight(NotOfForm("decided", xk)))
                swap <- num(s"$C + NUM_POW 2 $K = NUM_POW 2 $K + $C")
                sum <- rw(value, grow).flatMap(trans(_, swap))
                newBound <- numLinText(Seq(below, powSuc), s"NUM_POW 2 $K + $C < NUM_POW 2 (SUC $K)")
                top <- at(k("BIT_TOP"), s"$C < NUM_POW 2 $K ==> ${bit(K, s"NUM_POW 2 $K + $C")}").flatMap(mp(_, below))
                every <- for {
                  jh <- assumed(s"${v("j")} < SUC $K")
                  split2 <- at(fact("NUM_LT_SUC_CASES"), s"${v("j")} < SUC $K ==> ${v("j")} < $K \\/ ${v("j")} = $K").flatMap(mp(_, jh._2))
                  lower <- for {
                    lh <- assumed(s"${v("j")} < $K")
                    same <- at(k("BIT_BELOW_TOP"), s"${v("j")} < $K ==> ((${bit(v("j"), s"NUM_POW 2 $K + $C")}) = (${bit(v("j"), C)}))").flatMap(mp(_, lh._2))
                    old <- at(bits, s"${v("j")} < $K ==> ((${bit(v("j"), C)}) = $X ${v("j")})").flatMap(mp(_, lh._2))
                    out <- trans(same, old)
                  } yield out
                  atTop <- for {
                    eh <- assumed(s"${v("j")} = $K")
                    wanted <- prop(s"(${bit(v("j"), s"NUM_POW 2 $K + $C")}) = $X ${v("j")}")
                    out <- rewriting(Seq(eh._2), wanted)(g => tauto(Seq(top, held._2), g))
                  } yield out
                  out <- rules.disjElim(split2, lower, atTop).flatMap(rules.disch(jh._1, _)).flatMap(gen(_, j))
                } yield out
                both <- conj(newBound, every)
                back <- Conv.sym(sum)
                out <- rw(back, both)
              } yield out
              offCase <- for {
                held <- assumed(s"~($X $K)")
                topT <- term(Top, Numbers)
                value <- condValue(topT, Seq(held._2)).flatMap(_.toRight(NotOfForm("decided", xk)))
                drop <- at(fact("NUM_ADD_ZERO"), s"$C + 0 = $C")
                sum <- rw(value, grow).flatMap(trans(_, drop))
                newBound <- numLinText(Seq(below, powSuc), s"$C < NUM_POW 2 (SUC $K)")
                off <- at(k("BIT_ABOVE"), s"$C < NUM_POW 2 $K ==> ~(${bit(K, C)})").flatMap(mp(_, below))
                every <- for {
                  jh <- assumed(s"${v("j")} < SUC $K")
                  split2 <- at(fact("NUM_LT_SUC_CASES"), s"${v("j")} < SUC $K ==> ${v("j")} < $K \\/ ${v("j")} = $K").flatMap(mp(_, jh._2))
                  lower <- for {
                    lh <- assumed(s"${v("j")} < $K")
                    out <- at(bits, s"${v("j")} < $K ==> ((${bit(v("j"), C)}) = $X ${v("j")})").flatMap(mp(_, lh._2))
                  } yield out
                  atTop <- for {
                    eh <- assumed(s"${v("j")} = $K")
                    wanted <- prop(s"(${bit(v("j"), C)}) = $X ${v("j")}")
                    out <- rewriting(Seq(eh._2), wanted)(g => tauto(Seq(off, held._2), g))
                  } yield out
                  out <- rules.disjElim(split2, lower, atTop).flatMap(rules.disch(jh._1, _)).flatMap(gen(_, j))
                } yield out
                both <- conj(newBound, every)
                back <- Conv.sym(sum)
                out <- rw(back, both)
              } yield out
              out <- classical.cases(xk, onCase, offCase).flatMap(gen(_, x))
            } yield out
          }
        )
      } yield proved
    }

    /** `0 + n = n`, as a rule. */
    private def zeroAdd: R[Kernel.Thm] = num("0 + (n:num) = n").flatMap(gen(_, Term.variable("n", Numbers)))

    /** The cell `(t, i)` as the Walsh series of the cell `(t, 0)` over the `2 t + 1` cells of its window. */
    def walshFormRows: R[Kernel.Thm] =
      rule { hs =>
        val T = "(t:num)"; val I = v("i")
        val Kw = s"2 * $T + 1"; val M = s"NUM_POW 2 ($Kw)"; val Mr = s"real_of_num ($M)"
        val Row = s"(\\q:num. $X ($I + q))"
        val C = code(Row, Kw)
        def window(sub: String) = s"Prod (\\j:num. COND (${bit("j", sub)}) (${sign(s"$X ($I + j)")}) 1) ($Kw)"
        def chiAt(sub: String, n: String) = s"Prod (\\j:num. COND (${bit("j", sub)}) (${sign(bit("j", n))}) 1) ($Kw)"
        val W = (s: String) => s"Sum (\\y:num. ${sign(s"$Run (\\p:num. ${bit("p", "y")}) $T 0")} * ${chiAt(s, "y")}) ($M) / $Mr"
        for {
          coneHere <- under("RULE_THIRTY_CONE")
          shiftHere <- under("RULE_THIRTY_SHIFT")
          enc <- at(k("ENCODE"), s"$C < $M /\\ (!j:num. j < $Kw ==> ((${bit("j", C)}) = $X ($I + j)))").flatMap(split)
          (below, bits) = (enc(0), enc(1))
          cell <- term(s"\\y:num. ${sign(s"$Run (\\p:num. ${bit("p", "y")}) $T 0")}", Type.fun(Numbers, Reals))
          atCell <- rules.specPrefix(k("WALSH_INVERSION"), List(cell)).flatMap(beta)
          inverted <- at(atCell,
            s"${sign(s"$Run (\\p:num. ${bit("p", s"NUM_MOD ($C) ($M)")}) $T 0")} = " +
              s"Sum (\\s:num. ${W("s")} * ${chiAt("s", C)}) ($M)")
          own <- at(fact("NUM_DIV_MOD_BELOW"), s"$C < $M ==> NUM_DIV ($C) ($M) = 0 /\\ NUM_MOD ($C) ($M) = $C")
            .flatMap(mp(_, below)).flatMap(rules.conjElim2)
          atCode <- rw(own, inverted)
          characters <- for {
            pointwise <- for {
              held <- assumed(s"${v("j")} < $Kw")
              same <- at(bits, s"${v("j")} < $Kw ==> ((${bit(v("j"), C)}) = $X ($I + ${v("j")}))").flatMap(mp(_, held._2))
              goal <- prop(s"COND (${bit(v("j"), "s:num")}) (${sign(bit(v("j"), C))}) 1 = COND (${bit(v("j"), "s:num")}) (${sign(s"$X ($I + ${v("j")})")}) 1")
              out <- rewriting(Seq(same), goal)(byBeta).flatMap(rules.disch(held._1, _)).flatMap(gen(_, j))
            } yield out
            congruent <- at(k("PROD_CONGRUENCE_BELOW"),
              s"(!j:num. j < $Kw ==> COND (${bit("j", "s:num")}) (${sign(bit("j", C))}) 1 = COND (${bit("j", "s:num")}) (${sign(s"$X ($I + j)")}) 1) ==> " +
                s"${chiAt("(s:num)", C)} = ${window("(s:num)")}")
            out <- mp(congruent, pointwise).flatMap(gen(_, Term.variable("s", Numbers)))
          } yield out
          series <- rw(characters, atCode)
          moved <- for {
            plus <- zeroAdd
            // By position, because the rows are lambdas applied to a sum, which the matcher does not decide;
            // a wrong order is refused below, where the antecedent is detached against `bits`.
            rowCode <- term(s"\\p:num. ${bit("p", C)}", Rows)
            rowWin <- term(Row, Rows)
            zeroT <- nm("0")
            c0 <- rules.specAll(coneHere, List(t, zeroT, rowCode, rowWin)).flatMap(beta)
            c1 <- rw(plus, c0)
            agree <- mp(c1, bits)
            s0 <- rules.specAll(shiftHere, List(x, t, i, zeroT)).flatMap(beta)
            s1 <- at(fact("NUM_ADD_ZERO"), s"$I + 0 = $I").flatMap(rw(_, s0))
            out <- Conv.sym(agree).flatMap(trans(s1, _))
          } yield out
          goal <- prop(s"${sign(s"$Run $X $T $I")} = Sum (\\s:num. ${W("s")} * ${window("s")}) ($M)")
          out <- rewriting(Seq(moved), goal)(landsOn(series)).flatMap(gen(_, t, i, x))
        } yield out
      }

    /** Over all `2^(2 t + 1)` windows, the cell `(t, 0)` is on exactly as often as off. */
    def balancedRows: R[Kernel.Thm] =
      rule { _ =>
        val T = "(t:num)"; val Mv = "(m:num)"
        val N = s"NUM_POW 2 (2 * $T)"
        def g(y: String) = sign(s"$Run (\\p:num. ${bit("p", y)}) $T 0")
        for {
          permutive <- under("RULE_THIRTY_LEFT_PERMUTIVE")
          double <- for {
            succ <- numLinText(Seq.empty, s"2 * $T + 1 = SUC (2 * $T)")
            pow <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC (2 * $T)) = $N * 2")
            twice <- num(s"$N * 2 = $N + $N")
            out <- Conv.apTerm(term("NUM_POW 2", Type.fun(Numbers, Numbers)).toOption.get, succ).flatMap(trans(_, pow, twice))
          } yield out
          evenOdd <- at(fact("SUM_EVEN_ODD"),
            s"Sum (\\y:num. ${g("y")}) ($N + $N) = Sum (\\m:num. ${g("m + m")}) ($N) + Sum (\\m:num. ${g("SUC (m + m)")}) ($N)")
          added <- at(fact("SUM_ADD"),
            s"Sum (\\m:num. ${g("m + m")} + ${g("SUC (m + m)")}) ($N) = Sum (\\m:num. ${g("m + m")}) ($N) + Sum (\\m:num. ${g("SUC (m + m)")}) ($N)")
            .flatMap(Conv.sym)
          pointwise <- for {
            evenEq <- num(s"$Mv + $Mv = 2 * $Mv + 0")
            oddEq <- numLinText(Seq.empty, s"SUC ($Mv + $Mv) = 2 * $Mv + 1")
            agree <- for {
              held <- assumed(s"0 < ${v("j")} /\\ ${v("j")} < 2 * $T + 1")
              positive <- rules.conjElim1(held._2)
              le <- numLinText(Seq(positive), s"1 <= ${v("j")}")
              sub <- at(fact("NUM_REAL_SUB"), s"1 <= ${v("j")} ==> real_of_num (NUM_SUB ${v("j")} 1) = real_of_num ${v("j")} - real_of_num 1").flatMap(mp(_, le))
              back <- numLinText(Seq(sub), s"SUC (NUM_SUB ${v("j")} 1) = ${v("j")}")
              smallE <- numLinText(Seq.empty, "(0:num) < 2"); smallO <- numLinText(Seq.empty, "(1:num) < 2")
              h0 <- at(k("BIT_HALVE"), s"(0:num) < 2 ==> ((${bit(s"SUC (NUM_SUB ${v("j")} 1)", s"2 * $Mv + 0")}) = (${bit(s"NUM_SUB ${v("j")} 1", Mv)}))").flatMap(mp(_, smallE))
              h1 <- at(k("BIT_HALVE"), s"(1:num) < 2 ==> ((${bit(s"SUC (NUM_SUB ${v("j")} 1)", s"2 * $Mv + 1")}) = (${bit(s"NUM_SUB ${v("j")} 1", Mv)}))").flatMap(mp(_, smallO))
              both <- Conv.sym(h1).flatMap(trans(h0, _))
              e1 <- Conv.sym(evenEq); o1 <- Conv.sym(oddEq)
              moved <- rw(back, both).flatMap(rw(e1, _)).flatMap(rw(o1, _))
              plus <- zeroAdd
              wanted <- prop(s"(${bit("0 + " + v("j"), s"$Mv + $Mv")}) = (${bit("0 + " + v("j"), s"SUC ($Mv + $Mv)")})")
              out <- rewriting(Seq(plus), wanted)(landsOn(moved)).flatMap(rules.disch(held._1, _)).flatMap(gen(_, j))
            } yield out
            differ <- for {
              powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
              ones <- Seq(s"$Mv + $Mv", s"SUC ($Mv + $Mv)").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, y) =>
                for {
                  done <- acc
                  unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
                  dm <- numLinText(Seq.empty, s"$y = SUC 0 * ($y) + 0")
                  u <- at(fact("NUM_DIV_MOD_UNIQUE"), s"$y = SUC 0 * ($y) + 0 /\\ 0 < SUC 0 ==> $y = NUM_DIV ($y) (SUC 0) /\\ 0 = NUM_MOD ($y) (SUC 0)")
                    .flatMap(th => conj(dm, unit).flatMap(mp(th, _))).flatMap(rules.conjElim1).flatMap(Conv.sym)
                } yield done :+ u
              }
              shiftE <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mv + 0) 2 = NUM_MOD 0 2").flatMap(th => Conv.sym(evenEq).flatMap(rw(_, th)))
              shiftO <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mv + 1) 2 = NUM_MOD 1 2").flatMap(th => Conv.sym(oddEq).flatMap(rw(_, th)))
              t2 <- two
              modZero <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(rules.conjElim2)
              oneTwo <- numLinText(Seq.empty, "(1:num) < 2")
              modOne <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneTwo)).flatMap(rules.conjElim2)
              apart <- zeroNotOne
              wanted <- prop(s"~((${bit("0", s"$Mv + $Mv")}) = (${bit("0", s"SUC ($Mv + $Mv)")}))")
              one <- nm("1").map(Kernel.refl)
              out <- rewriting(Seq(powZero) ++ ones ++ Seq(shiftE, shiftO, modZero, modOne), wanted)(gg => tauto(Seq(apart, one), gg))
            } yield out
            evenRow <- term(s"\\p:num. ${bit("p", s"$Mv + $Mv")}", Rows)
            oddRow <- term(s"\\p:num. ${bit("p", s"SUC ($Mv + $Mv)")}", Rows)
            zeroT <- nm("0")
            instance_ <- rules.specAll(permutive, List(t, zeroT, evenRow, oddRow)).flatMap(beta)
            apartRuns <- conj(agree, differ).flatMap(mp(instance_, _))
            goal <- prop(s"${g(s"$Mv + $Mv")} + ${g(s"SUC ($Mv + $Mv)")} = 0")
            atoms <- Seq(s"$Run (\\p:num. ${bit("p", s"$Mv + $Mv")}) $T 0", s"$Run (\\p:num. ${bit("p", s"SUC ($Mv + $Mv)")}) $T 0")
              .foldLeft[R[List[Term]]](Right(Nil))((acc, a) => for { d <- acc; p <- prop(a) } yield d :+ p)
            out <- byCases(atoms, Vector(apartRuns))(lits => orAbsurd(lits)(deciding(lits)(arithmetic)))(goal)
          } yield out
          zeros <- sumCongReal(Term.variable("m", Numbers), pointwise, term(N, Numbers).toOption.get)
          none <- at(fact("SUM_OF_ZERO"), s"Sum (\\m:num. 0) ($N) = 0")
          goal <- prop(s"Sum (\\y:num. ${g("y")}) (NUM_POW 2 (2 * $T + 1)) = 0")
          closed <- rewriting(Seq(double), goal) { g1 =>
            for {
              chain <- trans(evenOdd, added, zeros, none)
              out <- landsOn(chain)(g1)
            } yield out
          }
          out <- gen(closed, t)
        } yield out
      }

    /* ------------------------------------------------------------ the map on the naturals */

    private val gvar = Term.variable("g", Steps)
    private val itvar = Term.variable("iterate", Iterates)

    /** The four equations of the map and its iterate, assumed, and what `body` proves from them discharged. */
    private def mapRule(body: Vector[Kernel.Thm] => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        hT <- prop(MapEquations)
        h <- LogicError.lift(Kernel.assume(hT))
        hs <- split(h)
        proved <- body(hs)
        out <- rules.disch(hT, proved).flatMap(gen(_, gvar, itvar))
      } yield out

    /** A fact about the map, at the map assumed. */
    private def underMap(name: String): R[Kernel.Thm] =
      for {
        hT <- prop(MapEquations)
        h <- LogicError.lift(Kernel.assume(hT))
        out <- spec(k(name), gvar, itvar).flatMap(mp(_, h))
      } yield out

    /** `COND b 1 0 < 2` over the naturals. */
    def condBelowTwo: R[Kernel.Thm] = {
      val b = Term.variable("b", Type.Bool)
      for {
        goal <- prop("COND (b:bool) 1 0 < (2:num)")
        out <- byCases(List(b))(lits => deciding(lits)(numLin(Seq.empty, _)))(goal).flatMap(gen(_, b))
      } yield out
    }

    /** `NUM_MOD x 1 = 0`. */
    def modOne: R[Kernel.Thm] =
      for {
        unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
        lt <- at(fact("NUM_MOD_LT"), "(0:num) < SUC 0 ==> NUM_MOD (x:num) (SUC 0) < SUC 0").flatMap(mp(_, unit))
        out <- numLinText(Seq(lt), "NUM_MOD (x:num) (SUC 0) = 0").flatMap(gen(_, Term.variable("x", Numbers)))
      } yield out

    /** A residue modulo `2^k` is its own residue. */
    def modMod: R[Kernel.Thm] = {
      val (nv, kv) = (Term.variable("n", Numbers), Term.variable("k", Numbers))
      val M = "NUM_POW 2 (k:num)"; val Rr = s"NUM_MOD (n:num) ($M)"
      for {
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
        lt <- at(fact("NUM_MOD_LT"), s"0 < $M ==> $Rr < $M").flatMap(mp(_, positive))
        out <- at(fact("NUM_DIV_MOD_BELOW"), s"$Rr < $M ==> NUM_DIV ($Rr) ($M) = 0 /\\ NUM_MOD ($Rr) ($M) = $Rr")
          .flatMap(mp(_, lt)).flatMap(rules.conjElim2).flatMap(gen(_, nv, kv))
      } yield out
    }

    /** `NUM_MOD (2 m + e) (2^(SUC k)) = 2 (NUM_MOD m (2^k)) + e` for `e < 2`. */
    def modDouble: R[Kernel.Thm] = {
      val (kv, mv, ev) = (Term.variable("k", Numbers), Term.variable("m", Numbers), Term.variable("e", Numbers))
      val P = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
      val D = s"NUM_DIV (m:num) ($P)"; val Mm = s"NUM_MOD (m:num) ($P)"
      val n = "2 * (m:num) + (e:num)"
      for {
        held <- assumed("(e:num) < 2")
        (smallT, small) = held
        dm <- at(fact("NUM_DIV_MOD"), s"$P * $D + $Mm = m")
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $P").flatMap(mp(_, t2)))
        below <- at(fact("NUM_MOD_LT"), s"0 < $P ==> $Mm < $P").flatMap(mp(_, positive))
        powSuc <- at(fact("NUM_POW_SUC"), s"$P2 = $P * 2")
        regroup <- num(s"2 * ($P * $D + $Mm) + (e:num) = $P * 2 * $D + (2 * $Mm + e)")
        split_ <- rw(dm, regroup).flatMap(e => Conv.sym(powSuc).flatMap(rw(_, e)))
        bound <- numLinText(Seq(below, small, powSuc), s"2 * $Mm + (e:num) < $P2")
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"$n = $P2 * $D + (2 * $Mm + e) /\\ 2 * $Mm + e < $P2 ==> $D = NUM_DIV ($n) ($P2) /\\ 2 * $Mm + e = NUM_MOD ($n) ($P2)")
        out <- conj(split_, bound).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym)
          .flatMap(rules.disch(smallT, _)).flatMap(gen(_, kv, mv, ev))
      } yield out
    }

    /** Halving a residue modulo `2^(SUC k)` gives the residue of the half modulo `2^k`, and the low bit survives. */
    def divModShift: R[Kernel.Thm] = {
      val (nv, kv) = (Term.variable("n", Numbers), Term.variable("k", Numbers))
      val N = "(n:num)"; val P = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
      val D = s"NUM_DIV $N 2"; val E = s"NUM_MOD $N 2"; val X = s"NUM_MOD $N ($P2)"
      for {
        dm <- at(fact("NUM_DIV_MOD"), s"2 * $D + $E = $N")
        lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $E < 2").flatMap(mp(_, t2)))
        doubled <- at(k("MOD_DOUBLE"), s"$E < 2 ==> NUM_MOD (2 * $D + $E) ($P2) = 2 * NUM_MOD ($D) ($P) + $E").flatMap(mp(_, lt))
          .flatMap(rw(dm, _))
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"$X = 2 * NUM_MOD ($D) ($P) + $E /\\ $E < 2 ==> NUM_MOD ($D) ($P) = NUM_DIV ($X) 2 /\\ $E = NUM_MOD ($X) 2")
        parts <- conj(doubled, lt).flatMap(mp(unique, _)).flatMap(split)
        a <- Conv.sym(parts(0)); b <- Conv.sym(parts(1))
        out <- conj(a, b).flatMap(gen(_, nv, kv))
      } yield out
    }

    /** The two equations of the map as one: `g p q n` is its low bit and twice the map of the half. */
    def gStep: R[Kernel.Thm] =
      mapRule { hs =>
        val P = "(pb:bool)"; val Q = "(qb:bool)"; val N = "(nb:num)"
        val D = s"NUM_DIV $N 2"; val Mo = s"NUM_MOD $N 2"; val E = s"($Mo = 1)"
        val (pv, qv, nv) = (Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("nb", Numbers))
        for {
          goal <- prop(s"$G $P $Q $N = COND (~(($P \\/ $Q) = $E)) 1 0 + 2 * $G $E $P ($D)")
          dm <- at(fact("NUM_DIV_MOD"), s"2 * $D + $Mo = $N")
          lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $Mo < 2").flatMap(mp(_, t2)))
          either <- binary(Mo, lt)
          zeroF <- zeroOneFalse
          oneT <- oneOneTrue
          close = byCases(List(pv, qv))(lits => deciding(lits)(numClose)) _
          even <- for {
            h <- assumed(s"$Mo = 0")
            inst <- at(hs(0), s"$G $P $Q (2 * $D) = COND ($P \\/ $Q) 1 0 + 2 * $G F $P ($D)")
            noZero <- at(fact("NUM_ADD_ZERO"), s"2 * $D + 0 = 2 * $D")
            twice <- rw(h._2, dm).flatMap(rw(noZero, _))
            atN <- rw(twice, inst)
            out <- rewriting(Seq(atN, h._2, zeroF), goal)(close)
          } yield out
          odd <- for {
            h <- assumed(s"$Mo = 1")
            inst <- at(hs(1), s"$G $P $Q (2 * $D + 1) = COND ($P \\/ $Q) 0 1 + 2 * $G T $P ($D)")
            twice <- rw(h._2, dm)
            atN <- rw(twice, inst)
            out <- rewriting(Seq(atN, h._2, oneT), goal)(close)
          } yield out
          out <- rules.disjElim(either, even, odd).flatMap(gen(_, pv, qv, nv))
        } yield out
      }

    /** The low `k` bits of the map's value depend only on the low `k` bits of its argument. */
    def gResidues: R[Kernel.Thm] =
      mapRule { _ =>
        val (kv, pv, qv, nv) = (Term.variable("kb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("nb", Numbers))
        def claim(K: String) =
          s"NUM_MOD ($G (pb:bool) (qb:bool) (nb:num)) (NUM_POW 2 ($K)) = NUM_MOD ($G pb qb (NUM_MOD nb (NUM_POW 2 ($K)))) (NUM_POW 2 ($K))"
        for {
          step <- underMap("G_STEP")
          body <- prop(s"!pb:bool. !qb:bool. !nb:num. ${claim("kb:num")}")
          proved <- induct(kv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                out <- rewriting(Seq(powZero, k("MOD_ONE")), goal)(byBeta).flatMap(gen(_, pv, qv, nv))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name); val M = s"NUM_POW 2 $K"; val P2 = s"NUM_POW 2 (SUC $K)"
              val N = "(nb:num)"; val Pb = "(pb:bool)"; val Qb = "(qb:bool)"
              val E = s"(NUM_MOD $N 2 = 1)"; val D = s"NUM_DIV $N 2"; val Rr = s"NUM_MOD $N ($P2)"
              val C = s"COND (~(($Pb \\/ $Qb) = $E)) 1 0"
              val X = s"$G $E $Pb ($D)"; val Xr = s"$G $E $Pb (NUM_MOD ($D) ($M))"
              for {
                goal <- prop(claim(s"SUC $K"))
                atN <- at(step, s"$G $Pb $Qb $N = $C + 2 * $X")
                atR <- at(step, s"$G $Pb $Qb ($Rr) = COND (~(($Pb \\/ $Qb) = (NUM_MOD ($Rr) 2 = 1))) 1 0 + 2 * $G (NUM_MOD ($Rr) 2 = 1) $Pb (NUM_DIV ($Rr) 2)")
                shifts <- at(k("DIV_MOD_SHIFT"), s"NUM_DIV ($Rr) 2 = NUM_MOD ($D) ($M) /\\ NUM_MOD ($Rr) 2 = NUM_MOD $N 2").flatMap(split)
                small <- at(k("COND_BELOW_TWO"), s"$C < (2:num)")
                swap1 <- num(s"$C + 2 * $X = 2 * $X + $C")
                swap2 <- num(s"$C + 2 * $Xr = 2 * $Xr + $C")
                d1 <- at(k("MOD_DOUBLE"), s"$C < (2:num) ==> NUM_MOD (2 * $X + $C) ($P2) = 2 * NUM_MOD ($X) ($M) + $C").flatMap(mp(_, small))
                d2 <- at(k("MOD_DOUBLE"), s"$C < (2:num) ==> NUM_MOD (2 * $Xr + $C) ($P2) = 2 * NUM_MOD ($Xr) ($M) + $C").flatMap(mp(_, small))
                ih <- at(hyp, s"NUM_MOD ($X) ($M) = NUM_MOD ($G $E $Pb (NUM_MOD ($D) ($M))) ($M)")
                out <- rewriting(Seq(atN, atR) ++ shifts ++ Seq(swap1, swap2, d1, d2, ih), goal)(byBeta).flatMap(gen(_, pv, qv, nv))
              } yield out
            }
          )
        } yield proved
      }

    /** The low `k` bits of the `t`-th iterate depend only on the low `k` bits of the start. */
    def mapResidues: R[Kernel.Thm] =
      mapRule { hs =>
        val (tv, kv, nv) = (Term.variable("tb", Numbers), Term.variable("kb", Numbers), Term.variable("nb", Numbers))
        val M = "NUM_POW 2 (kb:num)"
        def claim(T: String) = s"NUM_MOD ($It (nb:num) ($T)) ($M) = NUM_MOD ($It (NUM_MOD nb ($M)) ($T)) ($M)"
        for {
          residues <- underMap("G_RESIDUES")
          body <- prop(s"!kb:num. !nb:num. ${claim("tb:num")}")
          proved <- induct(tv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                own <- at(k("MOD_MOD"), s"NUM_MOD (NUM_MOD (nb:num) ($M)) ($M) = NUM_MOD nb ($M)")
                out <- rewriting(Seq(hs(2), own), goal)(byBeta).flatMap(gen(_, kv, nv))
              } yield out,
            (kk, hyp, _) => {
              val T = v(kk.name)
              val X = s"$It (nb:num) $T"; val Y = s"$It (NUM_MOD (nb:num) ($M)) $T"
              for {
                goal <- prop(claim(s"SUC $T"))
                r1 <- at(residues, s"NUM_MOD ($G F F ($X)) ($M) = NUM_MOD ($G F F (NUM_MOD ($X) ($M))) ($M)")
                r2 <- at(residues, s"NUM_MOD ($G F F ($Y)) ($M) = NUM_MOD ($G F F (NUM_MOD ($Y) ($M))) ($M)")
                ih <- at(hyp, s"NUM_MOD ($X) ($M) = NUM_MOD ($Y) ($M)")
                out <- rewriting(Seq(hs(3), r1, r2, ih), goal)(byBeta).flatMap(gen(_, kv, nv))
              } yield out
            }
          )
          out <- spec(proved, tv, kv, nv).flatMap(gen(_, tv, kv, nv))
        } yield out
      }

    /** `a = b` for two numbers below 2 whose being 1 is the same proposition. */
    private def equalFromBits(a: String, b: String, aBelow: Kernel.Thm, bBelow: Kernel.Thm, iff: Kernel.Thm): R[Kernel.Thm] =
      for {
        ea <- binary(a, aBelow)
        eb <- binary(b, bBelow)
        wanted <- prop(s"$a = $b")
        zeroOne <- zeroNotOne
        same = (x: Kernel.Thm, y: Kernel.Thm) => rewriting(Seq(x, y), wanted)(byBeta)
        mixed = (x: Kernel.Thm, y: Kernel.Thm) =>
          for {
            moved <- rw(x, iff).flatMap(rw(y, _))
            one <- nm("1").map(Conv.refl)
            zeroIsOne <- LogicError.lift(Kernel.eqMp(moved, one)).orElse(Conv.sym(moved).flatMap(s => LogicError.lift(Kernel.eqMp(s, one))))
            contra <- rules.notElim(zeroOne, zeroIsOne)
            out <- rules.falsityElim(wanted, contra)
          } yield out
        a0 <- assumed(s"$a = 0"); a1 <- assumed(s"$a = 1")
        b0 <- assumed(s"$b = 0"); b1 <- assumed(s"$b = 1")
        c00 <- same(a0._2, b0._2); c01 <- mixed(a0._2, b1._2)
        c10 <- mixed(a1._2, b0._2); c11 <- same(a1._2, b1._2)
        whenA0 <- rules.disjElim(eb, c00, c01)
        whenA1 <- rules.disjElim(eb, c10, c11)
        out <- rules.disjElim(ea, whenA0, whenA1)
      } yield out

    /** Modulo `2^k` the map is injective: equal values come from equal residues. */
    def gInjective: R[Kernel.Thm] =
      mapRule { _ =>
        val (kv, pv, qv, mv, nv) = (Term.variable("kb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool),
          Term.variable("mb", Numbers), Term.variable("nb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"
        def claim(K: String) =
          s"NUM_MOD ($G $Pb $Qb (mb:num)) (NUM_POW 2 ($K)) = NUM_MOD ($G pb qb (nb:num)) (NUM_POW 2 ($K)) ==> " +
            s"NUM_MOD mb (NUM_POW 2 ($K)) = NUM_MOD nb (NUM_POW 2 ($K))"
        for {
          step <- underMap("G_STEP")
          body <- prop(s"!pb:bool. !qb:bool. !mb:num. !nb:num. ${claim("kb:num")}")
          proved <- induct(kv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                out <- underHyps(goal)((_, c) => rewriting(Seq(powZero, k("MOD_ONE")), c)(byBeta)).flatMap(gen(_, pv, qv, mv, nv))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name); val M = s"NUM_POW 2 $K"; val P2 = s"NUM_POW 2 (SUC $K)"
              def E(z: String) = s"(NUM_MOD ($z:num) 2 = 1)"
              def D(z: String) = s"NUM_DIV ($z:num) 2"
              def C(z: String) = s"COND (~(($Pb \\/ $Qb) = ${E(z)})) (1:num) 0"
              def X(z: String) = s"$G ${E(z)} $Pb (${D(z)})"
              for {
                goal <- prop(claim(s"SUC $K"))
                out <- underHyps(goal) { (hs_, _) =>
                  val h = hs_.head
                  for {
                    sides <- Seq("mb", "nb").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, z) =>
                      for {
                        done <- acc
                        atZ <- at(step, s"$G $Pb $Qb ($z:num) = ${C(z)} + 2 * ${X(z)}")
                        swap <- num(s"${C(z)} + 2 * ${X(z)} = 2 * ${X(z)} + ${C(z)}")
                        small <- at(k("COND_BELOW_TWO"), s"${C(z)} < (2:num)")
                        dbl <- at(k("MOD_DOUBLE"), s"${C(z)} < (2:num) ==> NUM_MOD (2 * ${X(z)} + ${C(z)}) ($P2) = 2 * NUM_MOD (${X(z)}) ($M) + ${C(z)}").flatMap(mp(_, small))
                      } yield done ++ Vector(atZ, swap, dbl, small)
                    }
                    reduced <- Seq(0, 1, 2, 4, 5, 6).foldLeft[R[Kernel.Thm]](Right(h))((acc, ix) => acc.flatMap(th => rw(sides(ix), th)))
                    unique <- at(fact("NUM_DIVISION_UNIQUE"),
                      s"2 * NUM_MOD (${X("mb")}) ($M) + ${C("mb")} = 2 * NUM_MOD (${X("nb")}) ($M) + ${C("nb")} /\\ ${C("mb")} < (2:num) /\\ ${C("nb")} < (2:num) ==> " +
                        s"NUM_MOD (${X("mb")}) ($M) = NUM_MOD (${X("nb")}) ($M) /\\ ${C("mb")} = ${C("nb")}")
                    parts <- conjs(reduced, sides(3), sides(7)).flatMap(mp(unique, _)).flatMap(split)
                    (xs, cs) = (parts(0), parts(1))
                    bits <- for {
                      wanted <- prop(s"${E("mb")} = ${E("nb")}")
                      atoms <- Seq("pb:bool", "qb:bool", E("mb"), E("nb")).foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
                      out <- byCases(atoms)(lits => g =>
                        tauto(lits, g).orElse(
                          for {
                            values <- conditionals(cs.conclusion).distinct.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, c) =>
                              for { done <- acc; vv <- condValue(c, lits) } yield done ++ vv.toVector
                            }
                            decided <- values.foldLeft[R[Kernel.Thm]](Right(cs))((acc, e) => acc.flatMap(rw(e, _)))
                            zeroOne <- zeroNotOne
                            contra <- rules.notElim(zeroOne, decided).orElse(Conv.sym(decided).flatMap(rules.notElim(zeroOne, _)))
                            out <- rules.falsityElim(g, contra)
                          } yield out))(wanted)
                    } yield out
                    aligned <- Conv.sym(bits).flatMap(rw(_, xs))
                    ih <- at(hyp, s"NUM_MOD (${X("mb")}) ($M) = NUM_MOD ($G ${E("mb")} $Pb (${D("nb")})) ($M) ==> NUM_MOD (${D("mb")}) ($M) = NUM_MOD (${D("nb")}) ($M)")
                    halves <- mp(ih, aligned)
                    residues <- Seq("mb", "nb").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, z) =>
                      for {
                        done <- acc
                        dm <- at(fact("NUM_DIV_MOD"), s"2 * ${D(z)} + NUM_MOD ($z:num) 2 = $z")
                        lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD ($z:num) 2 < 2").flatMap(mp(_, t2)))
                        dbl <- at(k("MOD_DOUBLE"), s"NUM_MOD ($z:num) 2 < 2 ==> NUM_MOD (2 * ${D(z)} + NUM_MOD $z 2) ($P2) = 2 * NUM_MOD (${D(z)}) ($M) + NUM_MOD $z 2")
                          .flatMap(mp(_, lt)).flatMap(rw(dm, _))
                      } yield done ++ Vector(dbl, lt)
                    }
                    lows <- equalFromBits("NUM_MOD (mb:num) 2", "NUM_MOD (nb:num) 2", residues(1), residues(3), bits)
                    out <- rewriting(Seq(residues(0), residues(2), halves, lows), goalConclusion(goal))(byBeta)
                  } yield out
                }.flatMap(gen(_, pv, qv, mv, nv))
              } yield out
            }
          )
        } yield proved
      }

    /** Modulo `2^k` the `t`-th iterate is injective. */
    def mapInjective: R[Kernel.Thm] =
      mapRule { hs =>
        val (tv, kv, mv, nv) = (Term.variable("tb", Numbers), Term.variable("kb", Numbers), Term.variable("mb", Numbers), Term.variable("nb", Numbers))
        val M = "NUM_POW 2 (kb:num)"
        def claim(T: String) =
          s"NUM_MOD ($It (mb:num) ($T)) ($M) = NUM_MOD ($It (nb:num) ($T)) ($M) ==> NUM_MOD mb ($M) = NUM_MOD nb ($M)"
        for {
          injective <- underMap("G_INJECTIVE")
          body <- prop(s"!kb:num. !mb:num. !nb:num. ${claim("tb:num")}")
          proved <- induct(tv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                out <- underHyps(goal)((h, c) => rw(hs(2), h.head).flatMap(landsOn(_)(c))).flatMap(gen(_, kv, mv, nv))
              } yield out,
            (kk, hyp, _) => {
              val T = v(kk.name)
              val X = s"$It (mb:num) $T"; val Y = s"$It (nb:num) $T"
              for {
                goal <- prop(claim(s"SUC $T"))
                out <- underHyps(goal) { (h, c) =>
                  for {
                    opened <- rw(hs(3), h.head)
                    lower <- at(injective, s"NUM_MOD ($G F F ($X)) ($M) = NUM_MOD ($G F F ($Y)) ($M) ==> NUM_MOD ($X) ($M) = NUM_MOD ($Y) ($M)")
                      .flatMap(mp(_, opened))
                    ih <- at(hyp, s"NUM_MOD ($X) ($M) = NUM_MOD ($Y) ($M) ==> NUM_MOD (mb:num) ($M) = NUM_MOD (nb:num) ($M)").flatMap(mp(_, lower))
                    out <- landsOn(ih)(c)
                  } yield out
                }.flatMap(gen(_, kv, mv, nv))
              } yield out
            }
          )
          out <- spec(proved, tv, kv, mv, nv).flatMap(gen(_, tv, kv, mv, nv))
        } yield out
      }

    /** `g F F 0 = 0`. */
    def gZero: R[Kernel.Thm] =
      mapRule { _ =>
        for {
          step <- underMap("G_STEP")
          at0 <- at(step, s"$G F F 0 = COND (~((F \\/ F) = (NUM_MOD 0 2 = 1))) 1 0 + 2 * $G (NUM_MOD 0 2 = 1) F (NUM_DIV 0 2)")
          t2 <- two
          small <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(split)
          zeroF <- zeroOneFalse
          opened <- rw(small(1), at0).flatMap(rw(small(0), _)).flatMap(rw(zeroF, _)).flatMap(decidedIn(_, Seq.empty))
          out <- numLinText(Seq(opened), s"$G F F 0 = 0")
        } yield out
      }

    /** A value of `2^L` to `2^(SUC L)` goes to `2^(L + 2)` to `2^(L + 3)`: each step adds two bits. */
    def gLength: R[Kernel.Thm] =
      mapRule { _ =>
        val (lv, pv, qv, nv) = (Term.variable("lb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("nb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val N = "(nb:num)"
        def pw(e: String) = s"NUM_POW 2 ($e)"
        def claim(L: String) =
          s"${pw(L)} <= $N /\\ $N < ${pw(s"SUC ($L)")} ==> ${pw(s"SUC (SUC ($L))")} <= $G $Pb $Qb $N /\\ $G $Pb $Qb $N < ${pw(s"SUC (SUC (SUC ($L)))")}"
        def powSuc(e: String) = at(fact("NUM_POW_SUC"), s"${pw(s"SUC ($e)")} = ${pw(e)} * 2")
        for {
          step <- underMap("G_STEP")
          zero <- underMap("G_ZERO")
          body <- prop(s"!pb:bool. !qb:bool. !nb:num. ${claim("lb:num")}")
          proved <- induct(lv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                out <- underHyps(goal) { (hs_, c) =>
                  for {
                    bounds <- split(hs_.head)
                    p0 <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                    p1 <- powSuc("0"); p2 <- powSuc("SUC 0"); p3 <- powSuc("SUC (SUC 0)")
                    one <- numLin(bounds ++ Seq(p0, p1), prop(s"$N = 1").toOption.get)
                    t2 <- two
                    oneLt <- numLinText(Seq.empty, "(1:num) < 2")
                    m1 <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneLt)).flatMap(split)
                    m0 <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(split)
                    zeroF <- zeroOneFalse; oneT <- oneOneTrue
                    s1 <- at(step, s"$G $Pb $Qb 1 = COND (~(($Pb \\/ $Qb) = (NUM_MOD 1 2 = 1))) 1 0 + 2 * $G (NUM_MOD 1 2 = 1) $Pb (NUM_DIV 1 2)")
                      .flatMap(rw(m1(1), _)).flatMap(rw(m1(0), _)).flatMap(rw(oneT, _))
                    s2 <- at(step, s"$G T $Pb 0 = COND (~((T \\/ $Pb) = (NUM_MOD 0 2 = 1))) 1 0 + 2 * $G (NUM_MOD 0 2 = 1) T (NUM_DIV 0 2)")
                      .flatMap(rw(m0(1), _)).flatMap(rw(m0(0), _)).flatMap(rw(zeroF, _)).flatMap(decidedIn(_, Seq.empty))
                    s3 <- at(step, s"$G F T 0 = COND (~((F \\/ T) = (NUM_MOD 0 2 = 1))) 1 0 + 2 * $G (NUM_MOD 0 2 = 1) F (NUM_DIV 0 2)")
                      .flatMap(rw(m0(1), _)).flatMap(rw(m0(0), _)).flatMap(rw(zeroF, _)).flatMap(decidedIn(_, Seq.empty))
                    small <- at(k("COND_BELOW_TWO"), s"COND (~(($Pb \\/ $Qb) = T)) 1 0 < (2:num)")
                    out <- rewriting(Seq(one), c)(numLin(Seq(s1, s2, s3, zero, small, p0, p1, p2, p3), _))
                  } yield out
                }.flatMap(gen(_, pv, qv, nv))
              } yield out,
            (kk, hyp, _) => {
              val L = v(kk.name)
              val E = s"(NUM_MOD $N 2 = 1)"; val D = s"NUM_DIV $N 2"
              val C = s"COND (~(($Pb \\/ $Qb) = $E)) (1:num) 0"; val X = s"$G $E $Pb ($D)"
              for {
                goal <- prop(claim(s"SUC $L"))
                out <- underHyps(goal) { (hs_, c) =>
                  for {
                    bounds <- split(hs_.head)
                    (low, high) = (bounds(0), bounds(1))
                    st <- at(step, s"$G $Pb $Qb $N = $C + 2 * $X")
                    dm <- at(fact("NUM_DIV_MOD"), s"2 * $D + NUM_MOD $N 2 = $N")
                    e2 <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD $N 2 < 2").flatMap(mp(_, t2)))
                    q1 <- powSuc(L); q2 <- powSuc(s"SUC $L"); q3 <- powSuc(s"SUC (SUC $L)"); q4 <- powSuc(s"SUC (SUC (SUC $L))")
                    facts = Seq(dm, e2, q1, q2, q3, q4)
                    lowD <- for {
                      a <- assumed(s"$D < ${pw(L)}")
                      under <- numLin(facts :+ a._2, prop(s"$N < ${pw(s"SUC $L")}").toOption.get)
                      not <- at(fact("NUM_LT_NOT_LE"), s"$N < ${pw(s"SUC $L")} ==> ~(${pw(s"SUC $L")} <= $N)").flatMap(mp(_, under))
                      contra <- rules.notElim(not, low)
                      refuted <- rules.notIntro(a._1, contra)
                      out <- at(fact("NUM_LE_OF_NOT_LT"), s"~($D < ${pw(L)}) ==> ${pw(L)} <= $D").flatMap(mp(_, refuted))
                    } yield out
                    highD <- for {
                      a <- assumed(s"${pw(s"SUC $L")} <= $D")
                      over <- numLin(facts :+ a._2, prop(s"${pw(s"SUC (SUC $L)")} <= $N").toOption.get)
                      not <- at(fact("NUM_LT_NOT_LE"), s"$N < ${pw(s"SUC (SUC $L)")} ==> ~(${pw(s"SUC (SUC $L)")} <= $N)").flatMap(mp(_, high))
                      contra <- rules.notElim(not, over)
                      refuted <- rules.notIntro(a._1, contra)
                      out <- at(k("NUM_NOT_LE"), s"~(${pw(s"SUC $L")} <= $D) ==> $D < ${pw(s"SUC $L")}").flatMap(mp(_, refuted))
                    } yield out
                    ih <- at(hyp, s"${pw(L)} <= $D /\\ $D < ${pw(s"SUC $L")} ==> ${pw(s"SUC (SUC $L)")} <= $X /\\ $X < ${pw(s"SUC (SUC (SUC $L))")}")
                      .flatMap(i => conj(lowD, highD).flatMap(mp(i, _)))
                    small <- at(k("COND_BELOW_TWO"), s"$C < (2:num)")
                    out <- rewriting(Seq(st), c)(numLin(Seq(ih, small) ++ facts, _))
                  } yield out
                }.flatMap(gen(_, pv, qv, nv))
              } yield out
            }
          )
        } yield proved
      }

    /** The row at time `t` has exactly `2 t + 1` bits. */
    def mapRowLength: R[Kernel.Thm] =
      mapRule { hs =>
        val tv = Term.variable("tb", Numbers)
        def pw(e: String) = s"NUM_POW 2 ($e)"
        def claim(T: String) = s"${pw(s"2 * ($T)")} <= $It 1 ($T) /\\ $It 1 ($T) < ${pw(s"2 * ($T) + 1")}"
        for {
          length <- underMap("G_LENGTH")
          body <- prop(claim("(tb:num)"))
          proved <- induct(tv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                start <- at(hs(2), s"$It 1 0 = 1")
                z <- num("2 * 0 = (0:num)")
                o <- numLinText(Seq.empty, "(0:num) + 1 = SUC 0")
                p0 <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                p1 <- at(fact("NUM_POW_SUC"), "NUM_POW 2 (SUC 0) = NUM_POW 2 0 * 2")
                out <- rewriting(Seq(start, z, o), goal)(numLin(Seq(p0, p1), _))
              } yield out,
            (kk, hyp, _) => {
              val T = v(kk.name); val X = s"$It 1 $T"
              for {
                goal <- prop(claim(s"SUC $T"))
                succ <- numLinText(Seq.empty, s"2 * $T + 1 = SUC (2 * $T)")
                ih <- rw(succ, hyp)
                grown <- at(length, s"${pw(s"2 * $T")} <= $X /\\ $X < ${pw(s"SUC (2 * $T)")} ==> " +
                  s"${pw(s"SUC (SUC (2 * $T))")} <= $G F F ($X) /\\ $G F F ($X) < ${pw(s"SUC (SUC (SUC (2 * $T)))")}").flatMap(mp(_, ih))
                a <- numLinText(Seq.empty, s"2 * SUC $T = SUC (SUC (2 * $T))")
                b <- numLinText(Seq.empty, s"SUC (SUC (2 * $T)) + 1 = SUC (SUC (SUC (2 * $T)))")
                out <- rewriting(Seq(hs(3), b, a), goal)(landsOn(grown))
              } yield out
            }
          )
        } yield proved
      }

    /** Over the residues modulo `2^(SUC j)`, bit `j` of the `t`-th iterate is on as often as off. */
    def mapBalanced: R[Kernel.Thm] =
      mapRule { _ =>
        val (tv, jv) = (Term.variable("tb", Numbers), Term.variable("jb", Numbers))
        val T = "(tb:num)"; val J = "(jb:num)"; val P = s"NUM_POW 2 $J"; val P2 = s"NUM_POW 2 (SUC $J)"
        def f(n: String) = sign(bit(J, s"$It ($n) $T"))
        for {
          residues <- underMap("RULE_THIRTY_MAP_RESIDUES")
          injective <- underMap("RULE_THIRTY_MAP_INJECTIVE")
          goal <- prop(s"Sum (\\n:num. ${f("n")}) ($P2) = 0")
          double <- for {
            s1 <- at(fact("NUM_POW_SUC"), s"$P2 = $P * 2")
            s2 <- num(s"$P * 2 = $P + $P")
            out <- trans(s1, s2)
          } yield out
          halves <- at(fact("SUM_HALVES"), s"Sum (\\n:num. ${f("n")}) ($P + $P) = Sum (\\n:num. ${f("n")}) ($P) + Sum (\\m:num. ${f(s"$P + m")}) ($P)")
          added <- at(fact("SUM_ADD"), s"Sum (\\m:num. ${f("m")} + ${f(s"$P + m")}) ($P) = Sum (\\n:num. ${f("n")}) ($P) + Sum (\\m:num. ${f(s"$P + m")}) ($P)")
            .flatMap(Conv.sym)
          pairedT <- term(s"Sum (\\m:num. ${f("m")} + ${f(s"$P + m")}) ($P)", Reals)
          paired <- belowBound(pairedT, "\\m:num. (0:real)", P) { (m, mBelow) =>
            val A = s"$It $m $T"; val B = s"$It ($P + $m) $T"
            for {
              own <- at(fact("NUM_DIV_MOD_BELOW"), s"$m < $P ==> NUM_DIV $m ($P) = 0 /\\ NUM_MOD $m ($P) = $m").flatMap(mp(_, mBelow)).flatMap(rules.conjElim2)
              shifted <- at(fact("NUM_DIV_MOD_STEP"), s"$m < $P ==> NUM_DIV ($P + $m) ($P) = SUC 0 /\\ NUM_MOD ($P + $m) ($P) = $m").flatMap(mp(_, mBelow)).flatMap(rules.conjElim2)
              rA <- at(residues, s"NUM_MOD ($A) ($P) = NUM_MOD ($It (NUM_MOD $m ($P)) $T) ($P)").flatMap(rw(own, _))
              rB <- at(residues, s"NUM_MOD ($B) ($P) = NUM_MOD ($It (NUM_MOD ($P + $m) ($P)) $T) ($P)").flatMap(rw(shifted, _))
              lowSame <- Conv.sym(rB).flatMap(trans(rA, _))
              apart <- for {
                held <- assumed(s"(${bit(J, A)}) = (${bit(J, B)})")
                splitA <- at(k("MOD_EQ_SPLIT"), s"(NUM_MOD ($A) ($P2) = NUM_MOD ($B) ($P2)) = (NUM_MOD ($A) ($P) = NUM_MOD ($B) ($P) /\\ ((${bit(J, A)}) = (${bit(J, B)})))")
                agreeHigh <- conj(lowSame, held._2).flatMap(c => Conv.sym(splitA).flatMap(s => LogicError.lift(Kernel.eqMp(s, c))))
                starts <- at(injective, s"NUM_MOD ($A) ($P2) = NUM_MOD ($B) ($P2) ==> NUM_MOD $m ($P2) = NUM_MOD ($P + $m) ($P2)").flatMap(mp(_, agreeHigh))
                splitS <- at(k("MOD_EQ_SPLIT"), s"(NUM_MOD $m ($P2) = NUM_MOD ($P + $m) ($P2)) = (NUM_MOD $m ($P) = NUM_MOD ($P + $m) ($P) /\\ ((${bit(J, m)}) = (${bit(J, s"$P + $m")})))")
                bitsSame <- LogicError.lift(Kernel.eqMp(splitS, starts)).flatMap(rules.conjElim2)
                off <- at(k("BIT_ABOVE"), s"$m < $P ==> ~(${bit(J, m)})").flatMap(mp(_, mBelow))
                on <- at(k("BIT_TOP"), s"$m < $P ==> ${bit(J, s"$P + $m")}").flatMap(mp(_, mBelow))
                falsity <- prop("F")
                contra <- tauto(Seq(bitsSame, off, on), falsity)
                out <- rules.notIntro(held._1, contra)
              } yield out
              atoms <- Seq(bit(J, A), bit(J, B)).foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
            } yield (Seq.empty, Seq(apart), atoms)
          }
          none <- at(fact("SUM_OF_ZERO"), s"Sum (\\m:num. 0) ($P) = 0")
          chain <- trans(halves, added, paired, none)
          out <- rewriting(Seq(double), goal)(landsOn(chain)).flatMap(gen(_, tv, jv))
        } yield out
      }

    /** Bit `j` of the `t`-th iterate as the Walsh series of its own transform over the `j + 1` low bits of the start. */
    def mapWalshForm: R[Kernel.Thm] =
      mapRule { _ =>
        val (tv, jv, nv) = (Term.variable("tb", Numbers), Term.variable("jb", Numbers), Term.variable("nb", Numbers))
        val T = "(tb:num)"; val J = "(jb:num)"; val N = "(nb:num)"; val K = s"SUC $J"; val M = s"NUM_POW 2 ($K)"
        def cell(n: String) = sign(bit(J, s"$It ($n) $T"))
        val Wt = (s: String) => s"Sum (\\y:num. ${cell("y")} * ${chi(s, "y", K)}) ($M) / real_of_num ($M)"
        for {
          residues <- underMap("RULE_THIRTY_MAP_RESIDUES")
          fn <- term(s"\\y:num. ${cell("y")}", Type.fun(Numbers, Reals))
          atCell <- rules.specPrefix(k("WALSH_INVERSION"), List(fn)).flatMap(beta)
          inverted <- at(atCell, s"${cell(s"NUM_MOD $N ($M)")} = Sum (\\s:num. ${Wt("s")} * ${chi("s", N, K)}) ($M)")
          below <- numLinText(Seq.empty, s"$J < $K")
          r <- at(residues, s"NUM_MOD ($It $N $T) ($M) = NUM_MOD ($It (NUM_MOD $N ($M)) $T) ($M)")
          m1 <- at(k("BIT_OF_MOD"), s"$J < $K ==> ((${bit(J, s"NUM_MOD ($It $N $T) ($M)")}) = (${bit(J, s"$It $N $T")}))").flatMap(mp(_, below))
          m2 <- at(k("BIT_OF_MOD"), s"$J < $K ==> ((${bit(J, s"NUM_MOD ($It (NUM_MOD $N ($M)) $T) ($M)")}) = (${bit(J, s"$It (NUM_MOD $N ($M)) $T")}))").flatMap(mp(_, below))
          same <- rw(r, m1).flatMap(a => Conv.sym(a).flatMap(trans(_, m2))).flatMap(Conv.sym)
          out <- rw(same, inverted).flatMap(gen(_, tv, jv, nv))
        } yield out
      }

    /**
     * The map and its iterate exist, so the theorems over their equations are not vacuous. The map is
     * built with a counter: `fn d` halves its argument `d` times and is right on every argument below
     * `2^d`, it stops changing once `2^d` passes the argument, and `g p q n = fn n p q n`.
     */
    def mapExists: R[Kernel.Thm] = {
      val Fn = "(fn:num->bool->bool->num->num)"
      val Base = "\\p:bool. \\q:bool. \\n:num. COND (p \\/ q) 1 0 + 2 * COND p 1 0"
      val Stepper = "\\h:bool->bool->num->num. \\d:num. \\p:bool. \\q:bool. \\n:num. " +
        "COND (NUM_MOD n 2 = 0) (COND (p \\/ q) 1 0 + 2 * h F p (NUM_DIV n 2)) (COND (p \\/ q) 0 1 + 2 * h T p (NUM_DIV n 2))"
      val (dv, ev, pv, qv, nv, mv, tv) = (Term.variable("db", Numbers), Term.variable("eb", Numbers), Term.variable("pb", Type.Bool),
        Term.variable("qb", Type.Bool), Term.variable("nb", Numbers), Term.variable("mb", Numbers), Term.variable("tb", Numbers))
      val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val N = "(nb:num)"; val Mb = "(mb:num)"
      for {
        recursive <- Right(Kernel.instType(Map("a" -> Steps), recursion))
        base <- term(Base, Steps)
        stepper <- term(Stepper, Type.fun(Steps, Type.fun(Numbers, Steps)))
        made <- spec(recursive, base, stepper)
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            atZero <- Conv.apThm(parts(0), pv).flatMap(Conv.apThm(_, qv)).flatMap(Conv.apThm(_, nv)).flatMap(beta).flatMap(gen(_, pv, qv, nv))
            atSuc <- spec(parts(1), dv).flatMap(Conv.apThm(_, pv)).flatMap(Conv.apThm(_, qv)).flatMap(Conv.apThm(_, nv)).flatMap(beta)
              .flatMap(gen(_, dv, pv, qv, nv))
            t2 <- two
            m0 <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(split)
            powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
            // one more halving changes nothing below 2^d
            stable <- for {
              body <- prop(s"!pb:bool. !qb:bool. !nb:num. nb < NUM_POW 2 (db:num) ==> $Fn (SUC db) pb qb nb = $Fn db pb qb nb")
              out <- induct(dv, body)(
                _ =>
                  for {
                    goal <- prop(s"$N < NUM_POW 2 0 ==> $Fn (SUC 0) $Pb $Qb $N = $Fn 0 $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        zero <- numLin(Seq(h.head, powZero), prop(s"$N = 0").toOption.get)
                        out <- rewriting(Seq(zero, atSuc, atZero) ++ m0, c)(byCases(List(pv, qv))(lits => deciding(lits)(numClose)))
                      } yield out
                    }.flatMap(gen(_, pv, qv, nv))
                  } yield out,
                (kk, hyp, _) => {
                  val D = v(kk.name); val H = s"NUM_DIV $N 2"
                  for {
                    goal <- prop(s"$N < NUM_POW 2 (SUC $D) ==> $Fn (SUC (SUC $D)) $Pb $Qb $N = $Fn (SUC $D) $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        dm <- at(fact("NUM_DIV_MOD"), s"2 * $H + NUM_MOD $N 2 = $N")
                        ps <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $D) = NUM_POW 2 $D * 2")
                        halfBelow <- for {
                          a <- assumed(s"NUM_POW 2 $D <= $H")
                          over <- numLin(Seq(a._2, dm, ps), prop(s"NUM_POW 2 (SUC $D) <= $N").toOption.get)
                          not <- at(fact("NUM_LT_NOT_LE"), s"$N < NUM_POW 2 (SUC $D) ==> ~(NUM_POW 2 (SUC $D) <= $N)").flatMap(mp(_, h.head))
                          refuted <- rules.notElim(not, over).flatMap(rules.notIntro(a._1, _))
                          out <- at(k("NUM_NOT_LE"), s"~(NUM_POW 2 $D <= $H) ==> $H < NUM_POW 2 $D").flatMap(mp(_, refuted))
                        } yield out
                        left <- at(atSuc, s"$Fn (SUC (SUC $D)) $Pb $Qb $N = COND (NUM_MOD $N 2 = 0) (COND ($Pb \\/ $Qb) 1 0 + 2 * $Fn (SUC $D) F $Pb ($H)) (COND ($Pb \\/ $Qb) 0 1 + 2 * $Fn (SUC $D) T $Pb ($H))")
                        right <- at(atSuc, s"$Fn (SUC $D) $Pb $Qb $N = COND (NUM_MOD $N 2 = 0) (COND ($Pb \\/ $Qb) 1 0 + 2 * $Fn $D F $Pb ($H)) (COND ($Pb \\/ $Qb) 0 1 + 2 * $Fn $D T $Pb ($H))")
                        ihF <- at(hyp, s"$H < NUM_POW 2 $D ==> $Fn (SUC $D) F $Pb ($H) = $Fn $D F $Pb ($H)").flatMap(mp(_, halfBelow))
                        ihT <- at(hyp, s"$H < NUM_POW 2 $D ==> $Fn (SUC $D) T $Pb ($H) = $Fn $D T $Pb ($H)").flatMap(mp(_, halfBelow))
                        out <- rewriting(Seq(left, right, ihF, ihT), c)(byBeta)
                      } yield out
                    }.flatMap(gen(_, pv, qv, nv))
                  } yield out
                }
              )
            } yield out
            // and so no number of further halvings does
            settled <- for {
              body <- prop(s"!db:num. !pb:bool. !qb:bool. !nb:num. nb < NUM_POW 2 db ==> $Fn (db + (eb:num)) pb qb nb = $Fn db pb qb nb")
              out <- induct(ev, body)(
                _ =>
                  for {
                    goal <- prop(s"(nb:num) < NUM_POW 2 (db:num) ==> $Fn (db + 0) $Pb $Qb nb = $Fn db $Pb $Qb nb")
                    plus <- at(fact("NUM_ADD_ZERO"), "(db:num) + 0 = db")
                    out <- underHyps(goal)((_, c) => rewriting(Seq(plus), c)(byBeta)).flatMap(gen(_, dv, pv, qv, nv))
                  } yield out,
                (kk, hyp, _) => {
                  val E = v(kk.name); val Db = "(db:num)"
                  for {
                    goal <- prop(s"$N < NUM_POW 2 $Db ==> $Fn ($Db + SUC $E) $Pb $Qb $N = $Fn $Db $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        succ <- at(fact("NUM_ADD_SUC"), s"$Db + SUC $E = SUC ($Db + $E)")
                        powAdd <- at(fact("NUM_POW_ADD"), s"NUM_POW 2 ($Db + $E) = NUM_POW 2 $Db * NUM_POW 2 $E")
                        pos <- at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < NUM_POW 2 $E").flatMap(mp(_, t2))
                        one <- numLinText(Seq(pos), s"1 <= NUM_POW 2 $E")
                        mono <- at(fact("NUM_MUL_MONOTONE"), s"1 <= NUM_POW 2 $E ==> NUM_POW 2 $Db * 1 <= NUM_POW 2 $Db * NUM_POW 2 $E").flatMap(mp(_, one))
                        unit <- num(s"NUM_POW 2 $Db * 1 = NUM_POW 2 $Db")
                        wider <- numLin(Seq(h.head, powAdd, mono, unit), prop(s"$N < NUM_POW 2 ($Db + $E)").toOption.get)
                        once <- at(stable, s"$N < NUM_POW 2 ($Db + $E) ==> $Fn (SUC ($Db + $E)) $Pb $Qb $N = $Fn ($Db + $E) $Pb $Qb $N").flatMap(mp(_, wider))
                        rest <- at(hyp, s"$N < NUM_POW 2 $Db ==> $Fn ($Db + $E) $Pb $Qb $N = $Fn $Db $Pb $Qb $N").flatMap(mp(_, h.head))
                        out <- rewriting(Seq(succ, once, rest), c)(byBeta)
                      } yield out
                    }.flatMap(gen(_, dv, pv, qv, nv))
                  } yield out
                }
              )
            } yield out
            fuel <- at(k("BELOW_POWER"), s"$Mb < NUM_POW 2 $Mb")
            gTerm <- term(s"\\p:bool. \\q:bool. \\n:num. $Fn n p q n", Steps)
            apart <- zeroNotOne
            oneNotZero <- for { h <- assumed("(1:num) = 0"); s <- Conv.sym(h._2); c <- rules.notElim(apart, s); out <- rules.notIntro(h._1, c) } yield out
            evenClause <- for {
              goal <- prop(s"$Fn (2 * $Mb) $Pb $Qb (2 * $Mb) = COND ($Pb \\/ $Qb) 1 0 + 2 * $Fn $Mb F $Pb $Mb")
              mT <- prop(s"$Mb = 0")
              isZero <- for {
                h <- assumed(s"$Mb = 0")
                twice <- num("2 * 0 = (0:num)")
                out <- rewriting(Seq(h._2, twice, atZero), goal)(byCases(List(pv, qv))(lits => deciding(lits)(numClose)))
              } yield out
              nonZero <- for {
                h <- assumed(s"~($Mb = 0)")
                pos <- positiveOf(h._2, Mb)
                le <- numLinText(Seq(pos), s"1 <= $Mb")
                sub <- at(fact("NUM_REAL_SUB"), s"1 <= $Mb ==> real_of_num (NUM_SUB $Mb 1) = real_of_num $Mb - real_of_num 1").flatMap(mp(_, le))
                fuelEq <- numLinText(Seq(sub), s"SUC ($Mb + NUM_SUB $Mb 1) = 2 * $Mb")
                opened <- at(atSuc, s"$Fn (SUC ($Mb + NUM_SUB $Mb 1)) $Pb $Qb (2 * $Mb) = COND (NUM_MOD (2 * $Mb) 2 = 0) " +
                  s"(COND ($Pb \\/ $Qb) 1 0 + 2 * $Fn ($Mb + NUM_SUB $Mb 1) F $Pb (NUM_DIV (2 * $Mb) 2)) (COND ($Pb \\/ $Qb) 0 1 + 2 * $Fn ($Mb + NUM_SUB $Mb 1) T $Pb (NUM_DIV (2 * $Mb) 2))")
                  .flatMap(rw(fuelEq, _))
                mod <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mb + 0) 2 = NUM_MOD 0 2").flatMap(e => num(s"2 * $Mb + 0 = 2 * $Mb").flatMap(rw(_, e))).flatMap(rw(m0(1), _))
                div <- for {
                  eq <- num(s"2 * $Mb = 2 * $Mb + 0")
                  u <- at(fact("NUM_DIV_MOD_UNIQUE"), s"2 * $Mb = 2 * $Mb + 0 /\\ (0:num) < 2 ==> $Mb = NUM_DIV (2 * $Mb) 2 /\\ 0 = NUM_MOD (2 * $Mb) 2")
                  out <- conj(eq, t2).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
                } yield out
                same <- at(settled, s"$Mb < NUM_POW 2 $Mb ==> $Fn ($Mb + NUM_SUB $Mb 1) F $Pb $Mb = $Fn $Mb F $Pb $Mb").flatMap(mp(_, fuel))
                out <- rewriting(Seq(opened, mod, div, same), goal)(deciding(Seq.empty)(numClose))
              } yield out
              out <- classical.cases(mT, isZero, nonZero).flatMap(gen(_, pv, qv, mv))
            } yield out
            oddClause <- for {
              goal <- prop(s"$Fn (2 * $Mb + 1) $Pb $Qb (2 * $Mb + 1) = COND ($Pb \\/ $Qb) 0 1 + 2 * $Fn $Mb T $Pb $Mb")
              fuelEq <- numLinText(Seq.empty, s"SUC ($Mb + $Mb) = 2 * $Mb + 1")
              opened <- at(atSuc, s"$Fn (SUC ($Mb + $Mb)) $Pb $Qb (2 * $Mb + 1) = COND (NUM_MOD (2 * $Mb + 1) 2 = 0) " +
                s"(COND ($Pb \\/ $Qb) 1 0 + 2 * $Fn ($Mb + $Mb) F $Pb (NUM_DIV (2 * $Mb + 1) 2)) (COND ($Pb \\/ $Qb) 0 1 + 2 * $Fn ($Mb + $Mb) T $Pb (NUM_DIV (2 * $Mb + 1) 2))")
                .flatMap(rw(fuelEq, _))
              oneLt <- numLinText(Seq.empty, "(1:num) < 2")
              m1 <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneLt)).flatMap(split)
              mod <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mb + 1) 2 = NUM_MOD 1 2").flatMap(rw(m1(1), _))
              div <- for {
                u <- at(fact("NUM_DIV_MOD_UNIQUE"), s"2 * $Mb + 1 = 2 * $Mb + 1 /\\ (1:num) < 2 ==> $Mb = NUM_DIV (2 * $Mb + 1) 2 /\\ 1 = NUM_MOD (2 * $Mb + 1) 2")
                refl <- term(s"2 * $Mb + 1", Numbers).map(Conv.refl)
                out <- conj(refl, oneLt).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
              } yield out
              double <- num(s"$Mb + $Mb = 2 * $Mb")
              same <- at(settled, s"$Mb < NUM_POW 2 $Mb ==> $Fn ($Mb + $Mb) T $Pb $Mb = $Fn $Mb T $Pb $Mb").flatMap(mp(_, fuel))
              out <- rewriting(Seq(opened, mod, div, same), goal)(deciding(Seq(oneNotZero))(numClose)).flatMap(gen(_, pv, qv, mv))
            } yield out
            // the iterate, by the recursion theorem at num -> num
            iterRec <- Right(Kernel.instType(Map("a" -> Type.fun(Numbers, Numbers)), recursion))
            idMap <- term("\\n:num. n", Type.fun(Numbers, Numbers))
            iterStep <- term(s"\\f:num->num. \\t:num. \\n:num. (\\p:bool. \\q:bool. \\n:num. $Fn n p q n) F F (f n)",
              Type.fun(Type.fun(Numbers, Numbers), Type.fun(Numbers, Type.fun(Numbers, Numbers))))
            madeIt <- spec(iterRec, idMap, iterStep)
            out <- choose(madeIt, "fn2") { (_, iterClauses) =>
              val Fn2 = "(fn2:num->num->num)"
              for {
                ip <- split(iterClauses)
                i0 <- Conv.apThm(ip(0), nv).flatMap(beta).flatMap(gen(_, nv))
                iS <- spec(ip(1), tv).flatMap(Conv.apThm(_, nv)).flatMap(beta).flatMap(gen(_, nv, tv))
                all <- conjs(evenClause, oddClause, i0, iS)
                itTerm <- term(s"\\n:num. \\t:num. $Fn2 t n", Iterates)
                forIt <- prop(s"?iterate:num->num->num. $MapEquations".replace(G, "(gg:bool->bool->num->num)"))
                  .flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))
                  .flatMap(pr => substitute(Map(Term.variable("gg", Steps) -> gTerm), pr))
                withIt <- introduce(forIt, itTerm, all)
                forG <- prop(StatementsMap("RULE_THIRTY_MAP_EXISTS")).flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))
                out <- introduce(forG, gTerm, withIt)
              } yield out
            }
          } yield out
        }
      } yield out
    }


    /** `m < 2^m`. */
    def belowPower: R[Kernel.Thm] = {
      val mv = Term.variable("m", Numbers)
      for {
        body <- prop("(m:num) < NUM_POW 2 m")
        out <- induct(mv, body)(
          _ =>
            for {
              p0 <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
              out <- prop("(0:num) < NUM_POW 2 0").flatMap(numLin(Seq(p0), _))
            } yield out,
          (kk, hyp, _) => {
            val M = v(kk.name)
            for {
              ps <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $M) = NUM_POW 2 $M * 2")
              out <- prop(s"SUC $M < NUM_POW 2 (SUC $M)").flatMap(numLin(Seq(hyp, ps), _))
            } yield out
          }
        )
      } yield out
    }

    /* ------------------------------------------------------------ the bridge */

    private def bit0(y: String) = s"NUM_MOD ($y) 2 = 1"

    /** `NUM_DIV x 1 = x`. */
    def divOne: R[Kernel.Thm] =
      for {
        unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
        eq <- numLinText(Seq.empty, "(x:num) = SUC 0 * x + 0")
        u <- at(fact("NUM_DIV_MOD_UNIQUE"), "(x:num) = SUC 0 * x + 0 /\\ 0 < SUC 0 ==> x = NUM_DIV x (SUC 0) /\\ 0 = NUM_MOD x (SUC 0)")
        out <- conj(eq, unit).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym).flatMap(gen(_, Term.variable("x", Numbers)))
      } yield out

    /** Bit 0 is the remainder by 2, and bit `SUC j` is bit `j` of the half. */
    def bitLow: R[Kernel.Thm] = {
      val (jv, xv) = (Term.variable("j", Numbers), Term.variable("x", Numbers))
      val X = "(x:num)"; val J = "(j:num)"
      for {
        powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
        zeroGoal <- prop(s"(${bit("0", X)}) = (${bit0(X)})")
        zero <- rewriting(Seq(powZero, k("DIV_ONE")), zeroGoal)(byBeta)
        dm <- at(fact("NUM_DIV_MOD"), s"2 * NUM_DIV $X 2 + NUM_MOD $X 2 = $X")
        lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD $X 2 < 2").flatMap(mp(_, t2)))
        half <- at(k("BIT_HALVE"), s"NUM_MOD $X 2 < 2 ==> ((${bit(s"SUC $J", s"2 * NUM_DIV $X 2 + NUM_MOD $X 2")}) = (${bit(J, s"NUM_DIV $X 2")}))")
          .flatMap(mp(_, lt)).flatMap(rw(dm, _))
        halfAll <- gen(half, jv)
        out <- conj(zero, halfAll).flatMap(gen(_, xv))
      } yield out
    }

    /** Bit 0 of the map is the XOR of bit 0 of its argument with the two bits below. */
    def gBitZero: R[Kernel.Thm] =
      mapRule { _ =>
        val (pv, qv, xv) = (Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val X = "(xb:num)"
        val E = s"(${bit0(X)})"; val C = s"COND (~(($Pb \\/ $Qb) = $E)) (1:num) 0"; val Y = s"$G $E $Pb (NUM_DIV $X 2)"
        for {
          step <- underMap("G_STEP")
          st <- at(step, s"$G $Pb $Qb $X = $C + 2 * $Y")
          swap <- num(s"$C + 2 * $Y = 2 * $Y + $C")
          low <- at(k("BIT_LOW"), s"((${bit("0", s"$G $Pb $Qb $X")}) = (${bit0(s"$G $Pb $Qb $X")})) /\\ " +
            s"(!j:num. (${bit("SUC j", s"$G $Pb $Qb $X")}) = (${bit("j", s"NUM_DIV ($G $Pb $Qb $X) 2")}))").flatMap(rules.conjElim1)
          shift <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Y + $C) 2 = NUM_MOD ($C) 2")
          goal <- prop(s"(${bit("0", s"$G $Pb $Qb $X")}) = ~(($Pb \\/ $Qb) = $E)")
          zeroF <- zeroOneFalse; oneT <- oneOneTrue
          t2 <- two; oneLt <- numLinText(Seq.empty, "(1:num) < 2")
          m0 <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(rules.conjElim2)
          m1 <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneLt)).flatMap(rules.conjElim2)
          atoms <- Seq("pb:bool", "qb:bool", bit0(X)).foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
          out <- rewriting(Seq(low), goal)(g1 => rewriting(Seq(st, swap, shift), g1)(byCases(atoms)(lits => deciding(lits)(g =>
            rewriting(Seq(m0, m1, zeroF, oneT), g)(gg => tauto(lits, gg))))))
          general <- gen(out, pv, qv, xv)
        } yield general
      }

    /** Bit `SUC j` of the map is bit `j` of the map at the half, carrying bit 0 down. */
    def gBitSuc: R[Kernel.Thm] =
      mapRule { _ =>
        val (jv, pv, qv, xv) = (Term.variable("jb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val X = "(xb:num)"; val J = "(jb:num)"
        val E = s"(${bit0(X)})"; val C = s"COND (~(($Pb \\/ $Qb) = $E)) (1:num) 0"; val Y = s"$G $E $Pb (NUM_DIV $X 2)"
        for {
          step <- underMap("G_STEP")
          st <- at(step, s"$G $Pb $Qb $X = $C + 2 * $Y")
          swap <- num(s"$C + 2 * $Y = 2 * $Y + $C")
          small <- at(k("COND_BELOW_TWO"), s"$C < (2:num)")
          half <- at(k("BIT_HALVE"), s"$C < (2:num) ==> ((${bit(s"SUC $J", s"2 * $Y + $C")}) = (${bit(J, Y)}))").flatMap(mp(_, small))
          goal <- prop(s"(${bit(s"SUC $J", s"$G $Pb $Qb $X")}) = (${bit(J, Y)})")
          out <- rewriting(Seq(st, swap, half), goal)(byBeta).flatMap(gen(_, jv, pv, qv, xv))
        } yield out
      }

    /** Two bits up, the map is Rule 30 on bits `SUC (SUC j)`, `SUC j` and `j` of its argument. */
    def gBitRule: R[Kernel.Thm] =
      mapRule { _ =>
        val (jv, pv, qv, xv) = (Term.variable("jb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        def claim(J: String, P: String, Q: String, X: String) =
          s"(${bit(s"SUC (SUC ($J))", s"$G $P $Q ($X)")}) = ~((${bit(s"SUC (SUC ($J))", X)}) = ((${bit(s"SUC ($J)", X)}) \\/ (${bit(J, X)})))"
        val X = "(xb:num)"; val H = s"NUM_DIV $X 2"; val H2 = s"NUM_DIV ($H) 2"
        val E = s"(${bit0(X)})"; val E1 = s"(${bit0(H)})"
        for {
          zero <- underMap("G_BIT_ZERO")
          succ <- underMap("G_BIT_SUC")
          body <- prop(s"!pb:bool. !qb:bool. !xb:num. ${claim("jb:num", "pb", "qb", "xb")}")
          proved <- induct(jv, body)(
            _ =>
              for {
                goal <- prop(claim("0", "(pb:bool)", "(qb:bool)", "(xb:num)"))
                a <- at(succ, s"(${bit("SUC (SUC 0)", s"$G (pb:bool) (qb:bool) $X")}) = (${bit("SUC 0", s"$G $E (pb:bool) ($H)")})")
                b <- at(succ, s"(${bit("SUC 0", s"$G $E (pb:bool) ($H)")}) = (${bit("0", s"$G $E1 $E ($H2)")})")
                c <- at(zero, s"(${bit("0", s"$G $E1 $E ($H2)")}) = ~(($E1 \\/ $E) = (${bit0(H2)}))")
                lows <- Seq(X, H, H2).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, y) =>
                  for {
                    done <- acc
                    l <- at(k("BIT_LOW"), s"((${bit("0", y)}) = (${bit0(y)})) /\\ (!j:num. (${bit("SUC j", y)}) = (${bit("j", s"NUM_DIV ($y) 2")}))").flatMap(split)
                  } yield done ++ l
                }
                out <- rewriting(Seq(a, b, c) ++ lows, goal)(g => tauto(Seq.empty, g)).flatMap(gen(_, pv, qv, xv))
              } yield out,
            (kk, hyp, _) => {
              val J = v(kk.name)
              for {
                goal <- prop(claim(s"SUC $J", "(pb:bool)", "(qb:bool)", X))
                a <- at(succ, s"(${bit(s"SUC (SUC (SUC $J))", s"$G (pb:bool) (qb:bool) $X")}) = (${bit(s"SUC (SUC $J)", s"$G $E (pb:bool) ($H)")})")
                ih <- at(hyp, claim(J, E, "(pb:bool)", H))
                low <- at(k("BIT_LOW"), s"((${bit("0", X)}) = (${bit0(X)})) /\\ (!j:num. (${bit("SUC j", X)}) = (${bit("j", H)}))")
                  .flatMap(rules.conjElim2)
                out <- rewriting(Seq(a, ih, low), goal)(byBeta).flatMap(gen(_, pv, qv, xv))
              } yield out
            }
          )
        } yield proved
      }

    /** The all-off row stays off. */
    def zeroRow: R[Kernel.Thm] =
      rule { hs =>
        val (tv, pv) = (Term.variable("tb", Numbers), Term.variable("pc", Numbers))
        val Off = "(\\q:num. F)"
        for {
          body <- prop(s"!pc:num. ~($Run $Off (tb:num) pc)")
          proved <- induct(tv, body)(
            _ =>
              for {
                goal <- prop(s"~($Run $Off 0 (pc:num))")
                out <- rewriting(Seq(hs(0)), goal)(g => betaThen(g)(gg => tauto(Seq.empty, gg))).flatMap(gen(_, pv))
              } yield out,
            (kk, hyp, _) => {
              val T = v(kk.name); val P = "(pc:num)"
              for {
                goal <- prop(s"~($Run $Off (SUC $T) $P)")
                st <- at(hs(1), s"$Run $Off (SUC $T) $P = ~($Run $Off $T $P = ($Run $Off $T ($P + 1) \\/ $Run $Off $T ($P + 2)))")
                facts <- Seq(P, s"$P + 1", s"$P + 2").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, q) =>
                  for { done <- acc; f <- at(hyp, s"~($Run $Off $T ($q))") } yield done :+ f)
                out <- rewriting(Seq(st), goal)(g => tauto(facts, g)).flatMap(gen(_, pv))
              } yield out
            }
          )
        } yield proved
      }

    /**
     * The two formulations agree: on the row whose cell `p <= k` is bit `k - p` of `n` and whose cells
     * past `k` are off, cell `(t, i)` is bit `j` of the `t`-th iterate whenever `i + j = k`.
     */
    def bridge: R[Kernel.Thm] = {
      val (tv, kv, nv, iv, jv) = (Term.variable("t", Numbers), Term.variable("k", Numbers), Term.variable("n", Numbers),
        Term.variable("i", Numbers), Term.variable("j", Numbers))
      val K = "(k:num)"; val N = "(n:num)"
      val Row = s"(\\p:num. p <= $K /\\ (${bit(s"NUM_SUB $K p", N)}))"
      def claim(T: String) = s"!i:num. !j:num. i + j = $K ==> $Run $Row ($T) i = (${bit("j", s"$It $N ($T)")})"
      for {
        ruleT <- prop(Rule); mapT <- prop(MapEquations)
        ruleH <- LogicError.lift(Kernel.assume(ruleT)); mapH <- LogicError.lift(Kernel.assume(mapT))
        hr <- split(ruleH); hm <- split(mapH)
        coneHere <- spec(k("RULE_THIRTY_CONE"), run).flatMap(mp(_, ruleH))
        zeroHere <- spec(k("ZERO_ROW"), run).flatMap(mp(_, ruleH))
        bitZero <- spec(k("G_BIT_ZERO"), gvar, itvar).flatMap(mp(_, mapH))
        bitSuc <- spec(k("G_BIT_SUC"), gvar, itvar).flatMap(mp(_, mapH))
        bitRule <- spec(k("G_BIT_RULE"), gvar, itvar).flatMap(mp(_, mapH))
        // past k the row is off at every time
        outside <- for {
          held <- assumed(s"$K < ${v("pc")}")
          offRow <- term("\\q:num. F", Rows)
          row <- term(Row, Rows)
          pcT <- nm(v("pc"))
          c0 <- rules.specAll(coneHere, List(Term.variable("tb", Numbers), pcT, row, offRow)).flatMap(beta)
          agree <- for {
            jh <- assumed(s"${v("jc")} < 2 * (tb:num) + 1")
            beyond <- numLinText(Seq(held._2), s"$K < ${v("pc")} + ${v("jc")}")
            not <- at(fact("NUM_LT_NOT_LE"), s"$K < ${v("pc")} + ${v("jc")} ==> ~(${v("pc")} + ${v("jc")} <= $K)").flatMap(mp(_, beyond))
            goal <- prop(s"(${v("pc")} + ${v("jc")} <= $K /\\ (${bit(s"NUM_SUB $K (${v("pc")} + ${v("jc")})", N)})) = F")
            out <- tauto(Seq(not), goal).flatMap(rules.disch(jh._1, _)).flatMap(gen(_, Term.variable("jc", Numbers)))
          } yield out
          same <- mp(c0, agree)
          off <- at(zeroHere, s"~($Run (\\q:num. F) (tb:num) ${v("pc")})")
          out <- Conv.sym(same).flatMap(s => rw(s, off)).flatMap(rules.disch(held._1, _)).flatMap(gen(_, Term.variable("tb", Numbers), Term.variable("pc", Numbers)))
        } yield out
        body <- prop(claim("t:num"))
        proved <- induct(tv, body)(
          _ =>
            for {
              goal <- prop(claim("0"))
              out <- underHypsAll(goal, iv, jv) { (h, c) =>
                for {
                  le <- numLinText(Seq(h), s"${v("i")} <= $K")
                  sub <- for {
                    s1 <- at(fact("NUM_ADD_SUB"), s"NUM_SUB (${v("j")} + ${v("i")}) ${v("i")} = ${v("j")}")
                    sw <- num(s"${v("j")} + ${v("i")} = ${v("i")} + ${v("j")}")
                    out <- rw(sw, s1).flatMap(rw(h, _))
                  } yield out
                  truth <- rules.eqTruthIntro(le)
                  out <- rewriting(Seq(hr(0), hm(2)), c)(g => betaThen(g)(g2 => rewriting(Seq(sub, truth), g2)(g3 => tauto(Seq.empty, g3))))
                } yield out
              }
            } yield out,
          (kk, hyp, _) => {
            val T = v(kk.name); val I = v("i"); val J = v("j"); val X = s"$It $N $T"
            for {
              goal <- prop(claim(s"SUC $T"))
              out <- underHypsAll(goal, iv, jv) { (h, c) =>
                for {
                  st <- at(hr(1), s"$Run $Row (SUC $T) $I = ~($Run $Row $T $I = ($Run $Row $T ($I + 1) \\/ $Run $Row $T ($I + 2)))")
                  self <- at(hyp, s"$I + $J = $K ==> $Run $Row $T $I = (${bit(J, X)})").flatMap(mp(_, h))
                  iter <- at(hm(3), s"$It $N (SUC $T) = $G F F ($X)")
                  small <- prop(s"$J < 2")
                  low <- for {
                    lt <- LogicError.lift(Kernel.assume(small))
                    either <- binary(J, lt)
                    zeroCase <- for {
                      z <- assumed(s"$J = 0")
                      o1 <- numLinText(Seq(h, z._2), s"$K < $I + 1"); o2 <- numLinText(Seq(h, z._2), s"$K < $I + 2")
                      off1 <- at(outside, s"$K < $I + 1 ==> ~($Run $Row $T ($I + 1))").flatMap(mp(_, o1))
                      off2 <- at(outside, s"$K < $I + 2 ==> ~($Run $Row $T ($I + 2))").flatMap(mp(_, o2))
                      b0 <- at(bitZero, s"(${bit("0", s"$G F F ($X)")}) = ~((F \\/ F) = (${bit0(X)}))")
                      l0 <- at(k("BIT_LOW"), s"((${bit("0", X)}) = (${bit0(X)})) /\\ (!j:num. (${bit("SUC j", X)}) = (${bit("j", s"NUM_DIV ($X) 2")}))").flatMap(rules.conjElim1)
                      selfZ <- rw(z._2, self)
                      out <- rewriting(Seq(z._2, st, iter, b0), c)(g => tauto(Seq(selfZ, off1, off2, l0), g))
                    } yield out
                    oneCase <- for {
                      o <- assumed(s"$J = 1")
                      one <- numLinText(Seq(o._2), s"$J = SUC 0")
                      edge <- numLinText(Seq(h, o._2), s"$I + 1 + 0 = $K")
                      o2 <- numLinText(Seq(h, o._2), s"$K < $I + 2")
                      off2 <- at(outside, s"$K < $I + 2 ==> ~($Run $Row $T ($I + 2))").flatMap(mp(_, o2))
                      nb <- at(hyp, s"$I + 1 + 0 = $K ==> $Run $Row $T ($I + 1) = (${bit("0", X)})").flatMap(mp(_, edge))
                      b1 <- at(bitSuc, s"(${bit("SUC 0", s"$G F F ($X)")}) = (${bit("0", s"$G (${bit0(X)}) F (NUM_DIV ($X) 2)")})")
                      b10 <- at(bitZero, s"(${bit("0", s"$G (${bit0(X)}) F (NUM_DIV ($X) 2)")}) = ~(((${bit0(X)}) \\/ F) = (${bit0(s"NUM_DIV ($X) 2")}))")
                      lows <- at(k("BIT_LOW"), s"((${bit("0", X)}) = (${bit0(X)})) /\\ (!j:num. (${bit("SUC j", X)}) = (${bit("j", s"NUM_DIV ($X) 2")}))").flatMap(split)
                      l1 <- at(lows(1), s"(${bit("SUC 0", X)}) = (${bit("0", s"NUM_DIV ($X) 2")})")
                      l2 <- at(k("BIT_LOW"), s"((${bit("0", s"NUM_DIV ($X) 2")}) = (${bit0(s"NUM_DIV ($X) 2")})) /\\ (!j:num. (${bit("SUC j", s"NUM_DIV ($X) 2")}) = (${bit("j", s"NUM_DIV (NUM_DIV ($X) 2) 2")}))").flatMap(rules.conjElim1)
                      selfO <- rw(one, self)
                      out <- rewriting(Seq(one, st, iter, b1, b10), c)(g => tauto(Seq(selfO, nb, off2, lows(0), l1, l2), g))
                    } yield out
                    out <- rules.disjElim(either, zeroCase, oneCase)
                  } yield out
                  jm = s"NUM_SUB $J 2"
                  high <- for {
                    nlt <- prop(s"~($J < 2)")
                    held <- LogicError.lift(Kernel.assume(nlt))
                    le <- at(fact("NUM_LE_OF_NOT_LT"), s"~($J < 2) ==> 2 <= $J").flatMap(mp(_, held))
                    sub <- at(fact("NUM_REAL_SUB"), s"2 <= $J ==> real_of_num (NUM_SUB $J 2) = real_of_num $J - real_of_num 2").flatMap(mp(_, le))
                    back <- numLinText(Seq(sub), s"SUC (SUC ($jm)) = $J")
                    e1 <- numLinText(Seq(h, sub), s"$I + 1 + SUC ($jm) = $K")
                    e2 <- numLinText(Seq(h, sub), s"$I + 2 + $jm = $K")
                    n1 <- at(hyp, s"$I + 1 + SUC ($jm) = $K ==> $Run $Row $T ($I + 1) = (${bit(s"SUC ($jm)", X)})").flatMap(mp(_, e1))
                    n2 <- at(hyp, s"$I + 2 + $jm = $K ==> $Run $Row $T ($I + 2) = (${bit(jm, X)})").flatMap(mp(_, e2))
                    r <- at(bitRule, s"(${bit(s"SUC (SUC ($jm))", s"$G F F ($X)")}) = ~((${bit(s"SUC (SUC ($jm))", X)}) = ((${bit(s"SUC ($jm)", X)}) \\/ (${bit(jm, X)})))")
                      .flatMap(rw(back, _))
                    out <- rewriting(Seq(st, iter, r), c)(g => tauto(Seq(self, n1, n2), g))
                  } yield out
                  out <- classical.cases(small, low, high)
                } yield out
              }
            } yield out
          }
        )
        inner <- rules.specPrefix(proved, List(tv)).flatMap(gen(_, tv, kv, nv))
        closed <- rules.disch(mapT, inner).flatMap(rules.disch(ruleT, _))
        out <- gen(closed, run, gvar, itvar)
      } yield out
    }

    /**
     * `Sum (\k. f k * COND (k = m) 1 0) n = f m` below `n`: the sum keeps its one term at `m`.
     * `Decision` publishes the same fact as `SUM_INDICATOR`, above this link, so it is proved here.
     */
    def pick: R[Kernel.Thm] = {
      val f = Term.variable("f", Type.fun(Numbers, Reals))
      val (nv, mv) = (Term.variable("n", Numbers), Term.variable("m", Numbers))
      val Fx = "(f:num->real)"; val Mx = "(m:num)"
      def sumAt(n: String, at: String) = s"Sum (\\k:num. $Fx k * COND (k = $at) 1 0) ($n)"
      for {
        body <- prop(s"!m:num. m < (n:num) ==> ${sumAt("n:num", "m")} = $Fx m")
        proved <- induct(nv, body)(
          _ =>
            for {
              goal <- prop(s"$Mx < 0 ==> ${sumAt("0", Mx)} = $Fx $Mx")
              out <- underHyps(goal) { (h, c) =>
                for {
                  none <- at(fact("NUM_NOT_LT_ZERO"), s"~($Mx < 0)")
                  contra <- rules.notElim(none, h.head)
                  out <- rules.falsityElim(c, contra)
                } yield out
              }.flatMap(gen(_, mv))
            } yield out,
          (kk, hyp, _) => {
            val N = v(kk.name)
            for {
              goal <- prop(s"$Mx < SUC $N ==> ${sumAt(s"SUC $N", Mx)} = $Fx $Mx")
              out <- underHyps(goal) { (h, c) =>
                for {
                  grow <- at(fact("SUM_SUC"), s"${sumAt(s"SUC $N", Mx)} = ${sumAt(N, Mx)} + $Fx $N * COND ($N = $Mx) 1 0")
                  cases_ <- at(fact("NUM_LT_SUC_CASES"), s"$Mx < SUC $N ==> $Mx < $N \\/ $Mx = $N").flatMap(mp(_, h.head))
                  below <- for {
                    lt <- assumed(s"$Mx < $N")
                    ih <- at(hyp, s"$Mx < $N ==> ${sumAt(N, Mx)} = $Fx $Mx").flatMap(mp(_, lt._2))
                    apart <- for {
                      e <- assumed(s"$N = $Mx")
                      moved <- rw(e._2, lt._2)
                      irrefl <- at(fact("NUM_LT_IRREFL"), s"~($Mx < $Mx)")
                      out <- rules.notElim(irrefl, moved).flatMap(rules.notIntro(e._1, _))
                    } yield out
                    out <- rewriting(Seq(grow, ih), c)(deciding(Seq(apart))(arithmetic))
                  } yield out
                  atTop <- for {
                    e <- assumed(s"$Mx = $N")
                    sumT <- term(sumAt(N, N), Reals)
                    zeros <- belowBound(sumT, "\\k:num. (0:real)", N) { (k, kBelow) =>
                      for {
                        apart <- for {
                          eq <- assumed(s"$k = $N")
                          moved <- rw(eq._2, kBelow)
                          irrefl <- at(fact("NUM_LT_IRREFL"), s"~($N < $N)")
                          out <- rules.notElim(irrefl, moved).flatMap(rules.notIntro(eq._1, _))
                        } yield out
                      } yield (Seq.empty, Seq(apart), Nil)
                    }
                    none <- at(fact("SUM_OF_ZERO"), s"Sum (\\k:num. 0) ($N) = 0")
                    moved <- rw(e._2, grow)
                    out <- rewriting(Seq(e._2), c)(g => rewriting(Seq(moved, zeros, none), g)(deciding(Seq.empty)(arithmetic)))
                  } yield out
                  out <- rules.disjElim(cases_, below, atTop)
                } yield out
              }.flatMap(gen(_, mv))
            } yield out
          }
        )
        out <- gen(proved, f)
      } yield out
    }
  }
}
