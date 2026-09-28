package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A derivative the kernel checks, for the functions `Circle` needs: sums, differences and products
 * of `t`, constants, `sin t` and `cos t`, and quotients by a constant.
 *
 * Nothing here is believed. Each case of [[Slope.at]] is one of `Derivative`'s published facts at
 * the pieces (`DERIVATIVE_ID`, `DERIVATIVE_CONST`, `DERIVATIVE_SIN`, `DERIVATIVE_COS`,
 * `DERIVATIVE_LINEAR`, `DERIVATIVE_PRODUCT`), and what they give is the derivative of the function
 * they build, `\w. 1 * f w + 1 * g w` for a sum, at the slope they build, `1 * y + 1 * z`. The last
 * step carries both to what the caller wrote: the function by extensionality over `Ring` on the two
 * bodies, the slope by `Ring`. A slope the caller got wrong is `Ring` refusing an equation, and a
 * body outside the grammar is refused by name before anything is built.
 *
 * It exists because `Circle` takes six derivatives of polynomials in `sin` and `cos`, and each one
 * written by hand is a dozen specialisations whose only content is the grammar below.
 *
 * What it does not do: the chain rule, a quotient by anything that varies, and any function but
 * `sin` and `cos`. Each is one more case over a published fact, and none is needed yet.
 */
private[theories] final case class Slope(
  logic: Logic,
  classical: Classical,
  ring: Ring,
  theory: Theory,
  notation: Notation,
  fact: String => Either[LogicError, Kernel.Thm]
) {
  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Binary: Type = Type.fun(Reals, Type.fun(Reals, Reals))
  private val rules = logic.rules

  private def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Reals)

  /** `|- derivative F x d` for some `F` equal to `\t. body` and some `d`, by the body's shape. */
  private def built(body: Term, t: FVar, x: Term): Either[LogicError, Kernel.Thm] =
    body match {
      case `t` => fact("DERIVATIVE_ID").flatMap(rules.spec(x, _))
      case _ if !Term.freeVariables(body).contains(t) => fact("DERIVATIVE_CONST").flatMap(rules.specAll(_, List(body, x)))
      case App(Const(Transcendental.Sine, _), `t`) => fact("DERIVATIVE_SIN").flatMap(rules.spec(x, _))
      case App(Const(Transcendental.Cosine, _), `t`) => fact("DERIVATIVE_COS").flatMap(rules.spec(x, _))
      case App(App(Const(operator, _), a), b) if operator == Real.Addition || operator == Real.Subtraction =>
        for {
          left <- built(a, t, x)
          right <- built(b, t, x)
          fy <- pieces(left)
          gz <- pieces(right)
          one <- real("1")
          sign <- real(if (operator == Real.Addition) "1" else "0 - 1")
          result <- fact("DERIVATIVE_LINEAR")
            .flatMap(rules.specAll(_, List(fy._1, gz._1, x, fy._2, gz._2, one, sign)))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right))
        } yield result
      case App(App(Const(Real.Multiplication, _), a), b) =>
        for {
          left <- built(a, t, x)
          right <- built(b, t, x)
          fy <- pieces(left)
          gz <- pieces(right)
          result <- fact("DERIVATIVE_PRODUCT")
            .flatMap(rules.specAll(_, List(fy._1, gz._1, x, fy._2, gz._2)))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right))
        } yield result
      // `f / c` as `(1 / c) * f + 0 * f`, which is `DERIVATIVE_LINEAR` at one function twice.
      case App(App(Const(Real.Division, _), a), c) if !Term.freeVariables(c).contains(t) =>
        for {
          inner <- built(a, t, x)
          fy <- pieces(inner)
          one <- real("1")
          zero <- real("0")
          divide <- LogicError.lift(theory.constant(Real.Division, Binary))
          scale <- LogicError.lift(Term.appAll(divide, List(one, c)))
          result <- fact("DERIVATIVE_LINEAR")
            .flatMap(rules.specAll(_, List(fy._1, fy._1, x, fy._2, fy._2, scale, zero)))
            .flatMap(rules.mp(_, inner))
            .flatMap(rules.mp(_, inner))
        } yield result
      case other =>
        Left(NotOfForm("a sum, difference or product of t, constants, sin t and cos t, or one over a constant", other))
    }

  /** `derivative F x d` taken apart into `F` and `d`. */
  private def pieces(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] = theorem.conclusion match {
    case App(App(App(_, function), _), slope) => Right((function, slope))
    case other => Left(NotOfForm("a derivative", other))
  }

  /**
   * `|- derivative (\t. body) x slope`, the function and the slope exactly as the caller wrote them.
   *
   * `slope` is a term in `x`. It is checked, not trusted: the equation between it and what the
   * published facts produced is `Ring`'s to prove, and a slope that is wrong is refused there.
   */
  def at(function: Term, x: Term, slope: Term): Either[LogicError, Kernel.Thm] = function match {
    case Abs(_, _) =>
      val w = Conv.freshVariable(
        "w",
        Reals,
        Term.freeVariables(function) ++ Term.freeVariables(x) ++ Term.freeVariables(slope)
      )
      for {
        body <- LogicError.lift(Term.app(function, w)).flatMap(Conv.betaRoot).flatMap(Datatype.rightOf)
        raw <- built(body, w, x)
        parts <- pieces(raw)
        (made, computed) = parts
        madeAtW <- LogicError.lift(Term.app(made, w)).flatMap(Conv.betaNormalise)
        wantedAtW <- LogicError.lift(Term.app(function, w)).flatMap(Conv.betaNormalise)
        pointwise <- for {
          l <- Datatype.rightOf(madeAtW)
          r <- Datatype.rightOf(wantedAtW)
          goal <- LogicError.lift(Term.eq(l, r))
          bodies <- ring.prove(goal)
          e <- Conv.trans(madeAtW, bodies).flatMap(e => Conv.sym(wantedAtW).flatMap(Conv.trans(e, _)))
        } yield e
        functions <- rules.gen(w, pointwise).flatMap(classical.ext(logic, _))
        slopes <- LogicError.lift(Term.eq(computed, slope)).flatMap(ring.prove)
        derivative <- raw.conclusion match {
          case App(App(App(c, _), _), _) => Right(c)
          case other => Left(NotOfForm("a derivative", other))
        }
        first <- Conv.apTerm(derivative, functions).flatMap(Conv.apThm(_, x)).flatMap(Conv.apThm(_, computed))
        second <- LogicError.lift(Term.appAll(derivative, List(function, x))).flatMap(Conv.apTerm(_, slopes))
        result <- Conv.trans(first, second).flatMap(e => LogicError.lift(Kernel.eqMp(e, raw)))
      } yield result
    case other => Left(NotOfForm("a function written as a lambda", other))
  }
}
