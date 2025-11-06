package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/* ------------------------------------------------------------------------- */
final case class Mul(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 2

  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).product

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Mul(exprs.map(_.replaceSymbol(sym, repl)))

  override def expand(implicit config: SimplificationConfig): Expr = {
    val children: Array[Expr] = exprs.map(_.expand(config))

    // First try product-to-sum if enabled
    if (config.isEnabled(ProductOfCosToSumOfCos)) {
      productToSumCosines(children)(config) match {
        case Some((transformed, remaining)) =>
          if (remaining.isEmpty)
            transformed.expand(config)
          else
            Mul(transformed +: remaining).expand(config)
        case None =>
          expandDistribute(children)(config)
      }
    } else {
      expandDistribute(children)(config)
    }
  }

  private def expandDistribute(children: Array[Expr])(implicit config: SimplificationConfig): Expr = {
    // Continue with normal expansion
    val termSets: Array[Array[Expr]] = children.map {
      case Add(ts) => ts
      case other => Array(other)
    }

    val hasAddition = termSets.exists(_.length > 1)
    if (!hasAddition || !config.isEnabled(DistributeProduct))
      return Mul(children).simplify(config)

    /* cartesian product ------------------------------------------------ */
    def cartesian[T](xss: List[List[T]]): List[List[T]] = xss match {
      case Nil => List(Nil)
      case h :: t =>
        for {
          x <- h
          xs <- cartesian(t)
        } yield x :: xs
    }

    val combos: List[List[Expr]] =
      cartesian(termSets.map(_.toList).toList)

    /* build a product for every combination, simplify it -------------- */
    val distributedTerms: Array[Expr] =
      combos.map { factors => Mul(factors.toArray).simplify(config) }.toArray

    Add(distributedTerms).simplify(config)
  }

  /* Product-to-sum for cosines: cos(A) * cos(B) = 1/2 * [cos(A-B) + cos(A+B)] */
  private def productToSumCosines(factors: Array[Expr])(implicit config: SimplificationConfig): Option[(Expr, Array[Expr])] = {
    // Find the first pair of Cos terms
    val cosIndices = factors.zipWithIndex.collect {
      case (Cos(_), idx) => idx
    }

    if (cosIndices.length >= 2) {
      val idx1 = cosIndices(0)
      val idx2 = cosIndices(1)

      val Cos(a) = factors(idx1): @unchecked
      val Cos(b) = factors(idx2): @unchecked

      // Build: 1/2 * [cos(a - b) + cos(a + b)]
      val halfFactor = Num(1, 2)
      val diff = Sub(Array(a, b)).simplify(config)
      val sum = Add(Array(a, b)).simplify(config)
      val cosSum = Add(Array(
        Cos(diff),
        Cos(sum)
      ))

      // Keep all other factors except the two cosines we used
      val remainingFactors = factors.zipWithIndex.collect {
        case (e, i) if i != idx1 && i != idx2 => e
      }

      Some((Mul(Array(halfFactor, cosSum)).simplify(config), remainingFactors))
    } else {
      None
    }
  }

  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplified = exprs.map(_.simplify(config))
    val one = Num(1.0)

    /* flatten nested multiplications ------------------------------------ */
    val flattened = if (config.isEnabled(FlattenOperations)) {
      simplified.flatMap {
        case Mul(innerExprs) => innerExprs
        case other => Array(other)
      }
    } else {
      simplified
    }

    /* remove useless factors -------------------------------------------- */
    val withoutOnes = if (config.isEnabled(RemoveIdentity)) {
      flattened.filterNot(_ == one)
    } else {
      flattened
    }

    // Check for zero
    if (withoutOnes.contains(Num(0.0))) {
      return Num(0.0)
    }

    /* Try product-to-sum transformation for cosines ------------------- */
    if (config.isEnabled(ProductOfCosToSumOfCos)) {
      productToSumCosines(withoutOnes)(config) match {
        case Some((transformed, remaining)) =>
          // Multiply with remaining factors and recursively simplify
          if (remaining.isEmpty)
            return transformed
          else {
            // Combine remaining factors with the transformed expression
            // The transformed is "1/2 * (cos(a-b) + cos(a+b))"
            // We want remaining * 1/2 * (cos(a-b) + cos(a+b))
            transformed match {
              case Mul(Array(halfFactor, sumExpr)) =>
                // Combine remaining factors with the half factor
                val allCoeffs = halfFactor +: remaining
                val finalCoeff = if (allCoeffs.length == 1) allCoeffs(0)
                else Mul(allCoeffs).simplify(config)
                return Mul(Array(finalCoeff, sumExpr)).simplify(config)
              case _ =>
                return Mul(transformed +: remaining).simplify(config)
            }
          }

        case None =>
        // Fall through to numeric simplification
      }
    }

    /* split into numeric and symbolic parts ----------------------------- */
    val (nums, others) = withoutOnes.partition(_.isInstanceOf[Num])

    val numericPart = if (config.isEnabled(CombineNumericLiterals) && nums.nonEmpty) {
      val (numProd, denProd) =
        nums.collect { case Num(n, d) => (n, d) }
          .foldLeft((1.0, 1.0)) { case ((an, ad), (bn, bd)) =>
            (an * bn, ad * bd)
          }
      Num(numProd, denProd).simplify(config)
    } else {
      one
    }

    val combined: Array[Expr] =
      (if (numericPart == one) nums else Array(numericPart)) ++ others

    combined.length match {
      case 0 => Num(1.0)
      case 1 => combined(0)
      case _ => Mul(combined)
    }
  }

  override def toString: String = {
    // Group numeric coefficients first for cleaner output
    val (nums, others) = exprs.partition(_.isInstanceOf[Num])

    val parts = if (nums.nonEmpty) {
      // Show numeric coefficients first (without extra parens)
      nums.map(_.toString) ++ others.map(e => showWithParens(e, this))
    } else {
      exprs.map(e => showWithParens(e, this))
    }

    parts.mkString(" * ")
  }
}
