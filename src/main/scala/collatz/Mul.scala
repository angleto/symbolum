package collatz ;

/* ------------------------------------------------------------------------- */
final case class Mul(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 2

  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).product

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Mul(exprs.map(_.replaceSymbol(sym, repl)))

  override def expand: Expr = {
    val children: Array[Expr] = exprs.map(_.expand)

    // First try product-to-sum on the unexpanded children
    productToSumCosines(children) match {
      case Some((transformed, remaining)) =>
        if (remaining.isEmpty)
          transformed.expand
        else
          Mul(transformed +: remaining).expand
      case None =>
        // Continue with normal expansion
        val termSets: Array[Array[Expr]] = children.map {
          case Add(ts) => ts
          case other => Array(other)
        }

        val hasAddition = termSets.exists(_.length > 1)
        if (!hasAddition) // nothing to distribute
          return Mul(children).simplify

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
          combos.map { factors => Mul(factors.toArray).simplify }.toArray

        Add(distributedTerms).simplify
    }
  }

  /* Product-to-sum for cosines: cos(A) * cos(B) = 1/2 * [cos(A-B) + cos(A+B)] */
  private def productToSumCosines(factors: Array[Expr]): Option[(Expr, Array[Expr])] = {
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
      val diff = Sub(Array(a, b)).simplify
      val sum = Add(Array(a, b)).simplify
      val cosSum = Add(Array(
        Cos(diff),
        Cos(sum)
      ))

      // Keep all other factors except the two cosines we used
      val remainingFactors = factors.zipWithIndex.collect {
        case (e, i) if i != idx1 && i != idx2 => e
      }

      Some((Mul(Array(halfFactor, cosSum)).simplify, remainingFactors))
    } else {
      None
    }
  }

  def simplify: Expr = {
    val simplified = exprs.map(_.simplify)
    val one = Num(1.0)

    /* flatten nested multiplications ------------------------------------ */
    val flattened = simplified.flatMap {
      case Mul(innerExprs) => innerExprs
      case other => Array(other)
    }

    /* remove useless factors -------------------------------------------- */
    val withoutOnes = flattened.filterNot(_ == one)
    if (withoutOnes.contains(Num(0.0))) {
      Num(0.0)
    } else {
      /* Try product-to-sum transformation for cosines ------------------- */
      productToSumCosines(withoutOnes) match {
        case Some((transformed, remaining)) =>
          // Multiply with remaining factors and recursively simplify
          if (remaining.isEmpty)
            transformed
          else {
            // Combine remaining factors with the transformed expression
            // The transformed is "1/2 * (cos(a-b) + cos(a+b))"
            // We want remaining * 1/2 * (cos(a-b) + cos(a+b))
            transformed match {
              case Mul(Array(halfFactor, sumExpr)) =>
                // Combine remaining factors with the half factor
                val allCoeffs = halfFactor +: remaining
                val finalCoeff = if (allCoeffs.length == 1) allCoeffs(0)
                else Mul(allCoeffs).simplify
                Mul(Array(finalCoeff, sumExpr)).simplify
              case _ =>
                Mul(transformed +: remaining).simplify
            }
          }

        case None =>
          /* split into numeric and symbolic parts ----------------------------- */
          val (nums, others) = withoutOnes.partition(_.isInstanceOf[Num])

          val (numProd, denProd) =
            nums.collect { case Num(n, d) => (n, d) }
              .foldLeft((1.0, 1.0)) { case ((an, ad), (bn, bd)) =>
                (an * bn, ad * bd)
              }

          val numericPart = Num(numProd, denProd).simplify
          val combined: Array[Expr] =
            (if (numericPart == one) Array.empty[Expr]
            else Array(numericPart.expand)) ++ others

          combined.length match {
            case 0 => Num(1.0)
            case 1 => combined(0)
            case _ => Mul(combined)
          }
      }
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
