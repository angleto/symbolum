package symbolicas

/**
 * Base class for all expression-related errors.
 *
 * These errors represent runtime failures during expression evaluation or manipulation.
 * They are distinct from programming errors (which use require/IllegalArgumentException).
 *
 * @param message Error message describing what went wrong
 * @param cause Optional underlying cause
 */
sealed abstract class ExpressionError(message: String, cause: Option[Throwable] = None)
  extends Exception(message, cause.orNull)

/**
 * Thrown when attempting to divide by zero during evaluation.
 *
 * @param expression String representation of the expression causing the error
 */
final case class DivisionByZeroError(expression: String)
  extends ExpressionError(s"Division by zero in expression: $expression")

/**
 * Thrown when a variable is not defined in the evaluation context.
 *
 * @param variableName The name of the undefined variable
 * @param availableVariables Names of variables that are defined
 */
final case class UndefinedVariableError(
  variableName: String,
  availableVariables: Set[String] = Set.empty
) extends ExpressionError({
  val available = if (availableVariables.nonEmpty)
    s" (available: ${availableVariables.mkString(", ")})"
  else
    ""
  s"Variable '$variableName' is not defined$available"
})

/**
 * Thrown when a numeric overflow occurs during computation.
 *
 * @param operation Description of the operation that caused overflow
 * @param details Optional details about the values involved
 */
final case class NumericOverflowError(operation: String, details: Option[String] = None)
  extends ExpressionError({
    val detailStr = details.map(d => s": $d").getOrElse("")
    s"Numeric overflow in $operation$detailStr"
  })

/**
 * Thrown when expansion would create too many terms.
 *
 * @param estimatedTerms Number of terms that would be created
 * @param limit Maximum allowed terms
 */
final case class ExpansionLimitExceededError(estimatedTerms: Long, limit: Int)
  extends ExpressionError(
    s"Expansion would create $estimatedTerms terms (limit: $limit). " +
    s"Consider using a higher limit or simplifying the expression first."
  )

/**
 * Thrown when an invalid expression structure is encountered.
 *
 * @param message Description of the invalid structure
 */
final case class InvalidExpressionError(message: String)
  extends ExpressionError(message)
