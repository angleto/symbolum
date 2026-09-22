package garden.xeno.symbolum

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
 * Thrown when expansion would create too many terms.
 *
 * `$estimatedTerms terms` is not a count that reaches one, and the reason is two guards rather
 * than a reading of the message: `SimplificationConfig` requires `maxExpansionTerms > 0`, and
 * `Canonical.distribute` raises this only where `estimatedTerms > maxExpansionTerms`, so the
 * number printed is at least two. `Arbitrary`'s own `$digits digits` is excluded for the same
 * shape of reason, inside a `require`. Neither takes the counter in `Plural`.
 *
 * @param estimatedTerms Number of terms that would be created
 * @param limit Maximum allowed terms
 */
final case class ExpansionLimitExceededError(estimatedTerms: Long, limit: Int)
  extends ExpressionError(
    s"Expansion would create $estimatedTerms terms (limit: $limit). " +
    s"Consider using a higher limit or simplifying the expression first."
  )

