# Contributing to Symbolum

Thank you for your interest in contributing to Symbolum! This document provides guidelines and instructions for contributing to the project.

## Code of Conduct

We are committed to providing a welcoming and inclusive environment. Please be respectful and professional in all interactions.

## How to Contribute

### Reporting Bugs

If you find a bug:

1. Check if the issue already exists in the GitHub Issues
2. If not, create a new issue with:
   - Clear, descriptive title
   - Steps to reproduce the problem
   - Expected behavior vs actual behavior
   - Scala version and environment details
   - Code example demonstrating the issue

### Suggesting Enhancements

We welcome suggestions for new features or improvements:

1. Check existing issues and discussions
2. Create an issue describing:
   - The problem you're trying to solve
   - Your proposed solution
   - Why this would be useful to others
   - Example usage if applicable

### Pull Requests

We love pull requests! Here's how to submit one:

1. **Fork the repository** and create your branch from `main`
2. **Make your changes** following our coding standards
3. **Add tests** for any new functionality
4. **Update documentation** including:
   - Scaladoc comments for new public APIs
   - README if adding major features
   - CHANGELOG with your changes
5. **Ensure tests pass**: `sbt test`
6. **Ensure code compiles**: `sbt compile`
7. **Submit the pull request** with:
   - Clear title and description
   - Reference to related issues (if any)
   - Summary of changes made

## Development Setup

### Prerequisites

- Scala 3.3.5 or later
- SBT (Scala Build Tool)
- Git

### Getting Started

```bash
# Clone your fork
git clone https://github.com/YOUR_USERNAME/garden.xeno.symbolum.git
cd symbolum

# Add upstream remote
git remote add upstream https://github.com/angleto/symbolum.git

# Create a branch for your changes
git checkout -b feature/my-feature

# Make your changes and commit
git add .
git commit -m "Add my feature"

# Push to your fork
git push origin feature/my-feature
```

### Building

```bash
# Compile the project
sbt compile

# Run tests
sbt test

# Generate documentation
sbt doc
```

### Running Tests

```bash
# Run the whole suite
sbt test

# Run one suite
sbt "core/testOnly garden.xeno.symbolum.BasicSimplificationSpec"

# Run the runnable demonstrations
sbt "examples/runMain garden.xeno.symbolum.examples.TestSymbolum"
```

## Before changing anything in the proof half

This repository contains a proof assistant, and its correctness argument is that a theorem can only
come from an inference rule. Two rules follow, and they are not style:

**Do not add to `modules/kernel` without reading [docs/architecture.md](docs/architecture.md).** A
bug there is unbounded: it can make the system prove anything. Everywhere else, a bug costs a
failed proof.

**Do not assert an axiom.** `Kernel.assertAxiom` exists and is named so that it reads as what it is
at the call site. The theory holds sixteen axioms, a test asserts exactly those, and an axiom added
by accident would fail no other test: it would make more things provable, which looks like
progress. If something cannot be proved, derive it, or say in the pull request why it must be
assumed.

**Documentation is part of the change.** Every example in `README.md` and `docs/proving.md` is
executed by `DocumentationSpec`, so an example that stops working fails the build. Add yours there
in the same commit.

## Coding Standards

### Scala Style

- Follow standard Scala 3 conventions
- Use meaningful variable and function names
- Keep functions focused and reasonably sized
- Use pattern matching where appropriate
- Prefer immutability and functional approaches

### Documentation

All public APIs must have Scaladoc comments including:

```scala
/**
 * Brief one-line description.
 *
 * Detailed description with multiple paragraphs if needed.
 * Explain what the function does, any important details,
 * and edge cases.
 *
 * @param paramName description of parameter
 * @return description of return value
 * @throws ExceptionType when this exception is thrown
 *
 * @example {{{
 * val x = Var("x")
 * val result = x.someMethod()
 * // result: expected output
 * }}}
 */
def someMethod(paramName: Type): ReturnType = ???
```

### Commit Messages

Write clear, descriptive commit messages:

```
Add feature: Brief description of what was added

More detailed explanation of the changes, why they were
needed, and any important context.

Fixes #123
```

Good commit message practices:
- Use present tense ("Add feature" not "Added feature")
- First line should be 50 characters or less
- Reference issue numbers when applicable
- Explain *why* not just *what*

## Project Structure

```
symbolum/
├── src/
│   ├── main/
│   │   └── scala/
│   │       └── garden/xeno/symbolum/
│   │           ├── Expr.scala           # Base trait
│   │           ├── Num.scala            # Numeric literals
│   │           ├── Var.scala            # Variables
│   │           ├── Add.scala            # Addition
│   │           ├── Mul.scala            # Multiplication
│   │           ├── Div.scala            # Division
│   │           ├── Sub.scala            # Subtraction
│   │           ├── Cos.scala            # Cosine and Negation
│   │           ├── SimplificationConfig.scala
│   │           ├── Rational.scala      # Exact fraction arithmetic
│   │           └── Dsl.scala            # DSL helpers
│   └── test/
│       └── scala/
│           └── garden/xeno/symbolum/
│               └── [test files]
├── build.sbt
├── README.md
├── LICENSE
└── CONTRIBUTING.md
```

## Areas for Contribution

We especially welcome contributions in these areas:

### High Priority

- **Additional simplification rules**: New algebraic transformations
- **Performance optimizations**: Faster simplification algorithms
- **Test coverage**: More comprehensive test cases
- **Documentation**: Examples, tutorials, API docs

### Medium Priority

- **New expression types**: Power, logarithm, exponential, etc.
- **Pattern matching**: Template matching for algebraic patterns
- **Polynomial operations**: Factoring, GCD, etc.
- **Integration with other systems**: Export to SymPy, Mathematica format

### Nice to Have

- **Web interface**: Interactive symbolic calculator
- **Jupyter notebook support**: Better integration
- **Visualization**: Expression tree visualization
- **REPL improvements**: Better interactive experience

## Testing Guidelines

### Writing Tests

When adding new functionality, include:

1. **Unit tests**: Test individual components in isolation
2. **Integration tests**: Test components working together
3. **Edge cases**: Test boundary conditions and error cases
4. **Regression tests**: Prevent previously fixed bugs from reoccurring

### Test Structure

```scala
// Example test structure (when using a test framework)
class MyFeatureTest extends AnyFlatSpec with Matchers {
  "MyFeature" should "behave correctly" in {
    val expr = /* ... */
    val result = expr.simplify()
    result shouldBe /* expected */
  }

  it should "handle edge cases" in {
    // Edge case test
  }
}
```

## Documentation Guidelines

### README Updates

When adding major features, update:
- Feature list
- Usage examples
- API reference table
- Version history

### Scaladoc

- All public classes, traits, and methods need documentation
- Include `@example` blocks for complex APIs
- Document parameters, return values, and exceptions
- Use proper Scaladoc formatting

### Markdown Files

- Use clear headings and structure
- Include code examples
- Keep line length reasonable (80-100 chars)
- Use proper markdown formatting

## Release Process

For maintainers:

1. Update version in `build.sbt`
2. Update CHANGELOG
3. Create release notes
4. Tag release: `git tag -a v2.x.x -m "Version 2.x.x"`
5. Push tags: `git push --tags`
6. Publish to Maven Central (if applicable)

## Questions?

If you have questions about contributing:

1. Check existing documentation
2. Search closed issues and PRs
3. Open a new issue with the `question` label
4. Reach out to maintainers

## Recognition

Contributors will be:
- Listed in the project README
- Credited in release notes
- Acknowledged in commit history

Thank you for contributing to Symbolum! 🎉
