# CI/CD Configuration

This document describes the Continuous Integration and Continuous Deployment setup for Symbolicas.

## Overview

The project uses GitHub Actions for automated testing, building, and package publishing. The CI/CD pipeline consists of two main workflows:

1. **CI Workflow** (`ci.yml`) - Runs on every push and pull request
2. **Publish Workflow** (`publish.yml`) - Publishes packages to GitHub Package Registry

## CI Workflow

### Trigger Events
- Push to `main`, `master`, `develop`, or any `claude/**` branch
- Pull requests targeting `main`, `master`, or `develop` branches

### Jobs

#### Test Job
- **Matrix Testing**: Tests across multiple Java versions (11, 17) and Scala 3.3.5
- **Steps**:
  1. Checkout code
  2. Setup JDK and SBT
  3. Cache dependencies (Ivy, SBT, Coursier)
  4. Compile the project
  5. Run all tests
  6. Check code formatting (optional)

#### Build Job
- **Runs after tests pass**
- **Steps**:
  1. Build package artifacts
  2. Generate Scaladoc documentation
  3. Upload artifacts (retained for 7 days)

### Running Locally

```bash
# Compile
sbt compile

# Run tests
sbt test

# Generate documentation
sbt doc

# Build package
sbt package
```

## Publish Workflow

### Trigger Events
- Creation of a GitHub release
- Manual workflow dispatch

### Configuration

The publish workflow:
1. Runs all tests before publishing
2. Extracts version from release tag or manual input
3. Updates `build.sbt` with the version
4. Publishes to GitHub Package Registry
5. Creates a summary with installation instructions

### Publishing a Release

#### Option 1: GitHub Release (Recommended)
1. Create a git tag:
   ```bash
   git tag v4.0.0
   git push origin v4.0.0
   ```
2. Create a GitHub release from the tag
3. The workflow will automatically publish the package

#### Option 2: Manual Workflow Dispatch
1. Go to Actions → Publish Package → Run workflow
2. Enter the version number (e.g., `4.0.0`)
3. Click "Run workflow"

### Manual Publishing

To publish manually from your local machine:

```bash
# Set GitHub token
export GITHUB_TOKEN=your_token_here

# Publish to GitHub Packages
sbt publish
```

## GitHub Package Registry Setup

### Publishing Configuration

The package is configured in `build.sbt`:
- **Organization**: `io.github.angleto`
- **Package Name**: `symbolicas`
- **Registry URL**: `https://maven.pkg.github.com/angleto/symbolicas`
- **Authentication**: Via `GITHUB_TOKEN` environment variable

### Using the Package

To use this package in your Scala project, add to `build.sbt`:

```scala
// Add resolver for GitHub Packages
resolvers += "GitHub Package Registry" at "https://maven.pkg.github.com/angleto/symbolicas"

// Add credentials (use GitHub personal access token with read:packages scope)
credentials += Credentials(
  "GitHub Package Registry",
  "maven.pkg.github.com",
  "YOUR_GITHUB_USERNAME",
  "YOUR_GITHUB_TOKEN"
)

// Add dependency
libraryDependencies += "io.github.angleto" %% "symbolicas" % "4.0.0"
```

Alternatively, create `~/.sbt/1.0/credentials.sbt`:

```scala
credentials += Credentials(
  "GitHub Package Registry",
  "maven.pkg.github.com",
  "YOUR_GITHUB_USERNAME",
  "YOUR_GITHUB_TOKEN"
)
```

### Creating a GitHub Token

1. Go to GitHub Settings → Developer settings → Personal access tokens → Tokens (classic)
2. Generate new token with the following scopes:
   - `read:packages` - To download packages
   - `write:packages` - To publish packages (for contributors)
3. Save the token securely
4. Use it in your credentials configuration

## Test Suite

The project includes comprehensive test coverage:

### Test Files
- `BasicSimplificationSpec.scala` - Basic simplification operations
- `CosineSimplificationSpec.scala` - Trigonometric simplification
- `DistributionSpec.scala` - Expression distribution
- `FractionOperationsSpec.scala` - Fraction operations
- `RegressionSpec.scala` - Regression tests
- `ExpansionSpec.scala` - Expression expansion
- `FixpointDetectionSpec.scala` - Fixpoint detection
- `CollatzSpec.scala` - Collatz series
- `FullSimplifyFixSpec.scala` - Full simplification fixes
- `ConfigurationSpec.scala` - Configuration testing
- `SimplificationCorrectnessSpec.scala` - Simplification correctness
- `DerivativeSpec.scala` - Symbolic differentiation
- `SolveSpec.scala` - Equation solving
- `TrigonometricSpec.scala` - Trigonometric functions
- `ExponentialLogarithmSpec.scala` - Exponential and logarithm
- `CoreTypesSpec.scala` - Core types (Num, Var)

### Test Frameworks
- **ScalaTest 3.2.18** - Main testing framework
- **ScalaCheck 1.17.0** - Property-based testing
- **Configuration**: Serial execution (no parallel tests)

### Running Tests

```bash
# Run all tests
sbt test

# Run specific test suite
sbt "testOnly symbolicas.DerivativeSpec"

# Run tests with detailed output
sbt "testOnly * -- -oD"

# Run tests in watch mode
sbt ~test
```

## Build Artifacts

Build artifacts are stored in:
- `target/scala-3.3.5/*.jar` - Compiled JAR files
- `target/scala-3.3.5/api/` - Generated Scaladoc

## Caching Strategy

The workflows cache the following directories for faster builds:
- `~/.ivy2/cache` - Ivy dependencies
- `~/.sbt` - SBT configuration and plugins
- `~/.coursier` - Coursier cache

## Environment Variables

### Required for Publishing
- `GITHUB_TOKEN` - Automatically provided by GitHub Actions for workflow-triggered publishes

### Optional
- `SBT_OPTS` - JVM options for SBT (e.g., `-Xmx2G`)

## Troubleshooting

### Tests Failing Locally but Passing in CI
- Ensure you're using the correct Java version (11 or 17)
- Clear SBT cache: `sbt clean`
- Check Scala version: `sbt scalaVersion`

### Publishing Fails
- Verify `GITHUB_TOKEN` has `write:packages` permission
- Ensure the version in `build.sbt` is updated
- Check that package name and organization match

### Dependencies Not Resolving
- Clear Ivy cache: `rm -rf ~/.ivy2/cache`
- Clear Coursier cache: `rm -rf ~/.coursier/cache`
- Update SBT: Check `project/build.properties`

## Best Practices

1. **Always run tests locally before pushing**
   ```bash
   sbt clean test
   ```

2. **Use semantic versioning for releases**
   - Major: Breaking changes
   - Minor: New features (backward compatible)
   - Patch: Bug fixes

3. **Tag releases consistently**
   ```bash
   git tag -a v4.0.0 -m "Release version 4.0.0"
   ```

4. **Monitor CI status before merging PRs**

5. **Keep dependencies up to date**
   - Regularly review and update library versions
   - Test thoroughly after updates

## Additional Resources

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [GitHub Packages Documentation](https://docs.github.com/en/packages)
- [SBT Documentation](https://www.scala-sbt.org/documentation.html)
- [ScalaTest Documentation](https://www.scalatest.org/)
