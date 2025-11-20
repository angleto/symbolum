ThisBuild / version := "4.0.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.5"

ThisBuild / organization := "io.github.angleto"

lazy val root = (project in file("."))
  .settings(
    name := "symbolicas",

    // Library dependencies
    libraryDependencies ++= Seq(
      // Testing frameworks
      "org.scalatest" %% "scalatest" % "3.2.18" % Test,
      "org.scalatestplus" %% "scalacheck-1-17" % "3.2.18.0" % Test,
      "org.scalacheck" %% "scalacheck" % "1.17.0" % Test
    ),

    // Compiler options
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-Xfatal-warnings"
    ),

    // Test configuration
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),
    Test / parallelExecution := false,

    // Publishing configuration
    publishMavenStyle := true,

    // GitHub Packages configuration
    publishTo := Some(
      "GitHub Package Registry" at "https://maven.pkg.github.com/angleto/symbolicas"
    ),

    credentials += Credentials(
      "GitHub Package Registry",
      "maven.pkg.github.com",
      "angleto",
      sys.env.getOrElse("GITHUB_TOKEN", "")
    ),

    // Project metadata
    licenses := Seq("MIT" -> url("https://opensource.org/licenses/MIT")),
    homepage := Some(url("https://github.com/angleto/symbolicas")),
    scmInfo := Some(
      ScmInfo(
        url("https://github.com/angleto/symbolicas"),
        "scm:git:git@github.com:angleto/symbolicas.git"
      )
    ),
    developers := List(
      Developer(
        id = "angleto",
        name = "angleto",
        email = "",
        url = url("https://github.com/angleto")
      )
    ),

    // POM settings
    pomIncludeRepository := { _ => false }
  )
