// Statement coverage. The floor it enforces lives in build.sbt, per module, set to the value
// actually measured rather than to an aspiration.
addSbtPlugin("org.scoverage" % "sbt-scoverage" % "2.2.1")

// The distribution: `dist/Universal/packageZipTarball` builds the tarball that carries every
// module's jar, the runtime classpath and a launcher per entry point. A library reaches a consumer
// as a maven coordinate and a person reaches the prover through a script, and those are two
// different artifacts rather than one artifact read two ways.
//
// Pinned at 1.11.7, the current release, because a packaging plugin decides the shape of what
// ships: a floating version would change the launcher scripts without a commit saying so.
addSbtPlugin("com.github.sbt" % "sbt-native-packager" % "1.11.7")

// The version, read from the git tag rather than written in `build.sbt`. Before this it was both:
// `ThisBuild / version` held a literal and the publishing workflow overwrote that literal with a
// value typed into a form, so what a published artifact called itself and what the repository was
// tagged were two copies of one fact with nothing comparing them. `git describe` is the comparison
// the release convention already asks for; this makes the build read the same answer.
//
// Pinned at 5.1.1, the current release. The prefix setting is in `build.sbt`: tags here carry no
// `v` and dynver expects one by default.
addSbtPlugin("com.github.sbt" % "sbt-dynver" % "5.1.1")
