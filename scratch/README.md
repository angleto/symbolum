# Scratch

Anything here is ignored by git and is not part of any sbt source set.

**It exists because the alternative happened.** A session writing a throwaway spec put it under
`modules/`, which `CLAUDE.md` forbids, and the next run of `sbt test` on the shared checkout failed
for somebody else with an error about a file they had never seen. Two sessions on one tree need a
place for a probe that is not the project.

What goes here: a `scala-cli` file to try a term out, a log worth keeping for an hour, a generated
table on the way to becoming a document. What does not: anything a test should assert instead.
