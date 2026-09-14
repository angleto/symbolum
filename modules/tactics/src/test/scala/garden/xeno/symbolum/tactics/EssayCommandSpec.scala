package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.theories.Essay

/**
 * The two commands a theorem's page tells a reader to run, checked against the commands themselves.
 *
 * `Essay` prints "run this to get the theorem back" and lives in `modules/theories`, which is below
 * `modules/tactics` and cannot see `Ask` or `Find`. So the page carries a literal, which is the
 * shape of copy that goes stale silently: the entry point moves, every generated page goes on
 * naming the old one, and the document keeps regenerating without complaint because the literal is
 * what it was generated from.
 *
 * This is the one module that can see both sides, so the agreement is asserted from here. It fails
 * on a rename of either entry point, which is the moment the pages become wrong.
 */
class EssayCommandSpec extends AnyFlatSpec with Matchers {

  "The `Ask` line on a theorem's page" should "name the command `Ask` actually publishes" in {
    withClue(s"page says `${Essay.AskCommand}`, `Ask` says `${Ask.Command}`\n") {
      Ask.Command.startsWith(Essay.AskCommand) shouldBe true
    }
  }

  "The `Find` line on a theorem's page" should "name the command `Find` actually publishes" in {
    withClue(s"page says `${Essay.FindCommand}`, `Find` says `${Find.Command}`\n") {
      Find.Command.startsWith(Essay.FindCommand) shouldBe true
    }
  }

  /**
   * And that neither literal is empty, which is what makes the two assertions above mean something.
   *
   * `"anything".startsWith("")` is true, so a literal that was emptied by a bad edit would pass
   * both checks above while every page lost its command. This is the input that makes the guard
   * trivially true, asserted against.
   */
  it should "be checked against a prefix that could fail" in {
    Essay.AskCommand should not be empty
    Essay.FindCommand should not be empty
    Ask.Command should not startWith Essay.FindCommand
  }
}
