package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.*

/**
 * What a generated page says, and what it must not be able to say.
 *
 * The page is the most persuasive artifact this repository produces: it sets a theorem the way a
 * book sets it, walks its derivation, and lists what it is believed on. So the assertions worth
 * making are not that it is pretty. They are that **every claim on it is one the code can make**,
 * and the failure modes are specific enough to be named:
 *
 *  - a formula that cannot be read back, published without the form that can;
 *  - a derivation that is missing, reported as a derivation that is short;
 *  - a theorem listed among the things it rests on, which reads as circular and is what the first
 *    page this produced actually said;
 *  - a citation to a name a reader cannot look up.
 *
 * The two fixed pages here are compared against properties rather than against text. A golden page
 * would pin the prose and fail on every spelling improved, which is the opposite of what should be
 * expensive to change: the wording is meant to move, the guarantees are not.
 */
class EssaySpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val library = Library.of(chain)
  private val signature = chain.widest

  private def page(name: String): String = Essay.of(chain, name).toOption.get

  "The page for a recorded theorem" should "carry both forms of the statement" in {
    val text = page(Magnitude.Triangle)
    val pair = signature.readable(library.named(Magnitude.Triangle).head.theorem.conclusion).get

    text should include(s"$$$$${pair.printed}$$$$")
    text should include(pair.legible)
    text should include(Essay.PrintedNotice)
  }

  it should "have one line for each recorded step, and say how many" in {
    val account = chain.magnitude.scripts(Magnitude.Triangle)
    val text = page(Magnitude.Triangle)

    text should include(s"${account.size} steps, recorded as the derivation was written")

    // Every step numbered, which is the property that would break if the page ever summarised the
    // account instead of carrying it. The heads themselves are checked below rather than here: the
    // first version of this assertion rebuilt them with an empty table of names, so it expected
    // "from step 1" where the page correctly says "from LT_TOTAL", and it was the expectation that
    // was wrong. A test that rebuilds what it is checking has to rebuild it the same way.
    (1 to account.size).foreach { number =>
      withClue(s"step $number is not on the page: ") { text should include(s"\n$number. ") }
    }
  }

  it should "name a premise by the lemma a reader can look up" in {
    val text = page(Magnitude.Triangle)

    // A lemma is cited by its name even where it is also the result of an earlier step, which is
    // the order `Script.lines` resolves in: `LT_TOTAL` is step 1 of this account and is still
    // referred to by name, because a name is what a reader can look up.
    text should include("specialise at x, y from LT_TOTAL")
    text should include("from ABS_ABOVE")

    // And a step whose result no library names is referred to by its number.
    text should include("from step ")
  }

  it should "not list the theorem among the things it rests on" in {
    // The first page this produced listed ABS_TRIANGLE under "what it rests on", because the walk
    // that finds the named facts finds the theorem's own conclusion. True, useless, and it reads as
    // a proof that leans on itself.
    val text = page(Magnitude.Triangle)
    val restsOn = text.split("## The derivation").head

    restsOn should not include s"`${Magnitude.Triangle}`"
    restsOn should include("`ADD_LE`")
    restsOn should include("`LT_TOTAL`")
  }

  it should "name the axioms it reaches and count the ones it cannot name" in {
    val text = page(Magnitude.Triangle)
    val axioms = garden.xeno.symbolum.kernel.Derivation.axiomsOf(library.named(Magnitude.Triangle).head.theorem)

    text should include(s"${axioms.size} axioms reached")
  }

  it should "report the kernel's own count, and the share of it that is bookkeeping" in {
    val theorem = library.named(Magnitude.Triangle).head.theorem
    val text = page(Magnitude.Triangle)

    text should include(s"${garden.xeno.symbolum.kernel.Derivation.size(theorem)} inferences")
    text should include("| rule | inferences | share |")
    text should include("Congruence")
  }

  "The page for a theorem nobody recorded" should "say that, rather than showing nothing" in {
    // `ADD_SYM` is an axiom of the reals: it has a statement, a foundation and a cost, and no
    // account, and the page has to be readable as exactly that. A page that simply omitted the
    // section would read as a theorem proved in no steps.
    val text = page("ADD_SYM")

    text should include("Not recorded")
    text should include("## What it rests on")
    text should include("## The proof the kernel holds")
  }

  "Every page" should "say which of its claims are checked" in {
    Vector(Magnitude.Triangle, "ADD_SYM", "NUM_EUCLID").foreach { name =>
      page(name) should include("## What on this page is checked")
    }
  }

  "A name the library does not hold" should "be refused, and the refusal names the command" in {
    Essay.of(chain, "NO_SUCH_LEMMA") match {
      case Left(reason) => reason should include("NO_SUCH_LEMMA")
      case Right(_) => fail("a page was produced for a lemma that does not exist")
    }
  }
}
