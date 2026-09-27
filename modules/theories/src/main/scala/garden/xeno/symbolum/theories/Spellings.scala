package garden.xeno.symbolum.theories

import garden.xeno.symbolum.logic.*

/**
 * How every constant of the widest signature is set in print.
 *
 * `Latex` is the mechanism and this is the table: one row per constant, and the rows are what makes
 * a generated page look like mathematics instead of like a transcript. Measured on 2026-09-13 over
 * the library's 278 statements: 82 constants appear in them, 22 carry a notation entry and are
 * spelled by the symbols `Latex.standard` gives those, and **60 carry none** and are spelled here.
 * 231 of the 278 name at least one of the 60, which is why the table is not optional decoration.
 *
 * == One table, and what that costs ==
 *
 * `Notation` is extended by each development as it declares its constants, and this is not: it is
 * assembled in one place over the whole chain. The reason is what a reader does with it. A spelling
 * is a claim about how a constant is written **in the literature**, and the question a reader asks
 * of it is "are these the symbols the books use", which is asked of the table as a page and not of
 * sixty call sites in ten files. `docs/reading-register.md` already lists every constant one per
 * row for the same reason.
 *
 * The cost is that a development added later does not carry its own spellings, and a constant with
 * no row here would silently print as its own name in roman. `LatexSpec` is the guard: it fails
 * when a constant of the signature has no row **and** when a row names a constant the signature
 * does not have, so the table cannot drift in either direction.
 *
 * == Three decisions a reader should be able to disagree with ==
 *
 * **The embedding of the naturals into the reals is visible.** `real_of_num n` is set as
 * `n_{\mathbb{R}}` and not as `n`. Every book writes it as `n`, and that is exactly the problem:
 * `real_of_num n` and a real variable `n` would then print alike while being different terms of
 * different types, and a page whose whole purpose is to be believed must not hide the one step
 * where a natural becomes a real.
 *
 * **`SUC` is `\mathrm{suc}` and not `n + 1`.** They are equal and they are not the same term, and
 * every recurrence over `num` in this library is stated at `SUC n`: a reader comparing the page
 * against the code would find `+1` in one and `SUC` in the other.
 *
 * **`WORD_LENGTH` is not the absolute value's bars.** `\lvert w \rvert` is what a book writes for
 * the length of a word, and `abs` already has those bars here; two constants sharing a spelling is
 * the one ambiguity this table can introduce on its own, so the length is written `\mathrm{len}`.
 */
object Spellings {

  /** The precedence of a relation, matching the notation's `<` and `<=`. */
  private val Relation: Int = 50

  /** The precedence of addition, and of subtraction, matching the notation's. */
  private val Additive: Int = 60

  /** The precedence of multiplication, matching the notation's. */
  private val Multiplicative: Int = 70

  /**
   * The whole chain's table.
   *
   * Grouped the way the developments are, so that a reader checking it against
   * `docs/lemmas.md` reads it in the order the library is listed.
   */
  val standard: Latex =
    Latex.standard
      /* ----------------------------------------------------------- the reals */
      // `operator` and not `delimited` for the four rows below and for `NUM_CONG`: a delimited
      // template must carry marks around its placeholders, and a postfix carries none, so
      // `inv (a + b)` set as `a + b^{-1}`, the inverse of a sum as a sum with an inverse in it.
      // Found by a peer session reading the output of two of them, and by the check in `LatexSpec`
      // for the other three, which is the guard that came out of it.
      .operator("inv", 1, "#1^{-1}", Multiplicative + 5)
      .delimited("abs", 1, "\\lvert #1 \\rvert")
      .delimited("max", 2, "\\max(#1, #2)")
      .delimited("min", 2, "\\min(#1, #2)")
      .delimited("sgn", 1, "\\operatorname{sgn}(#1)")
      .operator("Power", 2, "#1^{#2}", Multiplicative + 5)
      .operator("Divides", 2, "#1 \\mid #2", Relation)
      .binding("Sum", "\\sum_{#b < #2} #1")
      .binding("Prod", "\\prod_{#b < #2} #1")
      /* -------------------------------------------------------- the naturals */
      .delimited("SUC", 1, "\\mathrm{suc}(#1)")
      .delimited("PRE", 1, "\\mathrm{pred}(#1)")
      // `NUM_ADD`, `NUM_MUL`, `NUM_LE` and `NUM_LT` had rows here, `#1 + #2`, `#1 \cdot #2`,
      // `#1 \le #2` and `#1 < #2`, and `docs/adr/0018` removed them by giving the four a notation.
      // A constant the notation spells falls through to it, so the rows were the same decision
      // taken twice, and this table is the place where that was visible first: somebody writing it
      // from the literature gave those four the reals' own marks and deliberately withheld them
      // from the two below, years of convention ahead of the question being asked.
      //
      // Removing them is output-preserving and that was measured rather than assumed: the notation
      // renders `+` and `<` as themselves and `*` and `<=` through `Latex`'s symbol table as
      // `\cdot` and `\le`, and `Notation`'s precedences are the same three numbers as `Additive`,
      // `Multiplicative` and `Relation` below.
      //
      // The two that stay are the two the record refuses to overload, and they keep their rows for
      // exactly that reason: `NUM_SUB` is truncated and `NUM_POW` does not share a shape with
      // `Power`, so neither has a notation to fall through to.
      .operator("NUM_SUB", 2, "#1 \\mathbin{\\dot-} #2", Additive)
      .operator("NUM_POW", 2, "#1^{#2}", Multiplicative + 5)
      // The binomial coefficient, in the one notation every reader of one already knows. It binds
      // tighter than anything it could sit beside, because a `\binom` is a single box on the page
      // however large its two arguments are, so nothing inside it needs a bracket and nothing
      // outside it can be captured by it.
      .operator("NUM_CHOOSE", 2, "\\binom{#1}{#2}", Multiplicative + 5)
      .operator("real_of_num", 1, "#1_{\\mathbb{R}}", Multiplicative + 5)
      .binding("NUM_SUM", "\\sum_{#b < #2} #1")
      .binding("NUM_PROD", "\\prod_{#b < #2} #1")
      /* ------------------------------------------------- number theory on num */
      .operator("NUM_DIVIDES", 2, "#1 \\mid #2", Relation)
      .operator("NUM_DIV", 2, "#1 \\operatorname{div} #2", Multiplicative)
      .operator("NUM_MOD", 2, "#1 \\bmod #2", Multiplicative)
      .delimited("NUM_GCD", 2, "\\gcd(#1, #2)")
      // `operator` and not `delimited`, which is the constructor a postfix asks for and the one
      // this table's own contract refuses: a delimited template has to carry the marks around its
      // arguments, and `#1!` carries none, so `NUM_FACT (NUM_ADD a b)` would print `a + b!`. As an
      // operator the context brackets it, which is how `Power` handles the same shape. Tighter than
      // multiplication, like a power.
      .operator("NUM_FACT", 1, "#1!", Multiplicative + 5)
      // `delimited`, because a three-argument function has no infix reading at all and the
      // contract that refuses `NUM_FACT` here is the one that admits this: the template carries
      // its own marks around every argument, so nothing outside it can bind tighter.
      .delimited("NUM_BETA", 3, "\\beta(#1, #2, #3)")
      /* ------------------------------------------------- the arithmetisation */
      // The triangular numbers are written as the sum they are rather than with a binomial,
      // because the definition here is the recursion and not the closed form: setting them as
      // `\\binom{n+1}{2}` would print a division this development deliberately never performs.
      .operator("NUM_TRI", 1, "T_{#1}", Multiplicative + 5)
      .delimited("NUM_PAIR", 2, "\\langle #1, #2 \\rangle")
      // Delimited and not a pair of angle brackets again: a code IS a pair, with a tag and a
      // successor around it, and setting the two the same way would hide the one difference a
      // reader of a coded term needs to see.
      .delimited("NUM_CODE", 2, "\\lceil #1, #2 \\rceil")
      // The four projections. The pair's are the usual projections and the code's are named, so
      // that a reader of a coded formula can see which of the two shapes is being opened.
      .delimited("NUM_FST", 1, "\\pi_1(#1)")
      .delimited("NUM_SND", 1, "\\pi_2(#1)")
      .delimited("NUM_TAG", 1, "\\operatorname{tag}(#1)")
      .delimited("NUM_PAYLOAD", 1, "\\operatorname{arg}(#1)")
      // A predicate and not an operator: `NUM_TERM n` says a number codes a term, and setting
      // it as a relation would suggest it relates two things.
      .delimited("NUM_TERM", 1, "\\operatorname{Tm}(#1)")
      .delimited("NUM_FORM", 1, "\\operatorname{Fm}(#1)")
      // The object language's numeral for a meta-level number, set with the corner quotes the
      // literature uses for a code, because that is what it is.
      .delimited("NUM_NUMERAL", 1, "\\ulcorner #1 \\urcorner")
      // `operator` and not `delimited`, for the reason `NUM_FACT` gives four rows up and which the
      // guard caught here: a delimited template has to carry its own marks around EVERY argument,
      // and `#3` sits outside the brackets. As an operator the context brackets it.
      .operator("NUM_SUBST_TERM", 3, "#3[#1 := #2]", Multiplicative + 5)
      .operator("NUM_SUBST_FORM", 3, "#3[#1 := #2]", Multiplicative + 5)
      .delimited("NUM_FREE_TERM", 2, "\\operatorname{free}(#1, #2)")
      .delimited("NUM_FREE_FORM", 2, "\\operatorname{free}(#1, #2)")
      .delimited("NUM_CLOSED", 1, "\\operatorname{closed}(#1)")
      .delimited("NUM_LOGIC", 1, "\\operatorname{Log}(#1)")
      .delimited("NUM_STEP", 3, "\\operatorname{step}(#1, #2, #3)")
      .delimited("NUM_PROOF", 2, "\\operatorname{Prf}(#1, #2)")
      .delimited("NUM_PROV", 1, "\\operatorname{Prov}(#1)")
      // The two the deduction theorem needed. `step` and `Prov` with the hypothesis in front of a
      // turnstile, which is how a derivation from an assumption is written everywhere else.
      .delimited("NUM_STEP_FROM", 4, "\\operatorname{step}_{#1}(#2, #3, #4)")
      .delimited("NUM_PROV_FROM", 2, "\\operatorname{Prov}_{#1}(#2)")
      .delimited("NUM_PA", 1, "\\operatorname{PA}(#1)")
      // The value of a term and the truth of a formula at an environment, which is how the
      // semantics of a first-order language is written: the double brackets for the value and a
      // satisfaction turnstile for the truth, the environment on the left of it.
      .delimited("NUM_VALUE", 2, "[\\![#1]\\!]_{#2}")
      // `operator` and not `delimited`: neither argument is inside marks of its own.
      .operator("NUM_TRUE", 2, "#2 \\vDash #1", Relation)
      .delimited("NUM_TRI_GRAPH", 0, "\\ulcorner v_0 + v_0 = v_1 \\cdot S v_1 \\urcorner")
      // The object language's derived connectives. Set as named operations rather than with the
      // meta level's own symbols, which is the point of the row: `NUM_AND p q` is a NUMBER that
      // codes a conjunction, and writing it `#1 \\wedge #2` would put it in the same shape as the
      // ambient connective it is a code for. `\\operatorname{Tm}` and `\\operatorname{Fm}` three rows
      // up made the same choice for the same reason.
      .delimited("NUM_AND", 2, "\\operatorname{and}(#1, #2)")
      .delimited("NUM_OR", 2, "\\operatorname{or}(#1, #2)")
      .delimited("NUM_EXISTS", 2, "\\operatorname{ex}(#1, #2)")
      // The three that carry a witness index take it in a subscript, which is where
      // `NUM_STEP_FROM` puts its own parameter. `ball` and `bex` rather than a bounded quantifier
      // set with a bound under it: the bound is an argument here, not a decoration, and a reader
      // who cannot see it as an argument cannot check the row against the statement.
      .delimited("NUM_LESS", 3, "\\operatorname{lt}_{#1}(#2, #3)")
      .delimited("NUM_ALL_BELOW", 4, "\\operatorname{ball}_{#1}(#2, #3, #4)")
      .delimited("NUM_EXISTS_BELOW", 4, "\\operatorname{bex}_{#1}(#2, #3, #4)")
      // The modulus is the FIRST argument, and this row had it last until the rendering was read
      // against `Modular`'s own docstring: "`NUM_CONG k m n`", and "`NUM_CONG k` takes its modulus
      // first, and that is the useful currying". The wrong order set beautifully and said something
      // else, which is the failure this table can produce on its own and no test here can catch.
      .operator("NUM_CONG", 3, "#2 \\equiv #3 \\pmod{#1}", Relation)
      .delimited("NUM_PRIME", 1, "\\mathrm{prime}(#1)")
      .delimited("NUM_TOTIENT", 1, "\\varphi(#1)")
      .delimited("NUM_VALUATION", 2, "\\nu_{#1}(#2)")
      .delimited("NUM_FLOOR", 1, "\\lfloor #1 \\rfloor")
      .delimited("NUM_CEIL", 1, "\\lceil #1 \\rceil")
      /* ------------------------------------------------------------ the pair */
      // Angle brackets rather than round ones, so that `FST (PAIR x y)` sets as
      // `\pi_1(\langle x, y \rangle)` and not as `\pi_1((x, y))`, where the reader has to decide
      // which of the two pairs of brackets is the projection's.
      .delimited("PAIR", 2, "\\langle #1, #2 \\rangle")
      .delimited("FST", 1, "\\pi_{1}(#1)")
      .delimited("SND", 1, "\\pi_{2}(#1)")
      .delimited("mk_prod", 1, "\\mathrm{mk\\_prod}(#1)")
      .delimited("dest_prod", 3, "\\mathrm{dest\\_prod}(#1, #2, #3)")
      .delimited("mk_pair", 4, "\\mathrm{mk\\_pair}(#1, #2, #3, #4)")
      /* ------------------------------------------------------------ the word */
      .delimited("WORD_LENGTH", 1, "\\mathrm{len}(#1)")
      // The index is bracketed where it is a sum, which is redundant inside the square brackets
      // and never wrong: one row carries one precedence for all of its places.
      .operator("WORD_NTH", 2, "#1[#2]", Multiplicative + 5)
      .delimited("WORD_MAKE", 2, "\\mathrm{word}(#1, #2)")
      .delimited("WORD_ROTATE", 2, "\\mathrm{rot}_{#1}(#2)")
      .delimited("WORD_PAD", 0, "\\square")
      .delimited("mk_word", 1, "\\mathrm{mk\\_word}(#1)")
      .delimited("dest_word", 1, "\\mathrm{dest\\_word}(#1)")
      /* --------------------------------------------- the concatenation and its relations */
      // Juxtaposition is what a book writes for concatenation and it is what this sets, with a thin
      // space so that `uv` does not read as one name. The precedence is multiplication's because
      // the operation is a monoid's and a reader bracketing it will bracket it that way; it is NOT
      // spelled with a product symbol, for the reason `docs/adr/0018` refuses `*` in the concrete
      // syntax, which is that concatenation is not multiplication.
      .operator("WORD_CONCAT", 2, "#1 \\, #2", Multiplicative)
      .delimited("WORD_EMPTY", 0, "\\varepsilon")
      // Angle brackets, so that a one-letter word is visibly a word and not its letter: `\langle x
      // \rangle` against `x`, which is the distinction every statement here turns on.
      .delimited("WORD_SINGLETON", 1, "\\langle #1 \\rangle")
      // The three relations get the marks a book gives them, which are not the subset signs: a
      // prefix is written with the square variants precisely because a factor is not a subset.
      .operator("WORD_PREFIX", 2, "#1 \\sqsubseteq_{p} #2", Relation)
      .operator("WORD_SUFFIX", 2, "#1 \\sqsubseteq_{s} #2", Relation)
      .operator("WORD_FACTOR", 2, "#1 \\sqsubseteq #2", Relation)
      // A step of the system, and membership of its right forward closure. The arrow carries the
      // system as a subscript because both are relative to one: `u \to_R v` is the shape every
      // rewriting text uses, and dropping the subscript would print two different systems the same.
      .operator("WORD_STEP", 3, "#2 \\to_{#1} #3", Relation)
      .operator("WORD_RFC", 2, "#2 \\in \\mathrm{RFC}(#1)", Relation)
      /* ------------------------------------------------- the list interface over `word` */
      // `docs/adr/0038` decides that a list here is an orientation on `word` and not a carrier of
      // its own, and these three spellings are where a reader meets that: the cons gets the double
      // colon every text writes it with, at the precedence of concatenation because it IS a
      // concatenation, and the empty list is `\varepsilon` above because it IS `WORD_EMPTY`.
      .operator("LIST_CONS", 2, "#1 :: #2", Multiplicative)
      .delimited("LIST_HEAD", 1, "\\mathrm{hd}(#1)")
      .delimited("LIST_TAIL", 1, "\\mathrm{tl}(#1)")
      .delimited("LIST_FOLD", 3, "\\mathrm{fold}_{#1}(#2, #3)")
      /* ---------------------------------------------------------- the matrix */
      .delimited("MAT2", 4, "\\begin{pmatrix} #1 & #2 \\\\ #3 & #4 \\end{pmatrix}")
      .delimited("MAT_ID", 0, "I")
      .delimited("MAT_DET", 1, "\\det(#1)")
      .operator("MAT_TRANSPOSE", 1, "#1^{\\mathsf{T}}", Multiplicative + 5)
      .operator("MAT_ADD", 2, "#1 + #2", Additive)
      .operator("MAT_MUL", 2, "#1 \\cdot #2", Multiplicative)
      .operator("MAT_SMUL", 2, "#1 \\cdot #2", Multiplicative)
      .delimited("MAT_E11", 1, "(#1)_{11}")
      .delimited("MAT_E12", 1, "(#1)_{12}")
      .delimited("MAT_E21", 1, "(#1)_{21}")
      .delimited("MAT_E22", 1, "(#1)_{22}")
      /* ------------------------------------------------------- the integers */
      // Set with the ordinary signs and not with a marked `+` of their own, which is the opposite
      // of what the constants are named: `INT_ADD` carries a prefix because `docs/adr/0018`'s
      // overloading stops at two types and a third candidate would make every existing statement
      // ambiguous to the elaborator. Nothing here is elaborated. A reader of `docs/lemmas.md` has
      // the statement's types beside it, and setting `\mathbin{+_{\mathbb{Z}}}` would put the
      // implementation's caution into a document that has no parser in it.
      .operator("INT_ADD", 2, "#1 + #2", Additive)
      .operator("INT_MUL", 2, "#1 \\cdot #2", Multiplicative)
      .operator("INT_NEG", 1, "-#1", Multiplicative + 5)
      .delimited("INT_ZERO", 0, "0_{\\mathbb{Z}}")
      .delimited("INT_ONE", 0, "1_{\\mathbb{Z}}")
      .operator("INT_DIVIDES", 2, "#1 \\mid #2", Relation)
      .operator("INT_LE", 2, "#1 \\leq #2", Relation)
      .operator("INT_OF_NUM", 1, "#1_{\\mathbb{Z}}", Multiplicative + 5)
      // The quotient's own vocabulary, set as the naming rather than as mathematics. A class and
      // its chosen representative are the construction showing through, and a reader meeting one
      // in a statement wants to see which of them it is rather than a bracket that hides it.
      .delimited("INT_OF_PAIR", 1, "[#1]")
      .delimited("INT_OF_PAIR_repr", 1, "\\mathrm{repr}(#1)")
      .operator("INT_SAME", 2, "#1 \\sim #2", Relation)
      /* ------------------------------------------------- the integers inside the reals */
      // `\iota` and not `#1_{\mathbb{R}}`, which is what `real_of_num` above carries, and the reason
      // is a rendering rather than taste. `NUM_ADD` falls through to the notation and `INT_ADD`
      // carries the row above, so both set as `+`; sharing the subscript would then make
      // `NUM_REAL_ADD` and `INT_REAL_ADD` render to the **same string** up to the names of their
      // variables, `(m + n)_{\mathbb{R}} = m_{\mathbb{R}} + n_{\mathbb{R}}` in both cases.
      // Rendered and compared on 2026-09-18 rather than argued. That is the ambiguity the docstring
      // at the top calls the one this table can introduce on its own, and the inclusion map is
      // written `\iota` in algebra anyway.
      //
      // The reading that does NOT decide it, written down because it is the one that suggests
      // itself: `INT_REAL_OF_NUM` would not print as a tautology under a shared subscript, since
      // `INT_OF_NUM` keeps its own `\mathbb{Z}` and the left side comes out `(n_{\mathbb{Z}})_
      // {\mathbb{R}}`. The facts that collide are the homomorphism's, not the triangle.
      .delimited("real_of_int", 1, "\\iota(#1)")
      .delimited("mk_int", 1, "\\mathrm{mk\\_int}(#1)")
      .delimited("dest_int", 2, "\\mathrm{dest\\_int}(#1, #2)")
      /* --------------------------------------------------------- the rationals */
      // In the chain's signature since phase 5 put the construction of the reals below them, and set
      // the way the integers are and for the same reason: the ordinary signs, with the quotient's own
      // vocabulary shown as the naming it is.
      .operator("RAT_ADD", 2, "#1 + #2", Additive)
      .operator("RAT_MUL", 2, "#1 \\cdot #2", Multiplicative)
      .operator("RAT_NEG", 1, "-#1", Multiplicative + 5)
      .operator("RAT_INV", 1, "#1^{-1}", Multiplicative + 5)
      .delimited("RAT_ZERO", 0, "0_{\\mathbb{Q}}")
      .delimited("RAT_ONE", 0, "1_{\\mathbb{Q}}")
      .operator("RAT_LE", 2, "#1 \\leq #2", Relation)
      .operator("RAT_LT", 2, "#1 < #2", Relation)
      .operator("RAT_OF_NUM", 1, "#1_{\\mathbb{Q}}", Multiplicative + 5)
      .delimited("RAT_OF_PAIR", 1, "[#1]")
      .delimited("RAT_OF_PAIR_repr", 1, "\\mathrm{repr}(#1)")
      .operator("RAT_SAME", 2, "#1 \\sim #2", Relation)
      .delimited("mk_rat", 1, "\\mathrm{mk\\_rat}(#1)")
      .delimited("dest_rat", 2, "\\mathrm{dest\\_rat}(#1, #2)")
      /* ------------------------------------------------------------- the cuts */
      // Set as the construction showing through, by name, and not with the reals' signs. Since
      // `docs/adr/0053` each primitive of the reals is defined as one of these, so `real_add` and
      // `CUT_ADD` are the same function; a statement written with the second is one about how the
      // reals were built, and a reader should see that it is.
      .delimited("IS_CUT", 1, "\\mathrm{cut}(#1)")
      .delimited("mk_cut", 1, "\\mathrm{mk\\_cut}(#1)")
      .delimited("dest_cut", 2, "\\mathrm{dest\\_cut}(#1, #2)")
      .delimited("CUT_OF_RAT", 1, "\\mathrm{cut}_{<}(#1)")
      .delimited("CUT_LE", 2, "\\mathrm{cut\\_le}(#1, #2)")
      .delimited("CUT_LT", 2, "\\mathrm{cut\\_lt}(#1, #2)")
      .delimited("CUT_ADD", 2, "\\mathrm{cut\\_add}(#1, #2)")
      .delimited("CUT_NEG", 1, "\\mathrm{cut\\_neg}(#1)")
      .delimited("CUT_MUL", 2, "\\mathrm{cut\\_mul}(#1, #2)")
      .delimited("CUT_PMUL", 2, "\\mathrm{cut\\_pmul}(#1, #2)")
      .delimited("CUT_INV", 1, "\\mathrm{cut\\_inv}(#1)")
      .delimited("CUT_PINV", 1, "\\mathrm{cut\\_pinv}(#1)")
      /* --------------------------------------------- limits and the series */
      // Convergence is a relation, because `converges s l` says the sequence approaches the value
      // and `\to` is what says that; a function-application spelling would hide it. The index
      // under the arrow is what a book writes and is not here: this arrow has no place to put one,
      // and inventing a subscript the term does not carry is the failure `NUM_CONG`'s row records.
      .operator("converges", 2, "#1 \\to #2", Relation)
      // `operator` and not `delimited`, for the reason `NUM_FACT`'s row gives: a delimited template
      // must carry its own marks around every argument and `\lim #1` carries none, so
      // `lim s + 1` would set as the limit of a sum.
      .operator("lim", 1, "\\lim #1", Multiplicative + 5)
      // Delimited, because the books write "the series diverges" in words after the series and a
      // template ending on its place promises nothing about where that place ends; the word in
      // front of a bracket is the same claim with its marks on both sides.
      .delimited("diverges", 1, "\\mathrm{diverges}(#1)")
      // The four transcendental functions, each as an operator tighter than multiplication rather
      // than as a delimited template: `\\sin(x)` is what a delimited row would give and
      // `\\sin x + 1` is what the books write, so the argument is bracketed by the context and
      // only where the context needs it.
      .operator("exp", 1, "\\exp #1", Multiplicative + 5)
      .operator("ln", 1, "\\ln #1", Multiplicative + 5)
      // The radical, with its argument under the bar, which is what makes the argument's extent
      // visible without brackets: `\sqrt{x * x}` needs none where `sqrt (x * x)` does.
      .delimited("sqrt", 1, "\\sqrt{#1}")
      .operator("sin", 1, "\\sin #1", Multiplicative + 5)
      .operator("cos", 1, "\\cos #1", Multiplicative + 5)
      .operator("sinh", 1, "\\sinh #1", Multiplicative + 5)
      .operator("cosh", 1, "\\cosh #1", Multiplicative + 5)
      // Continuity at a point, which books write in words and no symbol settles. Delimited, so the
      // function and the point are each bracketed by the template rather than by the context.
      .delimited("continuous", 2, "\\operatorname{cont}(#1, #2)")
      .delimited("continuous_within", 4, "\\operatorname{cont}_{[#2, #3]}(#1, #4)")
      // The derivative at a point, in words as continuity is and for the same reason. Not
      // `f'(x) = m`: the constant is a proposition, and an equation inside a delimited template
      // reads wrongly under a negation, where `\neg f'(x) = 0` hides which side is denied.
      .delimited("derivative", 3, "\\operatorname{deriv}(#1, #2, #3)")
      .delimited("derivative_within", 5, "\\operatorname{deriv}_{[#2, #3]}(#1, #4, #5)")
      // The integral and its two relations in words, for the reason `derivative` is: two of the
      // three are propositions, and the value is `select` applied to one of them.
      .delimited("fine_sum", 5, "\\operatorname{finesum}(#1, #2, #3, #4, #5)")
      .delimited("has_integral", 4, "\\operatorname{hasintegral}(#1, #2, #3, #4)")
      .delimited("integral", 3, "\\operatorname{integral}(#1, #2, #3)")
      /* ------------------------------------------------ the set defined by rules */
      // Both at arity ONE though each is written with two arguments, and that is the faithful
      // reading rather than a shortcut: `INDUCTIVE f` IS the set, and `INDUCTIVE f x` is that set
      // applied to a point, so a row at arity two would set membership as a two-place operator and
      // hide that the first argument alone denotes something. `\mu` is what the literature writes
      // for a least fixed point, and `mono` is a predicate on the operator, not on a pair.
      .delimited("INDUCTIVE", 1, "\\mu(#1)")
      .delimited("MONOTONE", 1, "\\operatorname{mono}(#1)")
      // Three arguments and not four: `REACH R A x` is the SET of steps reachable from `x`,
      // and the fourth argument is that set applied to one of them. Same reading as the two
      // rows above, and the subscripts are where the relation and the counted sub-relation
      // belong, since a reader tracks the step and not them.
      .delimited("REACH", 3, "\\operatorname{reach}^{#2}_{#1}(#3)")
      /* ---------------------------------------------------- resolution as an object */
      // Words rather than symbols, because the literature has none that all four share: a proof
      // complexity paper writes `w(\pi)` for the width of a refutation `\pi`, and here there is no
      // `\pi`, only the functions and the index count it is made of. The width's subscript is the
      // clause lengths and its argument the count, which is how `NUM_PROD` above is laid out.
      .delimited("RES_SAT", 5, "\\operatorname{sat}_{#1}(#2, #3, #4, #5)")
      .delimited("RES_JUSTIFIED", 5, "\\operatorname{just}(#1, #2, #3, #4, #5)")
      .delimited("RES_REFUTATION", 5, "\\operatorname{ref}(#1, #2, #3, #4, #5)")
      .delimited("RES_WIDTH", 2, "\\operatorname{w}_{#1}(#2)")
      /* ------------------------------------------ what the type definitions left */
      .delimited("IND_0", 0, "\\mathbb{I}_{0}")
      .delimited("IND_SUC", 1, "\\mathrm{ind\\_suc}(#1)")
      .delimited("NUM_REP", 1, "\\mathrm{num\\_rep}(#1)")
      .delimited("mk_num", 1, "\\mathrm{mk\\_num}(#1)")
      .delimited("dest_num", 1, "\\mathrm{dest\\_num}(#1)")
}
