# Numerics

**EXCERPT — for anyone scanning the index:**
The two numerical capabilities in `modules/core` that are not written here, what library they rest
on and what that costs anyone who depends on the published artifact, and the line between a number
and a theorem that the arrangement exists to hold. It does not explain the computer algebra system,
which is [../README.md](../README.md), and it does not argue the trust boundary, which is
[architecture.md](architecture.md).

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## Two capabilities, both untrusted

| What | Where | What it rests on |
|---|---|---|
| The discrete Fourier transform of a real signal | `garden.xeno.symbolum.Spectrum` | `breeze.signal.fourierTr`, which is JTransforms |
| The dominant eigenvalue of a matrix with no negative entry | `garden.xeno.symbolum.Perron` | `breeze.linalg.eig`, which is LAPACK's `dgeev` |

Both are in `modules/core`, which is the half of this repository that nothing on the proof side
believes. That is not a detail of where the files landed; it is the whole arrangement. **No library
anywhere produces `|- det (A * B) = det A * det B`**, so a number out of one is evidence and can
never be a step in a derivation. `NumericIsolationSpec` asserts it rather than trusting it: it scans
`kernel`, `logic`, `theories`, `tactics` and `checker` for any mention of the library and for any
mention of these two files, and fails naming what it found.

The build does most of that work already. `kernel`, `logic` and `theories` declare no path to
`core`, so Breeze is not on their compilation classpath at all. `tactics` is the exception and it is
a structural one: it depends on `core` **and** on `theories`, because it is the module where the
algebra proposes and the kernel checks, so Breeze reaches it transitively and no build setting can
prevent that without severing the join the module exists for. The source scan is what covers that
gap, and it is weaker than a build constraint in exactly one way worth naming: it catches an import
somebody adds on a Tuesday with a good reason, and it would miss a reflective load.

## What stays exact, and why the temptation is real

Two things in this repository do numerical work and are **not** moving onto a float library.

**`garden.xeno.symbolum.Relation`** finds integer relations by lattice reduction, in `BigDecimal` and exact
rationals. It works at a hundred to two hundred significant digits, because a relation among `n`
values with coefficients of size `M` happens by accident once `n log10(M)` reaches the digits the
values carry. At `Double`'s sixteen the method is not imprecise, it returns noise; `RelationSpec`
measures exactly that, with the minimal polynomial of `sqrt2 + sqrt3 + sqrt5` coming back as nine
random-looking numbers at sixteen digits and as the right polynomial at forty.

**`garden.xeno.symbolum.theories.Farkas`** searches for a linear-arithmetic certificate by pivoting over a
`Rational` that is a pair of `BigInt`. A certificate that is nearly a certificate is refused by the
ring step afterwards, so what a floating-point search would produce is a refusal with no rounding
error visible anywhere in it. It is also on the **proof** side and therefore could not take the
dependency even if the arithmetic allowed it.

Both are named in `NumericIsolationSpec`, which checks that `Farkas` still says `BigInt` and never
says `Double`, and that `Relation` still says `BigDecimal` and never says `breeze`. The point of
putting an assertion on something so obvious is that the temptation is to unify three kinds of
arithmetic onto one library, and the reason not to is in two files rather than in one place a
reader would think to look.

## The dependency, and what it costs a consumer

`modules/core` is published as `garden.xeno:symbolum-core`, so its dependencies are what a
consumer downloads. The artifact chosen is **`org.scalanlp:breeze:2.1.0`**, and the two alternatives
were rejected for measurable reasons rather than taste:

- **`breeze-natives`** bundles the netlib-java native binaries, tens of megabytes of
  platform-specific payload, to buy a faster BLAS. Nothing here has a measurement asking for one,
  and `breeze` alone resolves to `dev.ludovic.netlib`, which uses a native BLAS when the machine
  already has one and otherwise runs a pure-JVM translation. **Nothing in this repository requires
  a native library to be installed.** On the machine this was measured on there is no native LAPACK,
  and `dev.ludovic.netlib` says so on stderr the first time an eigenvalue is asked for, then falls
  back and answers.
- **`breeze-viz`** is plotting, and has no consumer.

The transitive closure the dependency adds, read off the resolved classpath on 2026-09-12 against
the jars in the Coursier cache rather than estimated. Eighteen jars, **24.14 MB**:

| Jar | Size | What it is |
|---|---|---|
| `breeze_3` | 10.27 MB | the library itself |
| `spire_3` + macros, platform, util | 5.10 MB | the numeric type classes Breeze is built on |
| `cats-kernel_3` | 2.48 MB | under spire |
| `commons-math3` | 1.94 MB | |
| `arpack_combined_all` | 1.14 MB | the translated Fortran under arpack |
| `JTransforms` | 1.12 MB | the transform itself |
| `algebra_3` | 0.82 MB | under spire |
| `dev.ludovic.netlib` lapack, blas, arpack | 0.95 MB | the pure-JVM linear algebra |
| `JLargeArrays` | 0.22 MB | under JTransforms |
| `opencsv`, `slf4j-api`, `scala-collection-compat`, `breeze-macros_3` | 0.08 MB | |

Two entries are worth reading rather than skipping. **`opencsv` is a CSV reader**, which nothing
here wants and which arrives because `breeze.linalg.csvread` ships in the same jar as the
eigenvalues. And **spire with cats-kernel and algebra is 8.4 MB**, a third of the total and the
largest block after Breeze itself, because Breeze's numeric type classes are built on them.

**Whether publication itself should be revisited is not decided here.** Adding a dependency to a
published artifact changes what every consumer pulls in, and this file records the consequence so
that somebody can decide, which is a different act from deciding it.

## The conventions, which are numpy's on purpose

`Spectrum.of` is `numpy.fft.fft` and `Spectrum.ofReal` is `numpy.fft.rfft`: the same exponent sign,
the same absence of a scale factor, and the same `n / 2 + 1` bins by integer division. The agreement
is deliberate. The work that named these two capabilities as blockers reads its spectra out of
`numpy.fft`, and a transform differing by a conjugation would agree on every magnitude and disagree
on every phase, which is the shape of error that survives a test suite. `SpectrumSpec` pins the sign
with a shifted impulse, whose transform is `exp(-2 pi i m n0 / n)` and which is the one case in that
file whose expected value changes if the sign does.

`Spectrum.ofReal` **costs what the whole transform costs**, because it is the whole transform with
the redundant half dropped. Breeze exposes no real-input transform: `fourierTr` interleaves the
samples into a complex array and calls `complexForward`. Reaching past Breeze to JTransforms'
`realForwardFull` would buy back about a factor of two in time and memory and would mean depending
on a library Breeze is entitled to change underneath. Nobody has measured a need for that factor.

## The one mutable value, and why it is the only one

Scala here is a functional language and both files are written that way: no `var`, no `while`, no
`return`, no `null`, no `asInstanceOf`, no mutable collection. The outcomes are values of a sealed
type, the refusals are values rather than exceptions, and the checks are expressions.

There is exactly one exception and it is three lines of `Spectrum.of`. `breeze.linalg.DenseVector`
takes an `Array[Double]` and there is no Breeze entry point that takes an immutable sequence, so the
alternative is not a purer call but no call. The array is built by `Array.tabulate` inside that
expression, read by the library, which copies it into a temporary of its own before touching
anything, and unreachable afterwards: immutable in, immutable out, nothing shared between calls, no
caller able to observe it.

Everything a caller sees is `IArray[Double]`, which is the primitive array with no mutation in its
surface, and the measurement that chose it over `Vector[Double]` is below. `Perron` uses
`Vector[Vector[Double]]` instead, because its matrix is `n^2` numbers under `O(n^3)` work and the
representation is a vanishing share of the cost; `Perron.settle` and `Perron.check` take the matrix
as the linear map it is, `Vector[Double] => Vector[Double]`, so that the numeric library does not
appear in their signatures at all.

The one place an exception is caught is `breeze.linalg.eig`, and it catches `NotConvergedException`
by name rather than using `Try`. `Try` collects everything non-fatal, and there is no honest outcome
to map a defect onto: the refusals have already thrown out every matrix `dgeev` documents an
argument error for, so anything else is a mistake in this repository and turning it into
`NotConverged` would be merging a defect with a refusal.

## The outcomes, and the two obligations they answer

**Agreement in numbers is reported as agreement in numbers and never as a proof.** Both files
say it in their first paragraphs, and the surfaces carry it: `Spectrum.Bins.agreesWith` returns the
largest difference bin by bin and has **no opinion about where the tolerance is**, because the
answer depends on `n` and on the size of the largest bin; `Perron.Dominant.residual` is the largest
entry of `A v - lambda v` and is an observation about how well the numbers satisfy the equation,
which is not the same act as proving that they do.

**An absent answer is never reported as a negative one.** The outcomes are kept apart the way
`Refutation` keeps its seven apart:

| `Spectrum` | |
|---|---|
| `Bins` | the transform ran. A bin that reads zero is a measurement: a constant signal really does have nothing outside bin zero |
| `Unusable` | the question could not be put. An empty signal, or a sample that is `NaN` or infinite, which would poison every bin because every bin is a sum over every sample |

| `Perron` | |
|---|---|
| `Dominant` | the decomposition ran and its answer is a Perron root. **An eigenvalue of zero is one of these**: a nilpotent matrix with no negative entry has spectral radius exactly zero, and that is a growth rate of nothing rather than a missing answer |
| `Undecided` | the decomposition ran and what came back is not a Perron root, which on a matrix with no negative entry means the arithmetic contradicted the theorem. The message names which of the three checks failed and by how much |
| `NotConverged` | the QR iteration gave up. A different move from `Undecided`: this one is about the matrix being hard |
| `Unusable` | the question could not be put: not square, no rows, ragged, non-finite, or negative somewhere |

The last of those is the one that reads as pedantry and is not. Perron-Frobenius is a theorem about
matrices with no negative entry. Run on a matrix with one, `dgeev` still returns a largest-modulus
eigenvalue, and that number is not a growth rate and its eigenvector can be anything. Answering
would be worse than refusing.

## What is not built, with the count instead

- **The inverse transform.** `breeze.signal.iFourierTr` is one line away and has zero named
  consumers.
- **The two-dimensional transform**, and windowing: zero named consumers.
- **The full spectrum of eigenvalues**, rather than the dominant one: zero named consumers. `eig`
  computes them all anyway and `Perron` throws the rest away, so the cost of adding it later is the
  surface and not the arithmetic.
- **A test for `Perron.NotConverged`.** It is the one branch in either file that nothing covers:
  `dgeev` does not fail to converge on any matrix small enough to put in a suite, and the seam that
  `settle` and `check` open for the `Undecided` gates does not reach it, because the failure happens
  inside the library. `Spectrum` is at 100% statement coverage and `Perron` at 92.62%, and those
  eleven uncovered statements are that branch and its message.
- **Uniqueness of the Perron vector.** `Perron.Dominant.subdominant` is the largest modulus among
  the other eigenvalues and is reported so that a caller can see how close the spectrum comes to
  the root, but nothing here decides irreducibility or primitivity, which is what would make the
  vector unique. A caller that needs the vector rather than the number has to read that field.

## Measurements

Taken on 2026-09-12 on an Apple Silicon laptop, with the load average beside each figure because
this machine has read the same test suite at 41 seconds and at 6 minutes 39 in the same afternoon.
**None of these is a test.** A wall-clock assertion here would measure the load rather than the
code, which is why there is not one.

### The transform at N = 2^22

One cosine at an integer frequency, `x[k] = cos(2 pi q k / n)` with `q = 12345`, so the answer is
known: bin `q` should read `n / 2` exactly and every bin but `q` and `n - q` should read zero. Load
average **145 rising to 163** across the run, `-Xmx6g`, one warm-up transform at `2^16` first.

| | round 1 | round 2 | round 3 |
|---|---|---|---|
| `Spectrum.of`, all 4194304 bins | 26.2 s | 13.66 s | 13.64 s |
| `Spectrum.ofReal`, 2097153 bins | 17.2 s | 13.3 s | 12.2 s |

The numbers it produced, which are the part that is not about the machine: bin 12345 came back at
**2097152.000000**, which is `n / 2` to every digit printed, and bin 0 at a magnitude of
**3.15e-10** against a bin of 2.1e6, so 1.5e-16 relative, which is a rounding error and not a peak.
The whole spectrum at that size occupied **1253 MB** of a 6 GB heap.

Thirteen seconds is much more than the arithmetic costs, and the same probe was run again at
**load 35 to 43**, with the stages separated. Best of three each:

| | best of three |
|---|---|
| `Array.tabulate`, the copy `DenseVector` needs | 362 ms |
| `fourierTr` itself | 1179 ms |
| unpacking its result into two `IArray[Double]` | 1626 ms |
| `Spectrum.of` end to end | 2946 ms |

Two things fall out of that and both are worth carrying.

**Load was most of the thirteen seconds.** The same call is 2.9 s at load 40 and 13.6 s at load 150,
which is the factor this repository keeps warning about and the reason there is no timing assertion
anywhere in the suite.

**More than half of what is left is not the transform.** `breeze.signal.fourierTr` returns a
`DenseVector[Complex]`, which at `n = 2^22` is four million boxed objects, and reading them back out
into two primitive arrays costs 1626 ms against the transform's 1179. That is the price of the
Breeze entry point rather than of the FFT: JTransforms underneath writes into an interleaved
primitive array and boxes nothing, so calling it directly would remove the 1626 ms and the 362 ms
copy both, and `realForwardFull` would roughly halve the 1179 as well. **That is a real factor of
three and it is still not being taken**, because it means depending on a library Breeze is entitled
to change underneath, and nothing has yet asked for a 2^22 transform in a loop. If something does,
this is the measurement that says where to go.

### The representation, which is why `IArray`

At `n = 2^22`, holding one array and collecting everything else. Load average **48**, five rounds,
best of each reported because the spread was wide:

| | `IArray[Double]` | `Vector[Double]` |
|---|---|---|
| retained | 35 MB | 115 MB |
| build | 10.5 ms | 271 ms |
| read every entry | 43 ms | 306 ms |

A spectrum is two of these, so the choice is 70 MB against 230 MB and 21 ms of allocation against
half a second, before any transform runs.

### The eigenvalue

Random matrices with entries uniform on `[0, 10)`, one seed, load average **150 to 163**.

| `n` | time | eigenvalue | subdominant | residual |
|---|---|---|---|---|
| 16 | 2.64 s | 82.0967 | 14.65 | 2.5e-14 |
| 64 | 1.12 s | 321.479 | 23.62 | 7.1e-14 |
| 256 | 59.7 s | 1286.05 | 47.81 | 1.8e-12 |

The first row is larger than the second because it paid for class loading and for
`dev.ludovic.netlib` deciding it has no native LAPACK; it is not a measurement of `n = 16`. The
`n = 512` row is missing because the probe was cut off, and the figures that are here are load-bound
rather than cubic: 16 to 64 is a factor of 64 in the arithmetic and reads as a factor of less than
one.

What is not load-bound is the last column. The residual grows with the size and the norm exactly as
a backward-stable method predicts, and at `n = 256` a residual of 1.8e-12 against a norm of about
1280 is 1.4e-15 relatively, which is where `Perron.Residual` was set from.

### The suite

`sbt test` with these two files and their suites in it: **1614 tests green in 27 minutes 11
seconds**, at load average 250. The three suites added run 42 tests, which took 5.2 seconds inside a
109-second invocation on the same machine.
