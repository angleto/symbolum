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
| The discrete Fourier transform of a real signal | `garden.xeno.symbolum.Spectrum` | `org.jtransforms.fft.DoubleFFT_1D` |
| The dominant eigenvalue of a matrix with no negative entry | `garden.xeno.symbolum.Perron` | `org.apache.commons.math3.linear.EigenDecomposition` |

Both rested on Breeze until 2026-09-16, on `breeze.signal.fourierTr` and `breeze.linalg.eig`. What
each of those called is what each now calls directly, and the section on the dependency below is
the argument and the measurement.

Both are in `modules/core`, which is the half of this repository that nothing on the proof side
believes. That is not a detail of where the files landed; it is the whole arrangement. **No library
anywhere produces `|- det (A * B) = det A * det B`**, so a number out of one is evidence and can
never be a step in a derivation. `NumericIsolationSpec` asserts it rather than trusting it: it scans
`kernel`, `logic`, `theories`, `tactics` and `checker` for any mention of either library and for
any mention of these two files, and fails naming what it found. The retired name is scanned for as
well, because a scan whose only word is a library nothing can resolve any more passes over
everything and reports nothing, which reads exactly like a scan that found nothing wrong.

The build does most of that work already. `kernel`, `logic` and `theories` declare no path to
`core`, so neither library is on their compilation classpath at all. `tactics` is the exception and
it is a structural one: it depends on `core` **and** on `theories`, because it is the module where
the algebra proposes and the kernel checks, so both reach it transitively and no build setting can
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
says `Double`, and that `Relation` still says `BigDecimal` and names none of the numeric libraries,
retired one included. The point of
putting an assertion on something so obvious is that the temptation is to unify three kinds of
arithmetic onto one library, and the reason not to is in two files rather than in one place a
reader would think to look.

## The dependency, and what it costs a consumer

`modules/core` is published as `garden.xeno:symbolum-core`, so its dependencies are what a
consumer downloads. There are two, both Java libraries with no Scala version of their own:
**`com.github.wendykierp:JTransforms:3.1`** and **`org.apache.commons:commons-math3:3.5`**.

**It was `org.scalanlp:breeze:2.1.0` for both capabilities until 2026-09-16**, and what removed it
is this table. The same command, `sbt "export core/fullClasspath"` with the jars measured in the
Coursier cache, read **20 jars and 30.96 MB** before and **5 jars and 10.12 MB** after:

| Jar | Size | What it is |
|---|---|---|
| `scala-library` 2.13 | 5.65 MB | Scala 3's own tail: `scala3-library_3` depends on it |
| `commons-math3` | 1.94 MB | the eigenvalues |
| `scala3-library_3` | 1.19 MB | |
| `JTransforms` | 1.12 MB | the transform |
| `JLargeArrays` | 0.22 MB | under JTransforms |

What went was 15 jars and 20.84 MB: `breeze_3` at 10.27, the spire, cats-kernel and algebra
type-class tail at 8.40 that Breeze's numerics are built on, the `arpack_combined_all` and
`dev.ludovic.netlib` linear algebra at 2.09, and `opencsv`, `slf4j-api` and the rest at 0.08.
`opencsv` is a CSV reader nothing here wanted, which arrived because `breeze.linalg.csvread` ships
in the same jar as the eigenvalues; at 20 KB it was 0.06% of the weight, which is the reverse of how
it had been described.

**`scala-library` 2.13 is the entry to read rather than skip**, and the note this replaces had it
wrong: it counted the 5.65 MB among what Breeze drags in because it is cross-built. Breeze is gone
and it is still here, because `scala3-library_3` depends on it. It is 56% of what remains and
nothing in this module can remove it.

Three things had to be measured before the swap, because **the risk of moving off a numeric library
is a different answer and not a build error**. The existing corpus is the judge:

- **The transform is bit-identical.** `breeze.signal.fourierTr` called
  `DoubleFFT_1D.realForwardFull`, which is what `Spectrum.of` now calls, and over signals at
  fourteen lengths from 1 to 4096, power-of-two and not, every bin agrees to the last bit. It is
  also faster, and that is below.
- **The eigenvalue is a second implementation of the same algorithm**, Hessenberg reduction and
  shifted QR on the Schur form, so agreement is expected and expecting it is not measuring it. Over
  every matrix `PerronSpec` names, including the nilpotent and zero ones that are defective and the
  cyclic permutation whose spectral radius is attained three times, the Perron root agrees with
  `dgeev` to at worst `2.3e-13` and the eigenvector's residual stays under `1.9e-14`; over 200
  random non-negative matrices up to 5 by 5 there was no disagreement and no refusal. `core/test`
  is green at 455 tests after the swap.
- **One library for both was not available.** `commons-math3` has a transform,
  `FastFourierTransformer`, and it refuses any length that is not a power of two, naming it.
  `SpectrumSpec` pins `n = 15` because numpy's rule at an odd length is what `Spectrum.ofReal`
  promises, so that library covers one of the two capabilities and not the other.

What is **not** established: that `EigenDecomposition` is as fast as `dgeev`, or that it holds up at
sizes past `PerronSpec`'s largest, which is `n = 64`. Nothing here has asked for one, and a caller
that does should measure rather than assume.

The two alternatives that were rejected while Breeze was the dependency are history now and are
recorded because the reasoning outlives the artifact: **`breeze-natives`** bundled the netlib-java
native binaries, tens of megabytes of platform-specific payload, to buy a faster BLAS no measurement
here asked for, and **`breeze-viz`** was plotting with no consumer. **Nothing in this repository
requires a native library to be installed**, which was true through `dev.ludovic.netlib`'s pure-JVM
fallback and is true now because neither remaining library has a native part at all.

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
the redundant half dropped, and since 2026-09-16 that is a choice rather than a limit.
`realForwardFull` uses the input being real and then writes the redundant half out anyway;
`DoubleFFT_1D.realForward` writes only the half this keeps, in `n` doubles rather than `2n`. It is
not taken, and the reason is the layout rather than the saving. Measured on 2026-09-16 rather than
read off the documentation: `realForward` puts bin zero's real part at index 0 and then, at index
**1**, the Nyquist bin's real part when `n` is even and the **imaginary** part of the last bin when
`n` is odd, with every other bin an interleaved pair after that. Two layouts, the odd one holding a
number the even one does not, and a misread is a wrong spectrum rather than a slow one.
`Spectrum.of` is the entry point every caller goes through and it wants the whole circle, so the
unpacked layout is read once and `ofReal` drops from it.

## The one mutable value, and why it is the only one

Scala here is a functional language and both files are written that way: no `var`, no `while`, no
`return`, no `null`, no `asInstanceOf`, no mutable collection. The outcomes are values of a sealed
type, the refusals are values rather than exceptions, and the checks are expressions.

There is exactly one exception and it is a handful of lines of `Spectrum.of`. `realForwardFull`
transforms in place, writing `n` complex numbers as `2n` interleaved doubles over a buffer whose
first half holds the samples, and no transform in the world reads an immutable sequence, so the
alternative is not a purer call but no call. The buffer is allocated and filled inside that
expression, handed to the library, and unreachable afterwards: immutable in, immutable out, nothing
shared between calls, no caller able to observe it. The samples go in through `copyToArray` and the
second half stays at the zero `new Array` gives it, because `StyleSpec` asserts that no source under
`modules/*/src/main` holds a `var`, a `while` or a cast: `Array.copy` will not take an `IArray`
without a cast, `IArray.toArray` is deprecated as incorrect and this build reads a warning as an
error, and the wrapper the deprecation points at copies twice.

What that costs was measured on 2026-09-17 in thread CPU time, the machine being busy, least of
seven interleaved rounds at `n = 2^22`, the fill alone: **13.2 ms** written as a loop, **14.8** as
this copy, 23.8 through the wrapper and 28.4 as an `Array.tabulate` with a branch per entry. The
loop would buy 12% of a fill, on the only comparison this machine supports, which is four fills in
one interleaved run. It would cost an entry in that guard's excuse list, which `Solver.scala` holds
two of and paid for with a much larger number. The
version that reads as the functional one, the tabulate, is the slowest of the four, which is the
part worth carrying.

Everything a caller sees is `IArray[Double]`, which is the primitive array with no mutation in its
surface, and the measurement that chose it over `Vector[Double]` is below. `Perron` uses
`Vector[Vector[Double]]` instead, because its matrix is `n^2` numbers under `O(n^3)` work and the
representation is a vanishing share of the cost; `Perron.settle` and `Perron.check` take the matrix
as the linear map it is, `Vector[Double] => Vector[Double]`, so that the numeric library does not
appear in their signatures at all.

The one place an exception is caught is the eigen decomposition, and it catches
`MaxCountExceededException` by name rather than using `Try`. That is what `EigenDecomposition`
raises with `CONVERGENCE_FAILED` when the QR iteration runs out of steps; the constructor's other
declared failure, `MathArithmeticException`, is a defect here rather than an outcome and is left to
propagate. `Try` collects everything non-fatal, and there is no honest outcome to map a defect onto:
the refusals have already thrown out every matrix the decomposition documents an argument error for,
so anything else is a mistake in this repository and turning it into `NotConverged` would be merging
a defect with a refusal.

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
matrices with no negative entry. Run on a matrix with one, the decomposition still returns a
largest-modulus eigenvalue, and that number is not a growth rate and its eigenvector can be
anything. Answering would be worse than refusing.

## What is not built, with the count instead

- **The inverse transform.** `DoubleFFT_1D.complexInverse` is one line away and has zero named
  consumers.
- **The two-dimensional transform**, and windowing: zero named consumers.
- **The full spectrum of eigenvalues**, rather than the dominant one: zero named consumers. The
  decomposition computes them all anyway and `Perron` throws the rest away, so the cost of adding it
  later is the surface and not the arithmetic.
- **A test for `Perron.NotConverged`.** It is the one branch in either file that nothing covers: the
  QR iteration does not fail to converge on any matrix small enough to put in a suite, and the seam
  that
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

**More than half of what was left was not the transform, and that is what the change on 2026-09-16
collected.** `breeze.signal.fourierTr` returned a `DenseVector[Complex]`, four million boxed objects
at `n = 2^22`, and reading them back into two primitive arrays cost 1626 ms against the transform's
1179. That was the price of the Breeze entry point rather than of the FFT. `realForwardFull` writes
into an interleaved primitive array and boxes nothing, so the unpacking and the copy in are gone and
the transform itself does about half the work.

The paragraph here predicted **a factor of three**. Measured end to end on 2026-09-16, best of three
on a machine under load, the same signal at `n = 2^22`: **897 ms against 2017 ms**, which is 2.25.
Both numbers are from the same run on the same machine minutes apart, so the ratio is a comparison
and the absolute figures are not comparable with the 2946 ms above, which was a quieter day and a
different probe. Nothing had asked for a `2^22` transform in a loop then and nothing has now: what
took it was the 20.84 MB, and the speed came with it.

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
