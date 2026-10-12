# Fourier transforms

`FFT.fft` transforms an array of interleaved complex binary64 components.  `FFT.inverse` uses the positive phase and divides each component by the number of complex samples.  `FFT.powerSpectrum` takes real samples and returns their squared transform magnitudes, from frequency zero through `n / 2`.  Empty input returns an empty array.  The complex functions ignore an odd final input component.

## Algorithm

For a power-of-two sample count `n = 2^p`, the functions copy the input into bit-reversed order, precompute `n / 2` trigonometric factors with `Fourier.twiddleWith`, and perform `p` stages of `n / 2` butterflies.  Each stage reads both complex operands before writing their sum and difference.  Factors use the existing `Trig.sinWith` and `Trig.cosWith`, with the tables passed by the public wrappers.  The output uses natural frequency order.  Other lengths use the direct transform in `Fourier.transformWith`.

The radix-2 path performs `O(n log₂ n)` work.  The direct path performs `n²` complex products.  The benchmark driver uses the deterministic `Fourier.signal` input with seed 17, two warmups, nine measured batches, and the median time per call.  It includes output release and checks that each call's allocation and release counts balance.

The exact stage identities follow [Cooley and Tukey's transform decomposition](https://web.stanford.edu/class/cme324/classics/cooley-tukey.pdf).  The negative forward phase and positive inverse phase agree with the [FFTW transform conventions](https://www.fftw.org/fftw3_doc/Complex-One_002dDimensional-DFTs.html).

## Numerical statements

Let `u = 2^-53`, `η = 2^-1075`, and `A = Σ(|Re x_j| + |Im x_j|)` over the used input samples.  For real power spectra, `A = Σ|x_j|`.  Set

```text
q = (1 + u)²(1 + 32u)
r = (1 + u)(2q - 1)
K₀ = 0
Kₛ₊₁ = 2rKₛ + 3(1 + u)²η
B = r^p A + Kp
E = (r^p - 1)A + Kp.
```

For `n = 2^p`, the domain requires finite used inputs, `p ≤ 32`, and `2qB + 2(1 + u)η < 2^1022`.  Each forward coordinate's absolute error is at most `E`.  Each inverse coordinate's error is at most `(E + uB)/n + η`.  Real power spectra also require `(1 + u)B² + η < 2^1022`, and each output's error from the exact squared transform magnitude is at most `4AE + 2E² + 2u(2 + u)B² + 2(1 + u)η`.  All used output coordinates are finite.  Power outputs are nonnegative.

For other lengths, the domain and bounds use the existing direct transform.  Set `G = (1 + u)^(n + 2)(1 + 32u)`, `H = 2n(1 + u)^(n + 1)η`, `B = GA + H`, and `E = (G - 1)A + H`.  Forward and inverse require finite used inputs, `n ≤ 2^32`, and `B < 2^1022`.  Real power spectra require finite samples, `n ≤ 2^32`, and `(1 + u)B² + η < 2^1022`.  The forward, inverse, and power error expressions then have the same forms as above.

The definitions in [the specification](FFTSpec.lean) include the empty case and select the bound for the implementation's chosen path.  `AccurateOutput` and `AccurateInverse` require `2n` output components.  `AccuratePower` requires zero outputs for empty input and `n / 2 + 1` otherwise.

## Proofs and tests

| Source | Result |
|---|---|
| [Bit-reversal proof](FFTBits.lean) | Power-of-two dispatch, stage count, reversal bounds, involution, and child indices. |
| [Index proof](FFTIndex.lean) | Butterfly and table indices, disjoint writes, enumeration, and UInt64 correspondence. |
| [Loop proof](FFTLoop.lean) | Copied entries, stage writes, stage induction, normalization, and spectrum projection. |
| [Exact transform identities](FFTMath.lean) | Stage values, input mass, even/odd decomposition, and final DFT coordinates. |
| [Rounded arithmetic proof](FFTArithmetic.lean) | Complex products, butterflies, and the error and magnitude recurrences. |
| [Radix-2 numerical proof](FFTNumerical.lean) | Finite computed coordinates, error at most `E`, and magnitude at most `B`. |
| [Division proof](FFTDivision.lean) | Final inverse normalization, including underflow. |
| [Public forward theorem](FFTTheorem.lean) | Radix-2 and direct dispatch under `FFTSpec.Admissible`. |
| [Public inverse theorem](FFTInverse.lean) | Positive phase and normalization under the same domain. |
| [Public power theorem](FFTPower.lean) | Finite, nonnegative squared magnitudes under `PowerAdmissible`. |
| [Compiler declaration](FFTProgram.lean) | Compilation of the same definitions. |
| [Byte proof](FFTBytes.lean) | Numerical bounds on the owned array returned by the decoded module. |
| [File proof](FFTFile.lean) | Encoding and decoding of `build/verified/fft.wasm`. |

The runtime statements use `Runs true`: a successful call returns an owned result with the numerical bounds and preserves borrowed inputs, tables, and prior heap regions.  They permit a trap at `unreachable`.  Input representation, allocator state, table regions, and the memory-cap premise are explicit.

`FFTProgram` enables the opt-in `Verified.Reflect.materializeModule` compiler option.  Native evaluation proposes a literal module, and Lean's kernel checks `compiled.module_literal_eq` against the original `compileWith` definition.  The byte proof then uses the literal to decide the original locals and encoder-success premises.  The compiler's default leaves the option off.

The [focused test driver](../../tests/fourier/run.sh) checks the byte proofs and emitted file, generates fixed cases in native Lean, compares their output bits and live allocation counts with Wasmtime, and runs the [numerical test](FFTAccuracy.lean).  Separate modes select `proof`, `prepare`, `cases`, `accuracy`, `runtime`, or `benchmark`.  `proof` checks the compiler, numerical byte theorem, emission, and file theorem.  `prepare` also generates the cases and runs the numerical test.  The numerical test uses the integer reference and a test tolerance separate from the proved bounds.  It covers 99 signals and reported a maximum component distance of `0.025000` of that tolerance in `build/fourier/fft-accuracy-002.log`.

The public numerical checks completed with status 0 in `build/fourier/fft-public-002.log`.  The full compiler declaration passed in `fft-program-003.log`, and the final numerical byte and emitted-file checks passed in `fft-proof-002.log`.  Every printed final declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.  The checked file contains 10,048 bytes.  The [compiler-option test](../../tests/fourier/Materialization.lean) checks its default and scoped values and recompiles the existing Elements, Tables, and Recursion definitions.  It collects the axioms of twelve test declarations and requires each set to equal the three permitted names.  These checks passed in `materialization-gate-004.log`.

`fft-runtime-001.log` records 72 Wasmtime cases with status 0.  The output bits match native Lean, and each call leaves exactly the input and output allocations live.  Cases include empty input, signed zeros, subnormals, infinities, NaN, finite extremes, ignored odd complex tails, direct fallback, and large arrays that exercise memory growth.

## Performance

`fft-benchmark-001.log` records the following medians on the build host's AMD Ryzen 3 PRO 7330U using Wasmtime 44.  Both functions receive the same interleaved complex input.  Times include output release and exclude module instantiation and input preparation.  DFT measurements stop at 4,096 complex samples.  Each FFT and DFT row reports two allocations per call.  Measured releases balance allocations, and releasing the input leaves no live allocations.

| Complex samples | FFT, ms | DFT, ms | DFT / FFT |
|---:|---:|---:|---:|
| 16 | 0.001190 | 0.002455 | 2.06 |
| 64 | 0.004950 | 0.025009 | 5.05 |
| 256 | 0.022757 | 0.350898 | 15.42 |
| 1,024 | 0.105243 | 5.457886 | 51.86 |
| 4,096 | 0.481779 | 91.811313 | 190.57 |
| 16,384 | 2.185429 | — | — |
| 65,536 | 9.829581 | — | — |
| 262,144 | 45.749520 | — | — |

Proof, test, and benchmark logs stay under `build/fourier/` on the build host.  Runtime tests use an isolated directory on the build host.
