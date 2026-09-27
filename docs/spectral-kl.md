# Spectral KL moment estimator

This work concerns the regularized moment functional from
[Francis Bach’s spectral log-density article](https://francisbach.com/spectral_log_density_estimation/).
The current proof coverage is:

- **Matrix polynomial computation:** a Lean theorem proves success and
  absolute error at most 1e-6 for all nonempty rational sample groups and
  every positive ridge, in arbitrary finite feature dimension. It computes
  full cross-feature moments, selects a recurrence and iteration count, and integrates its polynomial
  approximation using exact rational arithmetic. Run it directly in Lean
  with `tools/spectral-kl/matrix-series.mjs`.
- **Scalar computation:** a Lean theorem proves that every admitted input
  succeeds and the computed score has absolute error at most 1e-6. This covers
  the actual sample reductions and subsequent numerical computation. Run it
  directly in Lean with `tools/spectral-kl/scalar.mjs`.
- **Exact integer CPU/GPU moments:** a separate fixed-point input variant has
  exact u32 column and Gram reductions. Its CPU computation is proved. For
  the GPU variant, the emitted WGSL parses to a program whose reduction and
  score correctness are proved in a formalized subset of WGSL. Execution
  trusts the WebGPU compiler and device to implement those semantics.
- **Floating-point CPU and WebGPU computation:** the Cholesky/Jacobi solver and shader
  remain unproved. The separate matrix CLI checks their proposed score using
  a proved acceptance function. That checker does not complete the requested
  proof of those algorithms.

The caller supplies feature observations. The numerical target is the exact
regularized functional of those observations; sampling error and the relation
to population KL divergence are outside these computation proofs.

## Run

### Proved matrix polynomial computation

```sh
tools/spectral-kl/verify matrix-general-proof
tools/spectral-kl/verify matrix-general-audit
tools/spectral-kl/verify matrix-general-example
tools/spectral-kl/verify matrix-general-large
tools/spectral-kl/verify matrix-general-damped
```

The examples use 4 and 32 correlated features beyond the earlier algorithm's
moment/ridge domain. The last example selects the damped recurrence. Pass `--local` before the
verification target when local Lean execution has been authorized. Custom
input uses rows of feature observations:

```json
{"p": [[0.1, 0.3], [0.2, -0.4], [-0.1, 0.5]],
 "q": [[0.0, 0.4], [0.3, -0.3]], "eta": 1}
```

```sh
node tools/spectral-kl/matrix-series.mjs --input observations.json
```

The CLI accepts 1–32 features and at most 524288 values per group. It decodes
the supplied binary64 numbers into exact rationals. Let P and Q be the exact
uncentered sample moment matrices, and d the exact difference of sample means.
Both groups must be nonempty and eta must be positive. There is no condition
relating eta to the moments and no upper bound on the mean difference. There
is no assumption that the two matrices commute, are diagonal, or have distinct
eigenvalues. The theorem has no fixed dimension or sample-count limit.

The CLI has a five-minute execution timeout. Small ridges can require many
steps and large rational coefficients; the theorem proves termination of the
mathematical computation, with no practical runtime bound.

The default `--method auto` selects a recurrence and iteration count from
the input moments. `--method damped` always uses the general damped recurrence.
Both return an exact decimal score with twelve fractional digits; the 1e-6
proof includes this final rounding.

For H(r) = rP+(1-r)Q+eta I, the damped algorithm computes vector polynomials

\[
 U=2(\eta^2+\|P\|_F^2+\|Q\|_F^2),\qquad
 x_0(r)=0,\qquad x_{k+1}(r)=x_k(r)+\frac{\eta}{U}(d-H(r)x_k(r)),
\]

then integrates the polynomial

\[
 (1-r)\bigl(2d^Tx_k(r)-x_k(r)^TH(r)x_k(r)\bigr).
\]

All coefficients and their integrals are computed as exact rationals. The
bound on the unrounded score is

\[
 \left|\widehat F_k-F_\eta\right|
 \leq \rho^k\frac{d^Td}{2\eta},
 \qquad \rho_{\rm damped}=1-\frac{\eta^2}{U}\in[0,1).
\]

The automatic method also computes rho_fast = (‖P‖F²+‖Q‖F²)/eta². If that
factor is smaller, it uses x_(k+1) = (d-(rP+(1-r)Q)x_k)/eta. Otherwise it
uses the damped recurrence. It selects enough steps for the smaller proved
bound to leave 1e-12 for decimal rounding. The input-derived finite search
budget is proved sufficient for every positive ridge. The score is computed
from the observations without a proposed score or solution vectors.

This evaluates the regularized moment integral from the article using a
polynomial approximation. It does not implement the article's generalized
eigenvalue decomposition or claim its computational complexity.

The earlier `--method fixed` and `--method adaptive` remain available. Their
domain additionally requires ‖P‖F²+‖Q‖F² ≤ eta²/4 and dᵀd ≤ 32 eta; twelve
steps suffice in that domain. `auto` and `damped` remove these restrictions.

GPU assessment: this version uses variable-size integers and exact rational
polynomial coefficients throughout. WebGPU does not directly provide those
arithmetic types. A GPU version would require another representation and its
own arithmetic proof. The existing floating-point Gram shader remains a
separate implementation with an outstanding computation proof.

### Preconditioning for small ridges

```sh
tools/spectral-kl/verify preconditioned-proof
tools/spectral-kl/verify preconditioned-audit
tools/spectral-kl/verify preconditioned-example
tools/spectral-kl/verify preconditioned-gpu-example
tools/spectral-kl/verify preconditioned-large
tools/spectral-kl/verify preconditioned-gpu-large
```

Both matrix CLIs accept `--method preconditioned`. This method computes the
exact rational inverse M of C = (P+Q)/2 + eta I using Schur-complement
elimination. It factors C once and reuses the stored factors for every inverse
column, then considers the polynomial recurrence

\[
 x_0(r)=0,\qquad x_{k+1}(r)=x_k(r)+M(d-H(r)x_k(r)).
\]

Its squared-residual contraction bound is

\[
 \rho_{\rm pre}=\max\{\|I-(P+\eta I)M\|_F^2,
                 \|I-(Q+\eta I)M\|_F^2\}.
\]

The estimator selects this recurrence if that bound is smaller than the
existing automatic method's bound. Otherwise it uses that method. It still
proves success and absolute error at most 1e-6 for every pair of nonempty
rational sample groups and every positive ridge. A small ridge alone does
not force the preconditioned bound close to one. The actual bound depends on
how the two regularized moments differ relative to their midpoint.

The implementation streams the centered Neumann series. With
T=-M(P-Q)/2, it forms v₀=Md and v_(j+1)=Tv_j, and adds the exact integral of
(1-r)(2r-1)^j dᵀv_j. If the selected error budget requires depth k, it uses
2k terms. This equals the integral of (1-r)dᵀx_(2k)(r); a proved linear
residual bound gives the same accuracy budget. The CLI's iteration count
reports these coefficient-vector terms. It avoids constructing and
multiplying long vector polynomials.

[`ExactSolve`](../proofs/talos/lean/Project/SpectralKL/ExactSolve.lean) proves
that its computed solution satisfies Ax=b for every matrix with a positive
quadratic form. [`ExactInverse`](../proofs/talos/lean/Project/SpectralKL/ExactInverse.lean)
proves positivity of the sample midpoint and correctness of its computed
inverse. [`MatrixPreconditioned`](../proofs/talos/lean/Project/SpectralKL/MatrixPreconditioned.lean)
proves the stored polynomial recurrence's residual and integral error bounds.
[`MatrixNeumann`](../proofs/talos/lean/Project/SpectralKL/MatrixNeumann.lean)
connects the streamed coefficient computation to that recurrence, and
[`MatrixNeumannScore`](../proofs/talos/lean/Project/SpectralKL/MatrixNeumannScore.lean)
proves the streamed integral's error bound.
[`MatrixAccelerated.compute_correct`](../proofs/talos/lean/Project/SpectralKL/MatrixAccelerated.lean)
covers moment construction, method selection, iteration-count selection,
computed integral, and decimal rounding. The corresponding integer CPU and
shader-semantics compositions are in
[`WordAccelerated`](../proofs/talos/lean/Project/SpectralKL/WordAccelerated.lean).
These are computation theorems; no proposed score or externally supplied
approximate solution is an input.

The two-feature example uses 512 observations in each group: q alternates
between (-4,-4) and (4,4), and p=q+(-1/4096,1/4096). With eta=2^-20, both
CPU and software WebGPU runs returned 0.060047173764 using four streamed
coefficient terms. The GPU performs the same exact
moment reductions used by the larger workload below. The rational score
work remains on the CPU. This
improves some small-ridge inputs; it supplies no practical runtime bound for
all inputs.

The 32-feature CPU and software WebGPU examples at the same ridge, with
16381/16384 observations, completed with score 1.192735996967 using 82
coefficient terms. The GPU performs all roughly 33.6 million feature
products and returns only the integer moment sums to the score core. Earlier
versions that expanded full vector polynomials reached the five-minute
limit on this same input. The streamed implementation completed within that
unchanged limit.

The general rational example (`verify preconditioned-rational`) uses four
features, 64/67 observations scaled by binary64 0.3, and eta=2^-20. It
completed with score 0.465416924945 and 22 terms. These observations need
the general rational input path, rather than the selected signed-16-bit
format used by the GPU examples.

### Exact integer moments: CPU and GPU variants

```sh
tools/spectral-kl/verify word-shader-proof
tools/spectral-kl/verify word-shader-audit
tools/spectral-kl/verify word-moments-large
tools/spectral-kl/verify word-gpu-large
```

The CPU and GPU commands perform the same sample-to-score calculation with
32 features and 16381/16384 observations. The GPU computes every column sum
and every entry of XᵀX, about 33.6 million feature products across both groups.
Each invocation owns one output entry and reduces its independent sample
contributions. The score computation then runs directly in Lean.

Custom input uses the same JSON observation format:

```sh
node tools/spectral-kl/word-moments.mjs --input observations.json --denominator 128 --backend cpu
node tools/spectral-kl/word-moments.mjs --input observations.json --denominator 128 --backend gpu
```

Every observation must be exactly a signed 16-bit integer divided by the
specified positive power-of-two denominator. The CLI rejects values that
would require rounding. It supports 1–32 features and up to 524288 values
per group. Eta may be any positive finite binary64 value; the same small-ridge
runtime limitation as the rational estimator applies.

For the reduction, each signed integer is biased by 32768 and stored as a
u32. A product fits in a u32; sums use two u32 limbs with an explicit carry.
The host removes the bias and divides by the sample count and denominator
using exact rationals. Both variants feed the same proved score core.

The proof covers these layers:

- [`WordMoments`](../proofs/talos/lean/Project/SpectralKL/WordMoments.lean):
  carry arithmetic, products, and exact reductions for up to 2^20 rows.
- [`WordEstimator`](../proofs/talos/lean/Project/SpectralKL/WordEstimator.lean):
  exact bias correction, means and full moment matrices, and the CPU score.
- [`WordShader`](../proofs/talos/lean/Project/SpectralKL/WordShader.lean):
  one program definition supplies the execution model and emitted WGSL.
- [`WordShaderSource`](../proofs/talos/lean/Project/SpectralKL/WordShaderSource.lean):
  the complete emitted module parses back to that program. The parser checks
  the declarations, entry guard, loop, arithmetic expressions, and output write.
- [`WordShaderBounds`](../proofs/talos/lean/Project/SpectralKL/WordShaderBounds.lean):
  address bounds, dispatch coverage, distinct output locations, and equality
  of shader reductions to CPU reductions.
- [`WordShader.compute_correct`](../proofs/talos/lean/Project/SpectralKL/WordShaderEstimator.lean):
  the shader's source semantics followed by the score core produce absolute
  error at most 1e-6 against the supplied samples' regularized integral.

The formal GPU model covers the WGSL subset used by this kernel, including
u32 arithmetic and its canonical increasing loop. It is not a formalization
of all WGSL. The arithmetic follows the standard's
[modulo-2^32 integer rules](https://www.w3.org/TR/WGSL/#integer-types).
The WebGPU compiler, device execution, host buffer transport, JSON parsing,
and Lean evaluator remain trusted. The theorem assumes the uploaded buffer
contains the supplied biased samples in row order. The GPU path does not
recompute moments on the CPU or validate a proposed score.

Completed runs used Mesa llvmpipe, a software WebGPU adapter. CPU and GPU
both returned 0.003893093480 on the large input; the universal theorems
establish accuracy. For explicitly authorized local/software execution:

```sh
tools/spectral-kl/verify --local --software word-gpu-large
```

The earlier binary32 Gram shader is a separate implementation and remains
unproved.

### Proved scalar computation

```sh
tools/spectral-kl/verify scalar-proof
tools/spectral-kl/verify scalar-audit
tools/spectral-kl/verify scalar-example
```

Pass `--local` before the target when local Lean execution has been authorized.
The example computes the score directly in Lean for groups of 65536 and 65539
observations. For custom input:

```json
{"p": [0.1, 0.3, -0.2], "q": [0.2, 0.4], "eta": 3.5}
```

```sh
node tools/spectral-kl/scalar.mjs --input scalar-observations.json
```

Each group has 1–1048576 binary64 observations in [-0.5,0.5]. The ridge is in
[1,256], defaulting to 1. `--eta` overrides the input file's ridge. Every input
in this domain is covered by the total correctness theorem below. Values are
the binary64 numbers parsed from JSON, including their rounding from decimal.

The same Lean source can be compiled to WebAssembly:

```sh
tools/spectral-kl/verify scalar
node tools/spectral-kl/scalar.mjs --example --engine wasm
```

The WebAssembly route additionally trusts the compiler's translation. The
`scalar` target exercises compilation and the calling convention; numerical
comparisons in that target do not establish the universal error bound.

The large sample reductions are suitable GPU work. A proved GPU counterpart
of this scalar iteration remains outstanding.

### Matrix proposals and their acceptance checker

Use the repository’s configured Lean and Node environment. From the root:

```sh
node tools/spectral-kl/build.js
node tools/spectral-kl.mjs --example --backend cpu
```

The example uses 32 correlated features and approximately 16,000 observations
in each group. To supply your own observations:

```json
{"p": [[0.1, 0.3], [0.2, -0.4], [-0.1, 0.5]],
 "q": [[0.0, 0.4], [0.3, -0.3]], "eta": 1}
```

```sh
node tools/spectral-kl.mjs --input observations.json --backend cpu
```

Each group must be nonempty and rectangular, with the same 1–32 features and
at most 524288 values per group. Feature values must be finite and in [-16,16].
The CLI rounds features to binary32 for both backends. `eta` defaults to 1 and
must be in [2⁻²⁰,256]. The current kernel supports generalized eigenvalues in
[1/2,3/2]; the solver rejects spectra outside this interval. Increasing `eta`
can bring a spectrum into range, but also changes the mathematical quantity.
Factorization failure, lack of Jacobi convergence, and failure to certify the
requested accuracy are explicit errors. `--tolerance` sets the absolute error
bound (default 1e-6). `--intervals` sets the number of integration
intervals (default 8); finer partitions can tighten the enclosure.

### Original floating-point WebGPU variant

Install the optional [Dawn Node WebGPU binding](https://github.com/dawn-gpu/node-webgpu)
locally, then select the GPU backend:

```sh
npm install --prefix build/spectral-kl-gpu webgpu@0.6.1
node tools/spectral-kl.mjs --example --backend gpu
```

The GPU computes both feature means and full uncentered second-moment matrices.
For a feature matrix X, this is column reduction and XᵀX/n: each output entry
reduces independent contributions from observations. At 32 features and roughly
16,000 observations, each group supplies about 16 million feature products.
This is substantial, regular data-parallel work needed by the estimator.
The matrix solver and scalar kernel execute the same Lean/WASM code as the
CPU variant.

The shader has two passes: 256-lane tree reductions produce block sums, then
another reduction combines the blocks and divides by the observation count.
It uses binary32 products and sums, with no floating-point atomics. CPU moments
use sequential binary64 accumulation. These are different rounding orders;
bitwise agreement is not expected. GPU moment error can matter when `eta` is
small and the matrices are poorly conditioned.

The runtime reports the selected adapter. Software adapters require
`--allow-software`; this enables shader validation on a machine without an
exposed GPU. A rejected GPU request produces an error. `WEBGPU_BACKEND` can
select a Dawn backend, such as `vulkan`. The reusable
[runtime module](../tools/spectral-kl/runtime.mjs) also accepts a browser’s
`navigator.gpu` with the same shader.

## Mathematical computation

Let μp, μq denote feature means and Σp, Σq denote **uncentered** second moments.
Set d = μp − μq, A = Σp + ηI and B = Σq + ηI. The target is

\[
 F_\eta = \int_0^1 (1-r)\,d^T\bigl(rA+(1-r)B\bigr)^{-1}d\,dr.
\]

The original floating-point solver factors B = LLᵀ, constructs C = L⁻¹AL⁻ᵀ and z = L⁻¹d,
then uses symmetric Jacobi rotations on C and the coordinates z. If λi are
the resulting eigenvalues and zi the rotated coordinates, it evaluates

\[
 F_\eta = \sum_i z_i^2 h(\lambda_i),\qquad
 h(t)=\frac{t\log t-t+1}{(t-1)^2},\quad h(1)=\tfrac12.
\]

Directly evaluating this quotient near one loses accuracy through cancellation.
For |δ| ≤ 1/2, the implementation instead evaluates the first 41 terms of

\[
 h(1+\delta)=\sum_{k=0}^\infty
       \frac{(-\delta)^k}{(k+1)(k+2)}.
\]

Both matrices receive the ridge term. Cholesky solves avoid constructing B⁻¹.
Jacobi rotations update z along with C, so repeated eigenvalues do not require
choosing a particular eigenvector basis. The stopping threshold for off-diagonal
entries is 2⁻⁴², with a maximum of 32 sweeps.

## What is proved

### Preconditioned computation and integer GPU variant

[`MatrixAccelerated.compute_correct`](../proofs/talos/lean/Project/SpectralKL/MatrixAccelerated.lean)
proves total success and error at most 1e-6 for nonempty rational sample groups
and every positive ridge, in arbitrary finite dimension. Its returned-value
theorem derives the bound from the executable's successful result.
The [preconditioning section](#preconditioning-for-small-ridges) identifies
the factorization, streamed integral, and iteration-budget proofs it uses.

[`WordAccelerated.compute_correct`](../proofs/talos/lean/Project/SpectralKL/WordAccelerated.lean)
adds the actual integer CPU reductions and bias correction.
`WordAccelerated.computeSource_correct` starts with the parsed integer shader
semantics and composes those reductions with the same score core. Its input
layout assumption and trusted execution components are stated in the
[integer CPU/GPU section](#exact-integer-moments-cpu-and-gpu-variants).
Neither theorem takes a proposed score or externally computed solution as
an input. All these public theorems use only `propext`, `Classical.choice`,
and `Quot.sound`.

### Actual matrix polynomial computation

[`MatrixGeneral.computeAuto_correct`](../proofs/talos/lean/Project/SpectralKL/MatrixAuto.lean)
proves that every input satisfying `MatrixGeneral.Valid` returns a score
with error at most 1e-6 against the defining inverse-matrix integral.
`Valid` requires only nonempty groups and positive eta.
`computeAuto_returned_error` derives the same bound for every returned value
from the executable guards. The preceding damped version has its own
[`MatrixGeneral.compute_correct`](../proofs/talos/lean/Project/SpectralKL/MatrixGeneral.lean)
theorem. The earlier fixed and adaptive algorithms retain their separate
theorems and narrower domains.

The proof covers the executed computation:

- `storedMean_eq` and `storedMoment_eq` connect the actual stored-array
  reductions to the exact sample means and full uncentered moment matrices.
- [`DensePolynomial`](../proofs/talos/lean/Project/SpectralKL/DensePolynomial.lean)
  proves the implemented coefficient-list arithmetic and exact integration.
- [`MatrixPolynomial.solution_eval`](../proofs/talos/lean/Project/SpectralKL/MatrixPolynomial.lean)
  connects the executed polynomial iteration to the real matrix recurrence.
- [`MatrixIteration.residual_bound_with`](../proofs/talos/lean/Project/SpectralKL/MatrixIteration.lean)
  proves the residual reduction in arbitrary finite dimension.
- [`MatrixPolynomial.sampleScore_error_with`](../proofs/talos/lean/Project/SpectralKL/MatrixScore.lean)
  integrates the error bound for the original recurrence.
- [`MatrixDamped`](../proofs/talos/lean/Project/SpectralKL/MatrixDamped.lean)
  proves contraction of the damped residual for every positive ridge.
- [`MatrixDampedPolynomial`](../proofs/talos/lean/Project/SpectralKL/MatrixDampedPolynomial.lean)
  connects the executed damped polynomial iteration to that recurrence and
  integrates its error bound.
- [`GeometricBudget.select_budget`](../proofs/talos/lean/Project/SpectralKL/GeometricBudget.lean)
  proves that the executable depth search terminates within its derived
  budget and selects enough steps. `roundScore_error` covers decimal rounding.
- `selectedSampleScore_error` proves the automatically chosen algorithm has
  the selected error bound. `computeAuto_eq` connects the executed stored
  reductions and branch to this theorem.

These proofs use only `propext`, `Classical.choice`, and `Quot.sound`. Direct
execution trusts Lean's evaluator, its integer runtime, and the host I/O.
The JSON parser and transport have no end-to-end formal proof. The word
decoder's `wordValue_real` theorem connects its rational value to the IEEE
real-value definition. The new computation does not use the matrix proposal
acceptance checker. It reuses the analytic target and residual inequality.

### Actual scalar computation

[`Scalar.fromBoundedSamples_correct`](../proofs/talos/lean/Project/SpectralKL/ScalarEstimator.lean)
quantifies over arbitrary arrays and ridge words satisfying `ValidSamples` and
`ValidRidge`. It proves all three conclusions:

1. `fromBoundedSamples p q eta` returns status zero.
2. Its computed binary64 score is finite.
3. The score differs by at most 1e-6 from
   `regularizedIntegral p q (CodeLib.IEEE64.value eta)`.

`regularizedIntegral` is the defining integral with the exact sample means and
uncentered second moments. Its denominator is
`r*(secondP+eta)+(1-r)*(secondQ+eta)`. No successful-result assumption,
external score, approximate moments, or error estimate is an input to the
public theorem.

The proof chain is:

- [`ScalarStats`](../proofs/talos/lean/Project/SpectralKL/ScalarStats.lean):
  the actual `Array.foldl` reductions, rounded products, count accumulation,
  and division produce moments within 1e-8 of the exact sample moments.
- [`ScalarMoments.score_error`](../proofs/talos/lean/Project/SpectralKL/ScalarMoments.lean):
  regularization, division, subtraction, squaring, kernel evaluation, and final
  multiplication produce the stated score bound. The proof also establishes
  that the computed kernel argument stays inside its supported domain.
- [`KernelContinuity`](../proofs/talos/lean/Project/SpectralKL/KernelContinuity.lean):
  the integral kernel's sensitivity to its rounded argument.
- `regularizedIntegral_eq`: equality between the scalar spectral expression
  and the defining integral.

`fromUnitSamples_correct` is the ridge-one specialization. These theorems name
the executable source functions and use only `propext`, `Classical.choice`, and
`Quot.sound`. Direct Lean execution trusts Lean's evaluator, integer runtime,
and the input/output layer. The theorem does not prove the JSON parser or
WebAssembly translation.

### Matrix score acceptance

The separate acceptance theorem is
[`Certificate.accepts_sound`](../proofs/talos/lean/Project/SpectralKL/CertificateSound.lean).
For arbitrary finite feature dimension, rational observations, candidate score,
candidate solution vectors and interval partition, acceptance implies

\[
  |\widehat F-F_\eta(\text{observations})|\leq\text{tolerance}.
\]

The target is defined directly as the inverse-matrix integral above in
[`CertificateData.lean`](../proofs/talos/lean/Project/SpectralKL/CertificateData.lean).
The theorem covers the **complete score**, including errors introduced by moment
computation, matrix decomposition, and kernel evaluation. It does this by checking
the final value against the original observations. It does not assume that any
of those numerical stages computed the right answer.

[`Certificate.Fast.certify`](../proofs/talos/lean/Project/SpectralKL/CertificateFast.lean)
returns an optional `VerifiedScore` and its enclosure. Its successful result
contains the proved error bound in its Lean type. The command-line checker calls
that function. Stored vectors avoid repeated evaluation; `enclose_eq` proves
equality with the general checker's enclosure. Input bit patterns are decoded
into exact rationals;
`CertificateRun.wordValue_real` proves that this decoding agrees with the real
value used by the IEEE model. The target concerns the binary32 observations
that the CLI passes to both backends. Error from converting an original decimal
or binary64 dataset to binary32 is outside that target.

`Certificate.Fast.accepted_error` states the final error guarantee directly
for successful calls to the function used by the native checker, and for the
same proposed score passed by the CLI.

The proof uses a general residual inequality. For M ≽ ηI, any vector x,
and residual e = d − Mx,

\[
  2d^Tx-x^TMx
  \leq d^TM^{-1}d
  \leq 2d^Tx-x^TMx+\frac{e^Te}{\eta}.
\]

Lean proves this inequality for arbitrary finite dimension. It also proves that
sample second moments plus the ridge satisfy its assumptions, bounds residuals
throughout each interval, integrates those bounds, and checks that the partition
covers [0,1]. The checker uses exact rational arithmetic. It computes matrix-vector
products directly from projected observations; it does not rerun the Gram matrix
construction or eigensolver. The proposed solution vectors are untrusted.

Separately,
[`Executable.kernel40_accepted`](../proofs/talos/lean/Project/SpectralKL/Executable.lean)
proves the 1e-14 scalar error bound for successful results of the **executable**
`LeanExe.Examples.SpectralKL.kernel40` function. `kernel40_model` connects its
actual operation sequence to the general Horner theorem. The source now calls
pure binary64 operations, each proved equal to the numerical model for every
input word in
[`Operations.lean`](../proofs/talos/lean/Project/SpectralKL/Operations.lean).

These theorems use only `propext`, `Classical.choice`, and `Quot.sound`. There are
no additional numerical assumptions, solver-accuracy axioms, or shader-accuracy
axioms in the final-score theorem.

### Matrix checker execution boundary

The checker runs as a native Lean program. The theorem establishes correctness
of that Lean program's acceptance function. Running it trusts Lean's runtime,
exact integer/rational arithmetic, and the host's input/output transport. The
Node JSON encoder/decoder and operating system have not been formally verified.
The WASM compiler, eigensolver and WebGPU implementation produce proposals;
the final-score theorem does not need their correctness. There is still no
universal execution theorem for the complete emitted WASM module or the
original floating-point WGSL shader. The separate integer shader's computation
proof is described above.

This certifies a numerical functional of the supplied observations. It does not
bound sampling error or establish a population KL lower bound.

## Audit and run the checker

The repository verification command selects the locally installed toolchain
when present. It provides one stable command for repeatable approval rules:

```sh
tools/spectral-kl/verify build
tools/spectral-kl/verify audit
tools/spectral-kl/verify example-cpu
tools/spectral-kl/verify example-gpu
```

`audit` builds the proofs, then prints the mathematical definitions, theorem
statements and their axioms. For explicitly authorized execution without a
systemd resource scope, pass `--local` before the target. `--software` permits
a software GPU and selects the locally installed Mesa runtime when present.

A successful CLI result names a saved `checkInput` file. The adjacent
`result.json` contains exact rational enclosure endpoints, the accepted score,
and the tolerance. Replay it directly:

```sh
tools/leanrun --timeout 5m lake --dir proofs/talos/lean env lean --run /absolute/path/to/leanexe/tools/spectral-kl/check.lean /absolute/path/to/request.json
```

The [iteration record](../plans/spectral-kl.md) records the computation proofs,
complete executions, failed attempts, and earlier acceptance-checker limitations. Execution
regressions remain useful for integration failures; they are not the basis of
the mathematical error guarantee.

The low-level `CpuEstimator.score` and `GpuMoments.moments` APIs produce
uncertified proposals. The guarantee applies after the proved check succeeds, as in
the public CLI. A request may be rejected even when its proposed score is
accurate, because a finite partition can give an enclosure wider than the
requested tolerance. The current checker has a five-minute execution limit.
