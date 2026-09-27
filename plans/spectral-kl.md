# Spectral KL estimator

Implement on branch `mathalgo` through successive complete executions. Each
iteration must compile the Lean source to WASM, run independent numerical
checks, and state exactly what the Lean proofs cover. Focus on mathematics,
numerical accuracy, and useful behavior.

At every iteration, assess whether substantial work naturally fits a GPU. If
so, implement separate CPU and WebGPU variants against the same mathematical
specification and independent reference. Do not offload tiny scalar kernels
just to exercise WebGPU. Feature evaluation and batch moment accumulation are
the first likely candidates. State their rounding and reduction semantics.

Reference: Francis Bach, https://francisbach.com/spectral_log_density_estimation/
and https://arxiv.org/html/2605.10668v1, Sections 2.1–2.2.

## Iterations

1. One feature with equal normalized second moments: score d²/2. Establish the
   source → compiler → WASM → numerical-reference workflow and floating-point
   model error theorem.
2. Unequal scalar moments near ratio one: cancellation-free polynomial kernel,
   with an approximation theorem and floating-point error accounting.
3. Improve accuracy and add sample input with regularization and explicit
   failure behavior. Check independent quadrature and adversarial cases.
4. Extend the matrix computation through Cholesky and symmetric eigenanalysis;
   establish useful residual-based error contracts before claiming certified
   multivariate results.

The mathematical target is the regularized moment functional. Numerical error
does not certify sampling error or make the empirical result a population KL
lower bound. Second moments are uncentered. Regularization enters both matrices.

## Evidence

Record completed iteration commands and results here as they pass.

### Iteration 1 — equal scalar moments

Completed: `node test/spectral_kl.js` builds the Lean entry, compiles WASM, and
runs it in Wasmtime. Nine accepted cases cover signed zero, both endpoints,
ordinary values, and underflow; five rejection cases cover out-of-range inputs,
infinities, and NaN. All pass.

`lake -d proofs/talos/lean build Project.SpectralKL.Equal` checks the numerical
theorem: on finite |d| ≤ 1, the pure IEEE-754 computation returns a finite value
within 2·2⁻⁵² of d²/2, including underflow. Only the standard three logical
axioms occur. WASM agreement is tested; a universal WASM execution theorem has
not yet been established for this entry.

GPU decision: two scalar multiplications provide no substantial GPU workload.
Keep this iteration CPU-only.

### Iteration 2 — unequal moments near ratio one

Added `kernel2`, the cancellation-free degree-two approximation on |delta| ≤
1/2. `Project.SpectralKL.Kernel2.kernel2_error` proves total absolute error at
most |delta|³/10 + 71·2⁻⁵² against the defining integral for h(1+delta).
The proof accounts for coefficient conversion, rounded operations, and the
analytic remainder. No extra axioms occur.

The WASM test passes ten independent Simpson-quadrature comparisons, including
delta = ±10⁻⁸ and values close to machine epsilon, plus four rejection cases.
Largest observed error was 0.009538972213441799, within the proved bound.
This intentionally coarse approximation provides a checked starting point for
the next accuracy improvement. GPU decision: still a small scalar kernel.

### Iteration 3 — accurate kernel and observations to scalar score

Replaced the coarse kernel in the estimator with degree 40. The reusable
`series_error` theorem bounds any truncation length; `horner_error` exploits
contraction on |delta| ≤ 1/2 to bound rounding independently of polynomial
length. `kernel40_error` combines these into absolute error ≤ 10⁻¹⁴. Lean
checks every binary64 coefficient against its exact rational value.

The WASM gate passes 109 comparisons with an independent 100-digit decimal
logarithm oracle. Maximum observed kernel error: 5.551115123125783e-16. The
sample-to-score entry also passes quadrature comparisons and rejection tests.
It accepts bounded scalar samples and regularization, and explicitly rejects
ratios outside the current kernel interval. The kernel theorem covers the
pure IEEE model; moment accumulation and the complete score currently have
execution tests, not a composed numerical theorem. GPU decision: retain CPU
for this scalar iteration; introduce GPU at the full batch Gram computation.

The compiler rejected a 41-element array literal through `List.toArray`.
Constructing the coefficient array with `Array.push` compiles successfully and
preserves the checked coefficient-list equality.

### Iteration 4 — dense matrices and WebGPU moments

Completed the observations → means and uncentered second moments → Cholesky
whitening → symmetric Jacobi rotations → stable spectral sum pipeline in Lean
and compiled it to WASM. The shared CLI accepts JSON observations, with separate
CPU and GPU modes. See [the guide](../docs/spectral-kl.md) for usage and limits.

`node tools/spectral-kl/build.js`, `node test/spectral_matrix.mjs`, and
`node test/spectral_cli.mjs` pass. Matrix tests compare against Simpson
quadrature with independent pivoted linear solves, for dimensions 1, 2, 3, 8,
16 and 32. The largest case uses 16381 and 16384 observations. The largest
observed difference from quadrature is 1.98e-16. Rank-deficient raw moments,
repeated eigenvalues, sign/permutation invariance, ridge monotonicity, and
explicit failure cases also pass. CPU and GPU cases at minimum ridge and
maximum feature magnitude agree with a rank-one closed form to 2.23e-16,
including a matrix with condition number about 8.6e9. This evidence is numerical testing, not a
matrix error certificate; a composed conditioning and roundoff theorem remains
open.

GPU decision: full batch Gram computation is substantial independent reduction
work. Each of the two 32-feature groups requires roughly 16 million feature
products. Added a separate two-pass WGSL implementation, with the same
binary32 input values as the CPU baseline. CPU accumulation uses binary64;
WGSL uses binary32 and tree reductions. Both feed the same WASM solver.

`node test/spectral_matrix.mjs --gpu --allow-software` passes on Mesa llvmpipe
(Mesa 25.0.7, LLVM 19.1.7) through Dawn `webgpu@0.6.1`. Maximum moment difference
from CPU: 1.43e-8; maximum complete score difference: 2.00e-9. Additional cases
cover 1, 255, 256, 257 and 1031 observations, ±16 features and partial tiles.
Both CLI example modes run end to end. The CPU score is 0.01931482755368568.
No hardware GPU is exposed in this environment; this is software WebGPU
validation. Hardware execution and shader numerical proofs remain open.
The Vulkan loader, Mesa and LLVM shared libraries were extracted locally
under ignored `build/spectral-kl-gpu`, without system installation.

The initial monolithic matrix entry hit the compiler’s 120-second limit.
Splitting it into Cholesky, triangular solve, whitening, rotation and spectral
sum helpers let compilation complete. The mathematical pipeline stayed the
same. A sandbox EPERM blocked CLI subprocess testing; the approved direct
test passed outside that restriction.
