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
