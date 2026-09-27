# Spectral KL estimator

Implement on branch `mathalgo` through successive complete executions. Each
iteration must connect the executed algorithm to its mathematical specification,
check the Lean proofs, and exercise the complete command path. Focus on mathematics,
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

**Correction to the earlier completion claims:** iterations 1–3 initially proved
properties of separately defined IEEE computations without connecting them to
the executable scalar functions. Iteration 4 had no theorem bounding the final
score. Numerical agreement on its test set did not establish either missing
connection. A later nearly dependent-feature case produced an accepted GPU
score about 6.1% too large. The historical execution results below do not
constitute a proof of correctness for those versions.

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

### Repair — verified acceptance of the complete score

The public CLI now treats the matrix solver as a proposal generator. A native
Lean function accepts a proposal only when an exact rational enclosure proves
its error against the original, binary32-quantized observations. The target is
the regularized inverse-matrix integral itself. This is a change to the
algorithm's acceptance path; it is not a proof of the original eigensolver's
internals or of WGSL execution.

`Residual.quadratic_bounds` proves, in arbitrary finite dimension, that for
M ≽ ηI and e=d−Mx, the inverse quadratic form lies between 2dᵀx−xᵀMx and that
quantity plus eᵀe/η. `Samples.system_coercive` establishes the needed lower
bound from sample second moments and a positive ridge. `Certificate.cell_sound`
integrates the energy exactly and bounds the residual throughout each interval.
`Certificate.accepts_sound` combines these cells and the actual acceptance
conditions into the final absolute error theorem. It assumes no accuracy of
the proposal score or candidate solution vectors.

The checker evaluates matrix-vector actions directly over observations, with
one projection and vector update per row. It does not duplicate Gram matrix
construction. Thus the substantial GPU work remains the batch Gram reduction.
The proof is independent of feature dimension, while the CLI retains its
1–32-feature input and spectral-domain limits. Sampling and input-quantization
errors are outside this specification.

`Certificate.Fast.certify` returns an optional `VerifiedScore`, whose type
contains the error bound. Its stored-vector enclosure is proved equal to the
general checker by `enclose_eq`. The first large run of the function-based
checker timed out after five minutes because vector evaluation recomputed
intermediate sums and projections. A first attempt still returned vectors as functions; inspection of generated C
showed that eta expansion moved array construction inside coordinate lookup,
and that run also timed out. The revised implementation keeps `Vector` values
as data throughout accumulation and reuses the computed enclosure. This optimization is connected by a theorem,
not only by numerical comparisons.

The executable scalar source now uses pure integer binary64 definitions.
`Operations.lean` proves their equality with the IEEE model for every input
word. `Executable.kernel40_model` connects the complete executable Horner
sequence to the model, and `kernel40_accepted` derives its input domain from
the actual guard and establishes error ≤1e-14 for accepted source results.
The compiler could not lower a recursive Horner helper; the fixed 41-step
sequence compiles and its equality theorem checks.

The acceptance theorem and its optimized implementation use only `propext`,
`Classical.choice`, and `Quot.sound`. Native execution trusts Lean's runtime,
integer/rational arithmetic, and host I/O. Universal execution theorems for
the emitted WASM module and shader remain absent. The final acceptance theorem
does not require those proposal generators to be correct.

#### Completed executions after the repair

The proof build passes for `Project.SpectralKL.Executable` and
`Project.SpectralKL.CertificateRun`. The equal-moment and degree-two scalar
entry points also have accepted-result error proofs naming their executable
source functions.

Both full examples pass the proved acceptance function at absolute tolerance
1e-6, using eight intervals, 32 features, and groups of 16381 and 16384 rows:

- CPU proposal: 0.01931482755368568. Saved checker input:
  `build/spectral-kl-checks/run-Ba1CQT/request.json`.
- GPU proposal: 0.019314825559756277. Saved checker input:
  `build/spectral-kl-checks/run-JnLeEx/request.json`.

Each directory contains the accepted exact rational enclosure in `result.json`.
These are local execution records under ignored `build/`; the maintained
example generator reproduces the observations. GPU execution used Mesa
llvmpipe software WebGPU; no hardware GPU was exposed.

The nearly dependent-feature counterexample is reproduced in
`test/spectral_cli.mjs --gpu --allow-software`. Its old GPU proposal was
0.09432816505432147, while a high-precision evaluation of the rank-two example
was about 0.08889952711128719. The revised CLI rejects the GPU proposal and
accepts the CPU proposal at 1e-6 with 128 intervals. The high-precision comparison
is a diagnostic; the Lean acceptance proof supplies the error guarantee.

The native command also rejects invalid proposed scores, interval partitions,
solution vectors, ridge values, tolerances and nonfinite input. Those are
integration checks of the host path, not checks of proof soundness. The proof
itself is universally quantified and checked by Lean.

`tools/spectral-kl/verify` is the stable verification entry point. Its targets
select the build, proof audit, scalar/compiler integration, matrix and CLI
checks, or full examples. This avoids separate approval rules for each
combination of environment variables and command arguments.

Final checks passed through that entry point:

```sh
tools/spectral-kl/verify --local audit
tools/spectral-kl/verify --local scalar
tools/spectral-kl/verify --local --software matrix-gpu
tools/spectral-kl/verify --local --software cli-gpu
tools/spectral-kl/verify docs
```

The audit includes `Certificate.Fast.accepted_error`, which states the error
bound directly for the optimized acceptance function executed by the checker.
All printed public error proofs use only the standard three axioms. No
`sorry`, added axiom, or `native_decide` occurs in the spectral proof sources.
The documentation check passes 184 maintained Markdown files; `git diff --check`
passes. The unrelated existing change to `proofs/talos/cases.json` is preserved.

## Proof of the actual scalar computation (2026-09-27)

The acceptance checker above does not fulfill the requested proof of the
numerical algorithm. The matrix computation and GPU shader remain unproved.

The first complete computation proof is now
`Scalar.fromUnitSamples_correct` in `ScalarEstimator.lean`. It quantifies over
all nonempty arrays of at most 2^20 binary64 observations in [-1/2,1/2], with
ridge one. It proves that the actual `fromUnitSamples` function returns status
zero, a finite value, and absolute error at most 1e-6 from the sample integral.
There is no assumed successful result, proposed score, residual input, or
acceptance checker. The theorem uses only the standard three Lean axioms.

`ScalarStats` connects the executed array folds to the sequential IEEE sum
theorem and bounds errors in the computed means and uncentered moments.
`ScalarMoments.score_error` covers every arithmetic step after those reductions.
`KernelContinuity` bounds sensitivity to the computed kernel argument.
`ScalarEstimator.sampleIntegral_eq` connects the spectral expression to the
defining integral. The source uses the same `scalarScore` arithmetic in both
the broad moment API and the bounded sample estimator.

An initial successful-result proof still depended on the broad moment API's
guards. The bounded estimator now invokes the arithmetic directly after its
sample guards: the numerical proof establishes the kernel domain automatically.
This allows a total correctness theorem for every admitted input.

Completed end-to-end commands:

```sh
tools/spectral-kl/verify --local scalar-proof
tools/spectral-kl/verify --local scalar
tools/spectral-kl/verify --local scalar-example
tools/spectral-kl/verify --local scalar-example-wasm
```

Direct Lean execution and WebAssembly each returned 0.004809590922358297 on
groups of 65536 and 65539 observations. This execution record confirms wiring;
the universal Lean theorem supplies the numerical guarantee. Direct Lean is
the scalar CLI's default engine. WebAssembly execution additionally trusts the
compiler's lowering; no universal WASM execution theorem is claimed here.

GPU assessment: the large sample reductions are appropriate parallel work.
The existing binary32 shader is not covered by the scalar binary64 theorem.
A proved GPU version of this iteration remains outstanding.

### Second computation iteration: variable ridge

`Scalar.fromBoundedSamples_correct` generalizes the same actual computation to
every binary64 ridge in [1,256]. Its public premises concern only the input
arrays and ridge, and its conclusion includes success, finiteness, and error
at most 1e-6 against `regularizedIntegral`. The fixed-ridge theorem is now a
specialization. The source and reduction proof are reused; the arithmetic
proof now bounds the rounded regularized moments uniformly up to ridge 256.

The proof build and updated WASM compilation/entry checks passed. On the same
65536/65539-observation example at ridge 3.5, direct Lean and WebAssembly both
returned 0.0014121510604447527. The scalar CLI accepts `eta` in its input JSON
or via `--eta`; direct Lean remains its default engine.

The focused `scalar-audit` target prints the input predicates, exact sample
definitions, integral, executed source functions, public theorem, and axioms.
The second iteration has the same outstanding GPU obligation as the first.

## Full matrix polynomial computation (2026-09-27)

The new matrix implementation computes the same sample-based integral using
exact rational Richardson iteration on vector polynomials. It retains all cross-feature
moments. This is an additional algorithm; it does not establish correctness
of the earlier floating-point Cholesky/Jacobi implementation or WGSL shader.

For S(r) = rP+(1-r)Q, it constructs x₀=0 and
xₖ₊₁(r) = (d−S(r)xₖ(r))/eta, then integrates
(1−r)(2dᵀxₖ−xₖᵀ(S(r)+eta I)xₖ). Rational coefficient lists implement all
polynomial arithmetic. The fixed version performs twelve steps. It stores
sample sums, matrices, and polynomial vectors as data, avoiding recursive
reconstruction through function-valued vectors.

The proof quantifies over every finite dimension and all rational observations
in its domain: nonempty groups, positive eta, sum of the squared entries of
both moment matrices at most eta²/4, and dᵀd at most 32 eta. It imposes no
diagonal, commutativity, or distinct-eigenvalue assumption. The CLI limits
inputs to 32 features and 524288 values per group and decodes binary64 input
exactly. These runtime limits do not restrict the mathematical theorem.

`MatrixIteration.residual_bound_with` proves squared residual reduction by
rho = (‖P‖F²+‖Q‖F²)/eta². `MatrixPolynomial.solution_eval` connects the executed
coefficient-list computation to that recurrence. `sampleScore_error_with`
integrates the resulting error bound. Stored reduction equality theorems
connect the computed statistics to the sample integral. `roundScore_error`
covers the final rounding to twelve decimal places.

Mathlib's abstract polynomial operations were noncomputable, so an initial
attempt to use them could not supply an executable algorithm. The retained
implementation uses explicit rational coefficient lists; its addition,
multiplication, evaluation, and integration lemmas have all checked.

### First end-to-end matrix iteration

`MatrixEstimator.compute_correct` proves that every admitted input produces
an output within 1e-6 of the defining matrix integral. It includes the actual
sample computation, all twelve iteration steps, integration, and output
rounding. It takes no external approximate score or candidate solution.

After the proof build, direct Lean execution completed on:

- 4 correlated features, 64/67 observations: 0.001152501041.
- 32 correlated features, 1024/1027 observations: 0.003949107972.

### Second end-to-end matrix iteration

The adaptive version computes rho and dᵀd/(2 eta) from its input moments,
then chooses a depth whose proved error bound fits the budget after reserving
1e-12 for output rounding. `depth_budget` proves this choice valid.
`computeAdaptive_correct` proves success, at most twelve steps, and error
at most 1e-6 for every admitted input. `computeAdaptive_returned_error` derives
the same bound for every returned value from the executable input guards.
All these theorems use only propext, Classical.choice, and Quot.sound.

The first adaptive CLI execution caught a missing import for the decoder's
IEEE-value equality theorem. After adding the import, direct execution
completed on the same inputs:

- 4 features: one step, 0.001152480693.
- 32 features: two steps, 0.003949107851.

Scaling the 32-feature observations by three produced larger moments within
the same domain. The adaptive method took seven steps and returned
0.034296903457, with the same proved 1e-6 bound.

These executions establish that the native path runs. The universal proofs,
not numerical agreement between runs, establish the bounds.

GPU assessment: this implementation uses variable-size integer and rational
arithmetic, which WebGPU does not supply directly. Offloading it requires a
separate numerical representation and proof. The earlier floating-point Gram
shader remains suitable parallel work with an outstanding computation proof.

The focused matrix audit completed after the final changes. It prints the
exact input predicate, mathematical integral, executed functions, source
equality lemmas, total correctness theorem, returned-result theorem, and
their axioms. The documentation check and `git diff --check` passed. The
pre-existing `proofs/talos/cases.json` change was left untouched.

### Removing the moment/ridge restrictions

The previous input predicate excluded otherwise valid positive-ridge sample
problems. A damped Richardson iteration now uses U = 2(eta²+‖P‖F²+‖Q‖F²),
step eta/U, and squared-residual factor rho = 1-eta²/U. The factor lies in
[0,1) for every positive ridge. The proof uses positivity of the sample
moments and a Frobenius bound; it assumes no spectral separation.

The first proof run rejected a real-valued helper missing `noncomputable`.
That helper belongs to the analysis; the rational algorithm remains
computable. The next run exposed a missing distributivity step in the
polynomial/source equality proof. Expanding the finite sum repaired it.
The wrapper proof then needed its division written explicitly in a `change`
step. These were elaboration failures; none was bypassed with an assumption.

The checked chain now includes the actual stored polynomial recurrence,
integration error, an executable increasing search for a sufficient depth,
and `MatrixGeneral.compute_correct`. Its only input conditions are nonempty
groups and positive eta. The theorem includes sample reductions and decimal
rounding, with absolute error at most 1e-6. A finite search budget follows
from rho^k(1+k(1-rho)) ≤ 1. The search stops when its input-derived bound fits;
it does not inspect or accept a candidate score.

The new modules checked in approximately three seconds each after imports.
The public total and returned-result theorems use only propext,
Classical.choice, and Quot.sound. The bound is deliberately conservative;
termination as a mathematical function is not a practical runtime guarantee
for small ridge values.

The first end-to-end run of the general algorithm completed directly in Lean:

- 4 features, 64/67 observations scaled by eight: 25 steps, 0.060946312006.
- 32 features, 1024/1027 observations scaled by four: 29 steps, 0.059243434961.

Their sums of squared moment entries are approximately 0.368294 and 0.573566,
respectively, above the earlier eta²/4 limit of 0.25. These executions
demonstrate the expanded domain through the CLI; they are not the evidence
for the universal accuracy bound.

### Automatic choice of the recurrence

The next improvement compares the original and damped contraction factors
and uses the smaller one. Both algorithms share the same stored sample
statistics; there is no repeated Gram computation. The original recurrence
can now be selected whenever its factor is smaller, even outside the former
quarter-contraction domain. The selected factor is always below one.

`MatrixGeneral.computeAuto_correct` proves total correctness of this executed
branch and computation on the same general domain. Its returned-result
theorem also checked, using only the three standard axioms. An initial
attempt to refold definitions through `simp` failed; an explicit equality
for the selected sample score fixed the proof. No numerical condition was
added to the public theorem.

Direct Lean execution on the same inputs then took 12 and 20 steps, returning
0.060946311991 and 0.059243434964. A four-feature example scaled by ten
selected the damped branch, took 39 steps, and returned 0.087230974812.
The CLI now defaults to this proved automatic algorithm.

GPU assessment for both iterations: the coefficient operations and sample
reductions here use exact rational arithmetic with variable-size integers.
They do not map directly to WebGPU's native arithmetic. No new GPU variant
was added. The earlier floating-point Gram kernel is still appropriate GPU
work, and its computation proof remains unfinished. This work does not prove
the old Cholesky/Jacobi implementation either.

The final focused audit printed the unrestricted input predicate, the exact
sample integral, the executed automatic branch, both iteration definitions,
the finite depth selector, and the public theorem statements. All public
theorems passed with only propext, Classical.choice, and Quot.sound. The
source scan found no sorry, admit, added axiom, or native_decide in the five
new modules. Documentation checks passed for 184 files, and `git diff --check`
passed. The CLI call at `matrix-series.lean` invokes `computeAuto` directly;
the JSON parsing and Lean runtime remain outside the mathematical proof.

### Exact integer moment reductions for a GPU variant

Work continues with a separate representation for exactly representable
fixed-point observations. A signed 16-bit integer divided by an explicit
positive denominator represents each feature. Inputs are rejected if that
representation would round them. The GPU will perform the actual column and
Gram sums; it will not supply candidate scores for an acceptance checker.

`WordMoments.addWord_value` proves the two-u32 accumulator, including its
carry. `reduce_exact` proves exact reduction for up to 2^20 words. The product
of two biased 16-bit observations fits in one u32, and the complete sums fit
in two. These are the native modulo-2^32 operations specified by WGSL.

The arithmetic proof passed before the estimator bridge. Subsequent failures
were simplification order (the generic UInt32 multiplication lemma expanded
before the exact-product lemma), implicit natural/rational coercions, and
the distinction between a raw two-argument function and Mathlib's `Matrix.of`.
The retained proofs make those representations explicit. The new estimator
uses exact bias correction and the same proved rational score core. That
core was factored into `MatrixGeneral.computeMoments`; its existing public
sample theorem was rebuilt after the refactor.

The GPU program/source connection and dispatch bounds remain to be proved.
The CPU implementation and its end-to-end execution come first.

The CPU estimator theorem subsequently passed. Direct Lean runs returned
0.001152480693 for 4 features and 64/67 observations, and 0.003893093480 for
32 features and 16381/16384 observations. These runs use the two-u32 sums,
exact bias removal, and the shared rational score core.

The shader is a typed expression program with native u32 arithmetic. The
printer emits WGSL; a parser for the used subset consumes the full emitted
module, including its declarations, guard, increasing loop, and output write.
`source_parses` proves the emitted source parses back to the program. The
initial whole-string reduction failed, and a later attempt exited with code
139 after a large memory spike. The retained implementation separates token
parsing from string tokenization and uses `String.toList_ofList` before kernel
reduction. Both source lemmas then checked in about four seconds, without
native_decide or additional axioms.

`WordShaderBounds` proves the u32 addressing arithmetic, positive divisors,
all input/output bounds, active-entry coverage, and exact equality of each
invocation's reduction to the CPU column or Gram reduction. Distinct active
invocations write distinct output elements; the kernel has no shared-memory
updates, barriers, or atomics. `WordShader.compute_correct` composes the parsed
source semantics with the rational estimator. It assumes the uploaded buffer
contains the supplied biased samples in row order. The compiler, device,
buffer transport, and host JSON boundary remain trusted implementations of
those semantics.

The GPU CLI obtains its source directly from Lean, uploads the observations,
executes all column and Gram reductions, and passes only the resulting sums
to the common score core. It does not recompute the moments on the CPU or
check a proposed score. The complete CPU and shader-program theorems have
passed with only propext, Classical.choice, and Quot.sound. WebGPU execution
is the next integration step.

The first GPU launch caught a reserved Lean identifier in the output decoder;
renaming it fixed compilation. The complete GPU pipeline then ran on the
four-feature example and the 32-feature example. It returned 0.001152480693
and 0.003893093480, respectively, through Mesa llvmpipe. All moments in those
runs came from the shader. No hardware adapter was available in these runs.

Review of the host's denominator guard found that a floating-point log2 check
could misclassify a large integer near a power of two. It now checks the
power-of-two property exactly with BigInt before encoding any observations.
The remaining source-composition proof failures were a `congr` invocation
unfolding the parser unnecessarily and a library lemma name. Explicit
`congrArg` equalities and a direct length simplification resolved them.

The fixed-point CPU/GPU iteration is implemented. Work continues on the
small-ridge cost of the shared score calculation, starting with an exact
positive-definite matrix solve suitable for preconditioning.

### Small-ridge preconditioning

The exact rational elimination source and its proof now pass. The recursive
algorithm stores Schur complements and right-hand sides, proves positive
pivots and positive Schur complements, and returns a vector satisfying Ax=b.
The first compilation failures were two algebraic normalization boundaries;
separating the row rewrite from unfolding the vector constructor resolved
them. The midpoint inverse computes coordinate solves, with a theorem that
their stored columns form an inverse. Positivity of the midpoint follows
from the actual sample Gram matrices and eta>0.

The preconditioned polynomial iteration stores both residuals and iterates.
Its residual is multiplied by I-H(r)M each step. A Frobenius bound on the two
endpoint error matrices gives a uniform squared-residual contraction bound.
A new shared energy-integral lemma converts that bound to the target score
bound. The automatic selection retains the previous recurrence whenever its
bound is smaller, so the valid domain remains all nonempty rational sample
groups and every positive ridge. The selected iteration budget and final
decimal rounding are in the complete theorem.

The CPU word and parsed-shader compositions also pass, with only propext,
Classical.choice, and Quot.sound. Both complete execution paths ran on the
512/512-row nearly rank-one example, with eta=2^-20 and shift
(-1/4096,1/4096). They returned 0.060047320542 in three steps. The WebGPU
adapter was llvmpipe; all moments came from the shader. The 32-feature
small-ridge CPU run is underway. The GPU task remains the substantial Gram
reduction; the variable-size rational solve and polynomials stay on the CPU.

The first 32-feature small-ridge run reached the five-minute timeout without
a score. The subsequent revision replaces the sum of the two endpoint
Frobenius bounds by their maximum, justified by convexity of the squared
Frobenius norm. It also factors the midpoint once, stores its pivots and
border vectors, and reuses them for every inverse column. Equality of the
factored solve to the original elimination algorithm is proved for all
matrices and right-hand sides, so the original solve theorem transfers.
The revised computation and CPU/GPU composition proofs pass. The timeout
is retained as a failed execution of the first version.

After the tighter bound and shared factorization were checked, the small
CPU and GPU runs both completed in two steps, returning 0.060047173764. The
score changes because the method now takes fewer steps; the same universal
absolute-error bound applies. The revised large run remains under its
five-minute execution limit. A diagnostic mode now reports the exact
contraction comparisons without starting the polynomial iteration, to
distinguish an unhelpful bound from the cost of polynomial arithmetic if
the larger computation fails to finish.

The revised 32-feature CPU run also timed out (child status 124). Exact
diagnostics subsequently completed: the old contraction is between
0.999999999803 and 0.999999999804; the preconditioned contraction is between
0.581479090711 and 0.581479090712. The preconditioned branch is selected.
The difficulty is the remaining cost of expanding and integrating the
vector polynomials. The general rational CLI separately completed a
four-feature example scaled by binary64 0.3 at eta=2^-20, with score
0.465416924945 in 11 steps. This run uses observations beyond the word
input format.

The next revision streams the centered Neumann coefficient vectors and
integrates their scalar weights. A linear residual error lemma allows
twice as many vector steps to retain the same accuracy budget without
forming quadratic products of vector polynomials. Its source/integral
connection is being proved before replacing the existing score core.

The streamed computation and its full composition now pass Lean checking.
It stores T=-M(P-Q)/2 and starts from Md, repeatedly multiplying the current
coefficient vector by T. Each scalar integration weight is computed exactly
from (1-r)(2r-1)^j. The proof identifies the streamed sum with the linear
inverse-quadratic approximation after 2k preconditioned steps and bounds its
error using the squared residual after those steps. The public theorem now
discharges the midpoint-inverse hypothesis from the actual factorization
and inverse computation. The reported iteration count is 2k on this branch,
the actual number of streamed coefficient terms. All audited dependencies
remain the three standard logical axioms. Complete execution is next.

The streamed CPU and GPU versions both completed the small-ridge,
nearly rank-one case, returning 0.060047173764 with four coefficient terms.
The same 32-feature input that timed out twice is running with the new
source. Its sample data, ridge, error budget, and timeout are unchanged.

The streamed 32-feature CPU run completed within the unchanged five-minute
limit: score 1.192735996967, eta=2^-20, 82 coefficient terms, and
16381/16384 observations. This is the same input that timed out in both
earlier implementations. The corresponding GPU path is now running all
column and Gram reductions before the same streamed score core.

The corresponding large GPU run completed with the same decimal score and
82 coefficient terms. The adapter was Mesa llvmpipe, explicitly allowed as
software. All moments were computed by the shader and passed to the score
core; no CPU moment recomputation or proposed-score checker was used. This
completes the large CPU/GPU execution pair for the streamed revision. The
final theorem audit and general rational CLI rerun follow.

The focused audit passed, printing the admitted domains, target integral,
source functions, complete theorem statements, and standard-only axiom
dependencies. Its output was initially too verbose because it printed
expanded proof terms; theorem declarations now use `#check`, with separate
`#print axioms` commands. The general rational CLI rerun completed with
score 0.465416924945 and 22 streamed coefficient terms. The maintained
documentation and whitespace checks pass. No mathematical guarantee relies
on the execution examples.

The broader spectral audit also passed, including the existing scalar and
earlier matrix theorems together with the new complete computation theorems.
The concise focused audit, documentation check (184 maintained Markdown
files), and whitespace check passed. The work remains on branch mathalgo;
the unrelated cases.json changes were preserved.
