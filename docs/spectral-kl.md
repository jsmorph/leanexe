# Spectral KL moment estimator

This example implements the regularized moment functional from
[Francis Bach’s spectral log-density article](https://francisbach.com/spectral_log_density_estimation/).
It accepts two groups of feature observations and returns a scalar measure of
their difference. The feature map is supplied by the caller. The empirical
score depends on that map and the regularization; it is not a certified bound
on population KL divergence.

## Run

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
Factorization failure and lack of Jacobi convergence are explicit errors.

### WebGPU variant

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

The Lean implementation factors B = LLᵀ, constructs C = L⁻¹AL⁻ᵀ and z = L⁻¹d,
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

## Proof coverage and checks

Lean proves the scalar kernel’s analytic truncation bound and binary64 rounding
bound against its defining integral. For a finite input |δ| ≤ 1/2,
[`kernel40_error`](../proofs/talos/lean/Project/SpectralKL/Kernel40.lean)
gives absolute error at most **10⁻¹⁴**, including coefficient rounding.
The equal-moment scalar case has its own numerical theorem. These proofs use
the repository’s pure IEEE model and only the standard logical axioms.

The complete matrix computation, sample accumulation, shader arithmetic, and
their composition currently have numerical execution tests. They do not yet
have a composed error theorem, nor a universal theorem connecting this WASM
execution to the numerical model. In particular, 10⁻¹⁴ is a scalar kernel bound,
not an error guarantee for the returned estimator score.

```sh
node test/spectral_kl.js
node tools/spectral-kl/build.js
node test/spectral_matrix.mjs
node test/spectral_cli.mjs
node test/spectral_matrix.mjs --gpu
tools/leanrun --timeout 5m lake -d proofs/talos/lean build Project.SpectralKL.Equal Project.SpectralKL.Kernel2 Project.SpectralKL.Kernel40
```

The scalar WASM checks use a 100-digit decimal logarithm oracle. Matrix checks
use independent quadrature with direct linear solves, and exercise dimensions
1–32, rank deficiency, repeated eigenvalues, orthogonal feature changes, ridge
monotonicity, and rejection. GPU checks compare complete scores and cover
partial reduction tiles. The [iteration record](../plans/spectral-kl.md)
records observed errors and the hardware used.
