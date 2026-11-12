# Gating and track association requirements

## Purpose and scope

The demo serves the association of observations with tracks in catalog maintenance.  A gate decides whether an observation is a candidate for a track: the innovation `ν`, the observation less the track's predicted observation, passes the gate when its squared Mahalanobis distance `ν' S⁻¹ ν` under the innovation covariance `S` is at most a threshold `γ`.  Under the Gaussian model, `ν' S⁻¹ ν` has the chi-square distribution with `d` degrees of freedom, where `d` is the dimension of the observation, so the probability that a true association falls outside the gate is the chi-square distribution's tail at `γ`.  An assignment then pairs observations with tracks at the least total cost among the pairs that the gates admit.

The module `chisquare` encloses the chi-square distribution function and its tail at a point and encloses the quantile at a probability by bisection.  The module `gate` evaluates a gate: it shows `S` positive definite, encloses `ν' S⁻¹ ν`, and gives a verdict against `γ`, and the tail of `chisquare` at `γ` encloses the probability that a true association falls outside the gate.  The module `assignment` checks the optimality of an assignment that an unproved solver proposes, from a dual certificate, by weak duality in integers.  The theorems cover accepted results only.

The first iteration leaves out maneuver detection, whose theorem about false alarms is not yet defined, rectangular assignment problems, which a caller reduces to the square form with dummy rows and columns, multiple-hypothesis tracking, the computation of the innovation and its covariance from a track's state, and the conversion of likelihoods into integer costs.

## The models

### The chi-square distribution

Mathlib has no chi-square distribution, so `Model.chiSquare k` is Mathlib's Gamma distribution `gammaMeasure (k/2) (1/2)` of `Mathlib/Probability/Distributions/Gamma.lean`, with shape `k/2` and rate `1/2`, for a natural number `k ≥ 1`.  `Model.cdf k x` is Mathlib's distribution function `cdf (Model.chiSquare k) x`, the probability of `(-∞, x]`, and `Model.tail k x` is `(Model.chiSquare k).real (Ioi x)`, the probability of `(x, ∞)`.  The density of the Gamma distribution is zero below 0, so both are 0 and 1 for `x < 0`.

For `x ≥ 0` and `y = x/2`, the tail has a closed form in `exp` and `erf` for every `k`.  With `T(a, y) = exp(-y) y^a / Γ(a + 1)`,

`Model.tail k x = E_k(y) + Σ over j from 0 to ⌊k/2⌋ - 1 of T(a₀ + j, y)`,

where `a₀ = 0` and `E_k(y) = 0` for even `k`, and `a₀ = 1/2` and `E_k(y) = erfc(√y) = 1 - erf(√y)` for odd `k`.  For even `k = 2m` the sum is `exp(-y) Σ y^j/j!` over `j < m`, and for odd `k = 2m + 1` its terms are `exp(-y) y^(j + 1/2) / Γ(j + 3/2)`.  The form follows from three facts: `Model.cdf 2 x = 1 - exp(-y)`, `Model.cdf 1 x = erf(√y)`, and the recurrence `Model.cdf (k + 2) x = Model.cdf k x - T(k/2, y)` for `k ≥ 1`, each proved from Mathlib's integral of the Gamma density by the fundamental theorem of calculus.  `erf` is `LeanExe.ProofKit.RealErf.erf`, `(2/√π)` times the integral of `exp(-t²)` from 0 to its argument, and `erfc` is `RealErf.erfc`, `1 - erf`.  The terms satisfy `T(a + 1, y) = T(a, y) · y / (a + 1)`, from `Γ(a + 2) = (a + 1) Γ(a + 1)`, and `T(1/2, y) = 2 exp(-y) √(y/π)`, from `Γ(3/2) = √π / 2`.  For `a ≥ 1/2`, `T(a, y)` is the difference of the tails with `2a + 2` and `2a` degrees of freedom at `2y`, and `T(0, y) = exp(-y)` is the tail with 2 degrees of freedom, so every term lies in `[0, 1]`.

`Model.cdf k` is continuous and strictly increasing on `[0, ∞)` and is 0 at 0, because the density is positive on `(0, ∞)`.  For `0 < p < 1`, `Model.QuantileIn k p lo hi` states that `0 ≤ lo ≤ hi` and that exactly one real `x` has `Model.cdf k x = p`, and that this `x` lies in `[lo, hi]`.

### The gate

For a `d × d` real matrix `S` and a vector `ν` of `d` reals, `Model.mahalanobis S ν` is `ν ⬝ᵥ (S⁻¹ *ᵥ ν)`, with Mathlib's matrix inverse.  For a positive definite `S` (Mathlib's `Matrix.PosDef`), it is the squared Mahalanobis distance.  The gate with threshold `γ` holds the innovations with `Model.mahalanobis S ν ≤ γ`.

The link to probability is the theorem `Model.gaussian_tail`: for `d ≥ 1`, `S` positive definite, and `ν` distributed as Mathlib's `multivariateGaussian 0 S` on `EuclideanSpace ℝ (Fin d)`, the probability of `Model.mahalanobis S ν > γ` equals `Model.tail d γ` for every real `γ`.  It follows from `Model.gaussian_chiSquare`, which states that the law of `Model.mahalanobis S ν` is `Model.chiSquare d`.  The statement reads `ν` through `ofLp`, and it needs `d ≥ 1` because `Model.chiSquare 0` is the zero measure, since Mathlib's `Gamma 0` is 0.  It needs no hypothesis on `γ`: for `γ < 0` both sides are 1.

The proof whitens and then compares moment-generating functions.  `multivariateGaussian 0 S` is by definition the image of the standard Gaussian under `√S = CFC.sqrt S`, and Mathlib's `map_pi_eq_stdGaussian` gives the standard Gaussian as the image of the product of `d` copies of `gaussianReal 0 1`.  `√S` is symmetric and invertible with `√S √S = S`, so `√S S⁻¹ √S = 1` and the distance of `√S z` is `Σ z_i²`, which makes the law of the distance that of the sum of the squares of `d` independent standard normal variables.  For `t < 1/2`, the integral of `exp(t x²)` against `gaussianReal 0 1` is `(1/2 / (1/2 - t))^(1/2)` by Mathlib's Gaussian integral, the product over the coordinates gives the power `d/2`, and the integral of `exp(t x)` against `gammaMeasure (d/2) (1/2)` is the same value by Mathlib's Gamma integral with the rate `1/2 - t`.  Each value is positive, so each integrand is integrable.  The complex moment-generating functions of the two laws are then analytic on the half-plane `re z < 1/2` and agree at its real points, so the identity theorem makes them agree on the imaginary axis, where they are the characteristic functions, and Mathlib's `Measure.ext_of_charFun` makes the laws equal.  Mathlib's own uniqueness lemma for moment-generating functions needs them equal on all of `ℝ`, which the proof avoids.

`gate_miss` applies `Model.gaussian_tail` to an accepted result of `gate`, whose covariance `gate_sound` shows positive definite, with `d` the size of `nu` and `γ` the real value of `g`.  `gate_miss_tail` adds that an accepted result of `tail k g` with `k = d` contains that probability, and `gate_module` includes the conclusion of `gate_miss`.

### The assignment

An instance has `n ≥ 1` rows and `n` columns and an integer cost `c i j` for each pair, or a mark that forbids the pair.  An assignment is a permutation `f` of `{0, …, n - 1}`, which assigns column `f i` to row `i`, and it is admissible when it uses no forbidden pair.  Its cost is `Σ c i (f i)` over `i < n`, in the integers.  A dual certificate is a pair of integer vectors `u` and `v` with `u i + v j ≤ c i j` for every allowed pair.  For an admissible `f` and such a certificate, `Σ c i (f i) ≥ Σ (u i + v (f i)) = Σ u + Σ v`, which is weak duality.  The certificate's inequality needs no exception for a forbidden pair in the program, whose mark `2⁶³ - 1` exceeds every sum of two values in range.  An assignment `π` with `u i + v (π i) = c i (π i)` for every `i` therefore has cost `Σ u + Σ v`, the least cost of any admissible assignment.

## Interface

### The modules `chisquare` and `gate`

```text
module chisquare
  cdf       k : UInt64, x : Float                     ->  status, lo, hi
  tail      k : UInt64, x : Float                     ->  status, lo, hi
  quantile  k : UInt64, p : Float, h : UInt64         ->  status, lo, hi

module gate
  gate      nu : Array Float, s : Array Float, g : Float  ->  status, lo, hi, verdict

k        degrees of freedom, from 1 to 1,000
x        point, finite
p        probability, strictly between 0 and 1
h        halvings of each bisection, from 0 to 64
nu       the innovation, d values, d from 1 to 64
s        the innovation covariance, d·d values in row-major order, symmetric
g        the threshold γ, finite and at least 0
```

`cdf` and `tail` return status 0 with an interval that contains `Model.cdf k x` or `Model.tail k x`, and status 1, with zero endpoints, when `x` is not finite or `k` lies outside its range.  No interval operation rejects for a finite `x` with `k` in range, so every such input gives status 0.

`quantile` returns status 0 with an interval `[lo, hi]` that contains the quantile at `p`, status 1 when `p` is not finite or not strictly between 0 and 1, or when `k` or `h` lies outside its range, and status 2 when the enclosure of the distribution function at the bracket's upper end does not show it at least `p`.  Statuses 1 and 2 have zero endpoints.

`gate` takes `d` from the size of `nu`.  Status 1 marks a size outside the range, an `s` whose size is not `d·d`, a value that is not finite, `g < 0`, or an `s` that is not symmetric, `s[i·d + j] ≠ s[j·d + i]` for some `i` and `j`.  Status 2 marks a covariance that the elimination does not show positive definite and an interval operation that rejects, such as an overflow of the distance.  It includes every covariance that is not positive definite and those whose ill-conditioning the interval elimination cannot resolve, a region that grows with `d`, as the section on the method states.  Statuses 1 and 2 have every other field zero.  With status 0, `[lo, hi]` contains `Model.mahalanobis S ν` for the real values of `s` and `nu`, and the verdict is

```text
1   hi ≤ γ, so the innovation is inside the gate
2   γ < lo, so it is outside
0   neither
```

### The module `assignment`

```text
check  c : Array Int64, perm : Array UInt64, u : Array Int64, v : Array Int64
                                                  ->  status, row, col

perm     the proposed assignment: perm[i] is the column of row i; n is its size
c        costs, n·n values in row-major order; Int64.maxValue, 2⁶³ - 1, forbids the pair
u, v     the dual certificate, n values each
```

The check runs three passes and stops at the first failure, in the order of the passes and, within a pass, of the index.

| Status | Meaning | `row`, `col` |
|---|---|---|
| 0 | Accepted: the assignment is admissible and has the least cost | 0, 0 |
| 1 | `n` is 0 or above 16,384, or `c`, `u`, or `v` has the wrong size | 0, 0 |
| 2 | Pass 1, over `i`: `u[i]` or `v[i]` lies outside `(-2⁶², 2⁶²)` | `i`, 0 |
| 3 | Pass 2, over `i`: `perm[i] ≥ n`, or the pair `(i, perm[i])` is forbidden; or pass 3: two rows `i < j` share a column | Pass 2: `i`, `perm[i]`; pass 3: `j`, `perm[j]` |
| 4 | Pass 3, over `i·n + j`: `u[i] + v[j] > c[i·n + j]` | `i`, `j` |
| 5 | Pass 2, over `i`: `u[i] + v[perm[i]] ≠ c[i·n + perm[i]]` | `i`, `perm[i]` |

Pass 2 checks, for each `i`, the column range, then the mark, then tightness.  Pass 3 runs over the index `t = i·n + j` from 0 to `n² - 1` and checks, for each `t`, the shared column of rows `i < j` and then the dual inequality.  The range of `u` and `v` keeps every sum `u[i] + v[j]` within `Int64` and below the mark, so the program's sums are the integer sums and a forbidden pair never violates the inequality.  The program computes no total cost.  The limit of 16,384 on `n` keeps `c` below the `2²⁹` words of the largest array that the compiled code admits.

## Method

The Lean source fixes the order and grouping of every operation, and the module test compares the module with native Lean bit for bit, so the paragraphs below describe the method and the source is its specification.

### The distribution function and the tail

`tail` evaluates the closed form in [interval arithmetic](../../Library/Numerics/Interval/README.md), with the library's `exp` and `erfc`, each within one step of the nearest-even rounding of the real function and widened by two steps, as the conjunction demo does with `exp` and `erf`.  For `x < 0` it returns `[1, 1]`.  For `0 ≤ x ≤ 1450` it computes the interval `y` of `x · 0.5`, clamped to `[0, x]`, the interval of `exp(-y)` from the library's values at the two ends of `-y`, clamped to `[0, 1]`, and the first term, `exp(-y)` for even `k` and `2 exp(-y) √(y/π)` for odd `k`, with `π` from the interval `piI` of two adjacent doubles and `y/π` clamped to `[0, x]`.  The clamps of `y` and `y/π` keep the square roots from rejecting the lower end that outward rounding moves below 0 when a product rounds to 0.  A loop of `⌊k/2⌋` steps adds the current term to a sum and replaces the term by the term times `x` divided by the integer `2j + 2` for even `k` or `2j + 3` for odd `k`, at step `j` from 0, which is the ratio `y/(a + 1)` of consecutive terms.  For odd `k` the sum starts at the interval of `erfc` at the interval `√y`, clamped to `[0, 1]`, and for even `k` at 0.  Each term is clamped to `[0, 1]`, which holds for the real terms, and the result is clamped to `[0, 1]`.  The clamps keep every finite `x` from overflowing the terms' upper ends.

Near `x = 1,416`, `exp(-x/2)` leaves the normal range, and it rounds to 0 from about 1,490 on, where the closed form's upper end grows toward 1.  For `x > 1450` the program therefore returns the interval from 0 to the upper end of the closed form at 1,450, which contains the tail because the tail decreases.

`cdf` returns `1 - tail`, the difference of the point 1 and the tail's interval, clamped to `[0, 1]`.  Every term of the tail is positive, and `erfc` has a relative accuracy of one step, so the tail keeps its relative accuracy where it is small.  With `u = 2⁻⁵³`, the measured relative width of the tail for `0 ≤ x ≤ 1450` is at most `8 (k + x + 10) u`: each operation adds about one step, and the tail's sensitivity to the rounding of `x` grows with `x`.  The distribution function `1 - tail` has an absolute width of at most `4 (k + 10) u` and loses relative accuracy where it is small.

### The quantile

The quantile at `p` lies in `[0, B]` with `B = k + 2√(40 k) + 80`, computed in binary64 in that order.  By the inequality of Laurent and Massart, `P(X - k ≥ 2√(k t) + 2t) ≤ exp(-t)` for a chi-square `X` with `k` degrees of freedom, so with `t = 40` the tail at `B` is below `exp(-40) ≈ 4.25e-18`, and mpmath gives at most `2.9e-21` for `k ≤ 1000`.  Both lie under the `2⁻⁵³` that separates the largest double below 1 from 1.  The program evaluates the enclosure of the distribution function at `B` and returns status 2 unless its lower end is at least `p`.  No theorem depends on the inequality: the soundness of an accepted result rests only on the enclosures.

Two bisections then narrow `[0, B]`, as the circular error of the conjunction demo does.  Each halving takes the midpoint of the bit patterns of the two ends, `lo.toBits + (hi.toBits - lo.toBits) / 2`, which for two finite doubles at or above 0 is a double between them, so that 63 halvings reach two adjacent doubles from any bracket below `B`.  The first bisection moves its lower end to the midpoint when the enclosure there is accepted and its upper end lies below `p`, and its upper end otherwise, so its lower end always has a distribution function shown below `p`, or is 0.  The second moves its upper end to the midpoint when the enclosure there is accepted and its lower end is at least `p`, and its lower end otherwise, so its upper end always has a distribution function shown at least `p`.  The result is the lower end of the first and the upper end of the second.  Each enclosure in the search rejects a negative point.

The quantile's interval cannot be narrower than the change of `x` that moves the distribution function across its enclosure's width.  For `p` from `1e-6` to `1 - 2⁻⁵³` its measured relative width is at most `2 (k + 10) u / min(p, 1 - p)`: about `4e-15` at `p = 0.5` for small `k`, `2e-11` at `p = 0.999999`, and `0.04` at `p = 1 - 2⁻⁵³`.  Below `p ≈ k u` the enclosure of the distribution function, computed as `1 - tail`, cannot show it above `p`, and the upper end stays where the distribution function reaches about `k u`.  A gate's level `α` enters as `p = 1 - α`, so a level below `2⁻⁵³` cannot be expressed.

### The gate

`gate` checks the sizes, the finiteness of every value, `g ≥ 0`, and the symmetry of `s` by testing `s[i·d + j] ≤ s[j·d + i]` and the reverse for every index, and then eliminates in interval arithmetic.  The state holds a matrix `A` of `d·d` intervals, a vector `r` of `d` intervals, and a sum, starting from the points of `s`, of `nu`, and 0.  Step `k`, for `k` from 0 to `d - 1`, takes the pivot `p = A[k·d + k]` and stops with status 2 unless `p` is accepted with `0 < p.lo`.  It adds `r[k]² / p` to the sum, with the square from the interval library's `sq`, and replaces, for `i, j > k`, `A[i·d + j]` by `A[i·d + j] - (A[i·d + k] / p) · A[j·d + k]` and `r[i]` by `r[i] - (A[i·d + k] / p) · r[k]`, computing the new `A` and `r` as new arrays by `LeanExe.build` and leaving the other entries as they are.  The real counterpart of the elimination is the symmetric Gaussian elimination of `S` and `ν`: after step `k`, the entries with `i, j > k` hold the Schur complement of the leading `(k + 1) × (k + 1)` block, and

`ν' S⁻¹ ν = Σ over k of r_k² / p_k`

with the real pivots `p_k` and right-hand sides `r_k`.  The real `S` is positive definite exactly when every real pivot is positive, which generalizes the conjunction demo's test of `c11 > 0` and of the conditional variance `c22 - c12²/c11 > 0`.  A pivot interval above 0 shows the real pivot positive.

The result's interval is the sum clamped to its part at or above 0, since outward rounding can move an exact 0 one step below 0.  The verdict compares it with `g`.  The probability that a true association falls outside the gate depends only on `d` and `γ`, which a tracker fixes once for a gate, while the verdict runs for each pair of a track and an observation, so `tail d γ` of the module `chisquare` gives it and the gate does not recompute it.

Interval elimination widens its intervals at each step, so the covariances that it shows positive definite form a region that shrinks as `d` grows.  The review's sweep of random positive definite matrices, four for each cell and two at `d = 48` and 64, found these limits of acceptance and widths.

| `d` | Every matrix accepted up to the condition number | Largest relative width of the distance there |
|---|---|---|
| 1 to 9 | `1e12` | `6.8e-1` |
| 10, 16 | `1e10` | `2.1` |
| 24 | `1e8` | `7.8e-2` |
| 32, 48 | `1e6` | `1.7e-1` |
| 64 | `1e4` | `2.7e-3` |

For `d ≤ 9` the relative width is at most about `1e-12` times the condition number.  A tighter enclosure for larger `d`, such as a floating-point Cholesky factorization with a verified bound on its residual, lies outside this iteration.

### The assignment

The three passes read the arrays and allocate nothing.  Pass 1 checks the ranges of `u` and `v`, pass 2 the column range, the marks, and the tightness of each row's pair, and pass 3 the distinct columns and the dual inequality for every pair.  The certificate comes from an unproved solver, such as the Hungarian method with potentials, whose final potentials are a dual certificate for the optimal assignment it returns.  A solver that gives a forbidden pair a large finite cost returns, for an instance without an admissible assignment, an assignment through a forbidden pair, which the check rejects with status 3.

## Theorems

| Theorem | Statement |
|---|---|
| `Model.cdf_two`, `Model.cdf_one`, `Model.cdf_add_two` | For `x ≥ 0` and `y = x/2`: `Model.cdf 2 x = 1 - exp(-y)`, `Model.cdf 1 x = erf(√y)`, and for `k ≥ 1`, `Model.cdf (k + 2) x = Model.cdf k x - T(k/2, y)`. |
| `Model.tail_closed`, `Model.tail_eq_one_sub` | For `k ≥ 1` and `x ≥ 0`, `Model.tail k x` equals the closed form, and for every `x`, `Model.tail k x = 1 - Model.cdf k x`. |
| `Model.term_le_one` | For `k ≥ 1` and `y ≥ 0`, `T(k/2, y) ≤ 1`. |
| `Model.cdf_strictMonoOn`, `Model.cdf_continuousOn`, `Model.cdf_zero` | For `k ≥ 1`, `Model.cdf k` is strictly increasing and continuous on `[0, ∞)` and 0 at 0. |
| `Model.posDef_of_pivots`, `Model.mahalanobis_eq` | For a symmetric `S` whose elimination has positive pivots, `S` is positive definite and `Model.mahalanobis S ν = Σ r_k²/p_k`. |
| `Model.gaussian_chiSquare`, `Model.gaussian_tail` | For `d ≥ 1` and a positive definite `S`, the law of `Model.mahalanobis S ν` under `multivariateGaussian 0 S` is `Model.chiSquare d`, and for every real `γ` the probability of `Model.mahalanobis S ν > γ` is `Model.tail d γ`. |
| `cdf_sound`, `tail_sound` | When `cdf` or `tail` returns status 0, `1 ≤ k ≤ 1000`, `x` is finite, the endpoints are finite, and the interval contains `Model.cdf k x` or `Model.tail k x` for the real value of `x`. |
| `quantile_sound` | When `quantile` returns status 0, `0 < p < 1`, `1 ≤ k ≤ 1000`, the endpoints are finite, and `Model.QuantileIn k p lo hi` holds for the real value of `p`. |
| `gate_sound` | When `gate` returns status 0, `d = nu.size` lies from 1 to 64, `s` holds `d·d` values, `γ` is finite and at least 0, the real matrix `S` of `s` is positive definite, `lo ≤ Model.mahalanobis S ν ≤ hi` for the real values, verdict 1 implies `Model.mahalanobis S ν ≤ γ`, and verdict 2 implies `γ < Model.mahalanobis S ν`. |
| `gate_miss`, `gate_miss_tail` | When `gate` returns status 0, the `multivariateGaussian 0 S` probability of `Model.mahalanobis S ν > γ`, with `S` the real matrix of `s` and `γ` the real value of `g`, is `Model.tail d γ`, and when `tail k g` with `k = d` also returns status 0, its interval contains that probability. |
| `check_sound` | When `check` returns status 0, `n = perm.size` lies from 1 to 16,384, the sizes of `c`, `u`, and `v` are `n²`, `n`, and `n`, `perm` is a permutation of `{0, …, n - 1}` that uses no forbidden pair, its cost equals `Σ u + Σ v`, and every permutation of `{0, …, n - 1}` that uses no forbidden pair has a cost at least as large, all in the integers of the `Int64` values. |
| `compiled.*.implements`, call theorems | Each export returns the words of its function without a trap, from a ready store and, for `gate`, with room for its allocation bound. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  A program that rejects every input, or that returns `[0, 1]` for every tail, satisfies the soundness theorems, so the tests require status 0 and bound the widths where the method gives them.

## Target, memory, and cost

The target is the ground: the verified compiler's WebAssembly modules, run by a host such as Wasmtime, and their translation to C where the translation accepts them.  The Cortex-M7 back end rejects floating point, and an onboard image is outside this iteration.  The compiler's memory cap is at most 65,535 pages of 64 KiB, and its code traps for an array of `2²⁹` words or more.

`cdf` and `tail` allocate nothing and run at most 500 steps of their loop, with two calls of `exp`, one at each end of an interval, and, for odd `k`, two calls of `erfc`.  `quantile` allocates nothing and evaluates the distribution function at most `1 + 2h ≤ 129` times.  `gate` runs `d` steps of elimination, each with about `d²` interval operations of each kind, about 87,000 interval multiplications at `d = 64`, and it allocates, at each step, a new matrix of `d²` intervals and a new vector of `d` intervals, three words each, which the allocation bound of its theorem counts without reuse: `(d + 1)(24 d² + 24 d + 112)` bytes, at most 6,496,880 at `d = 64`.  `check` allocates nothing and performs `n² + 2n` iterations of its passes.  The module `chisquare` reads the table of `exp` and the seven tables of `erfc` from its data, and the modules `gate` and `assignment` have no tables.

## Tests

The distribution test compares `cdf`, `tail`, and `quantile` with `mpmath` at 50 digits, which computes the regularized incomplete gamma functions independently of the closed form.  The inputs hold every `k` from 1 to 12 and `k` of 15, 30, 64, 100, 999, and 1,000, with points at −1, −0, 0, the smallest subnormal, `1e-300`, the quantiles of common gates, 1,480 and 1,500 near the end of the normal range of `exp(-x/2)`, and far in the tail up to `1e300`; the quantile at probabilities from `1e-300` to `1 - 2⁻⁵³` with 0 and 64 halvings; and the rejected inputs.  Every finite `x` with `k` in range must give status 0 with an interval that contains the reference, and every `p` up to `1 - 2⁻⁵³` must give status 0 for the quantile.  The widths must meet the bounds of the method: `8 (k + x + 10) u` for the tail's relative width from 0 to 1,450, `4 (k + 10) u` for the distribution function's absolute width, and `2 (k + 10) u / min(p, 1 - p)` for the quantile's relative width at `p ≥ 1e-6` with 64 halvings.

The gate test compares `gate` with a reference that decides positive definiteness from the pivots of the symmetric elimination of the binary64 values in exact rational arithmetic and computes `ν' S⁻¹ ν` by solving `S x = ν` with mpmath at 50 digits.  The inputs hold covariances of dimensions 1 to 6, 10, 32, and 64, with condition numbers from 1 to `1e12`, correlations of `1 - 1e-12`, matrices with a negative or a zero eigenvalue, an asymmetry between entries that are not adjacent, every cause of status 1, an innovation whose distance overflows, `ν = 0` with `γ = 0` for odd and even `d`, and thresholds equal to the ends of an earlier result's interval.  An input outside the ranges must give status 1, a matrix that is not positive definite must not give status 0, and a positive definite matrix inside the acceptance region of the table above must give status 0.  An accepted result must contain the reference distance, its verdict must be 1 when `hi ≤ γ`, 2 when `γ < lo`, and 0 otherwise, and for `d ≤ 9` its relative width must be at most `1e-12` times the condition number.

The assignment test runs an unproved solver, the Hungarian method with potentials in the test support code, which gives a forbidden pair the cost `2⁵⁰`, on random instances of sizes 1 to 9, 16, 64, and 100 with costs of up to `2⁴⁰` in magnitude, negative costs, and forbidden pairs, among them instances with no admissible assignment.  A Python oracle computes the least cost by enumerating the permutations for `n ≤ 9`, by dynamic programming over subsets of columns for `n = 16`, and by successive shortest augmenting paths with the Bellman–Ford method for larger `n`.  A model of the check in Python, written from the table of statuses, gives the expected status, row, and column of every call, and the program must agree with it.  The certificate of the solver must give status 0 for an instance with an admissible assignment and status 3 for one without, and the cost of each accepted assignment must equal the oracle's least cost and `Σ u + Σ v`.

The mutations of a correct certificate are: `u[0]` raised by 1; `u[0]` raised and `u[n - 1]` lowered by 1; `u[n - 1]` set to `2⁶²`; `perm[0]` set to `n`; the assignment's pair of row 0 forbidden; the columns of rows 0 and 1 exchanged; the column of row 0 repeated in row 1; the same repetition with the cost of that pair set to keep row 1 tight, so that only pass 3 detects it; and the cost of the pair of row 1 and row 0's column lowered below `u[1] + v[perm[0]]`.  Every mutation except the exchange and the raised-and-lowered pair must be rejected, and those two must be rejected or have the least cost.  The special cases add sizes outside the range, dual values at `±(2⁶² - 1)` and costs near `±2⁶³`, a row whose pairs are all forbidden, a repeated column in rows that are not adjacent, and the order of failures between the passes.

The module tests compare the modules with native Lean, bit for bit, on generated cases that include every status.

## What lies outside the theorems

The theorems concern the stated models.  Whether the innovation is Gaussian with mean zero and covariance `S`, the realism of `S`, the choice of `γ` or of `p`, and the choice of the costs are the caller's.  The theorems bound no width: a wide interval is sound, its verdict is then 0, and a status other than 0 carries no statement.  The integer costs of the assignment are premises: the theorem concerns the costs that `check` reads, so a conversion of likelihoods into integers, its rounding, and its scaling lie outside it, and so does the solver.

## References

- [The conjunction demo](../Conjunction/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
- B. Laurent and P. Massart, Adaptive estimation of a quadratic functional by model selection, Annals of Statistics 28(5), 2000, 1302–1338, Lemma 1.  https://doi.org/10.1214/aos/1015957395
- M. Abramowitz and I. A. Stegun, Handbook of Mathematical Functions, 26.4.4 and 26.4.5.
- NIST Digital Library of Mathematical Functions, 8.4 and 8.8, the incomplete gamma functions.  https://dlmf.nist.gov/8
- H. W. Kuhn, The Hungarian method for the assignment problem, Naval Research Logistics Quarterly 2, 1955, 83–97.  https://doi.org/10.1002/nav.3800020109
- Y. Bar-Shalom, P. K. Willett, and X. Tian, Tracking and Data Fusion: A Handbook of Algorithms, YBS Publishing, 2011, on validation gates.
