# Three audits of GPT numerical error

The audits are complete for the current width-4 implementation and the single
entrywise parameter cap **B=4**. They establish three different conclusions:

1. The real model can be extremely sensitive on permitted parameters. An exact
   construction separates ideal logits by more than 118 after changing an
   embedding contribution that the current first addition rounds away.
2. The evaluation order loses information unnecessarily. Binary64 prototypes
   retaining separate components through centering and evaluating near-uniform
   weighted attention differently reduce the exhibited error from about 59.9
   to below 5e-15 before the binary32 head. These are finite diagnostics of
   unverified prototypes, not a uniform accuracy certificate.
3. The existing error estimates are substantially pessimistic. Their roughly
   4.85e9 result ignores output range and contains demonstrably loose local
   constants. A mathematical range argument gives a cap below 128.000046 for
   the current mixed computation under its specified arithmetic assumptions.
   This cap has not been added as a Lean theorem and is not claimed optimal.

A uniformly tiny error bound for the **current evaluation order** is impossible:
the counterexample proves an error greater than 59 is attainable. No
algorithm-independent impossibility follows. In particular, “a better algorithm
must require stronger parameter assumptions or wider scalar precision” has not
been established, and the prototype results are evidence against treating that
as a settled conclusion.

## Scope and evidence levels

The implementation has context length 4, hidden width 4, two attention heads,
feed-forward width 8 and 256 logits. All parameters, including embeddings,
normalization scales/shifts and biases, obey the single cap. Epsilon is 1e-5.
The hidden computation uses binary64 Wasm, the WGSL matrix projection uses
binary32, and the final bias addition uses binary64. The reference interprets
the stored binary64 parameters as exact real numbers. This is **not** an
all-binary32 or full-size GPT-2 audit; the opening assumption in
[`wgsl-notes.md`](../../wgsl-notes.md) does not describe this implementation.

There are four separate kinds of evidence:

- **Existing checked theorems:** the current source/artifact correspondence and
  numerical bounds, with their documented native-runtime assumptions.
- **Mathematical derivations:** the counterexample separation, sharper local
  constants and output-range cap below. These are not new Lean theorems.
- **Exact rational arithmetic:** 27 BigInt fraction comparisons checking the
  numerical thresholds in those derivations, not their analytic premises.
- **Numerical diagnostics:** pure Lean FP evaluation, existing native execution,
  high-precision reference evaluations and the alternative algorithms.
  Agreement at two precisions is not an interval enclosure.

No production algorithm, Wasm or WGSL artifact was modified. The existing
hidden Wasm SHA-256 is
`d03534266e4171a07512566429763ba890506ba306a6073379d2433b395837a2`;
the checkpoint parameter SHA-256 is
`229eeb877292325c6343079aad6e8543ef569c1b5a4d510debd95d8677689060`.
The audit does not extend the existing runtime-conformance guarantees.

## Audit 1: sensitivity of the real function

### What the single cap implies

Write P=I-11ᵀ/4 and q=Px/sqrt(||Px||₂²/4+epsilon). Then

    sum(q)=0,  ||q||₂<=2,  ||q||₁<=4,  |q_i|<=sqrt(3).

For h=gamma*q+beta, entrywise bounds by B imply ||h||₁<=8B and
|h_i|<=(sqrt(3)+1)B. These retain the vector constraint instead of treating
four independently maximal coordinates as simultaneously attainable.
They give the following real-arithmetic bounds from the same single cap:

| Quantity | Bound | B=4 |
|---|---:|---:|
| Token plus position, per coordinate | 2B | 8 |
| Normalized row, l1 norm | 8B | 32 |
| Normalized row, per coordinate | (sqrt(3)+1)B | 10.929 |
| Q, K or V projection, per coordinate | 8B² | 128 |
| Attention score magnitude | 64 sqrt(2) B⁴ | 23,170.476 |
| Attended value magnitude | 8B² | 128 |
| First residual magnitude | 32B³+3B | 2,060 |
| Expanded FF coordinate and its GELU magnitude | 8B²+B | 132 |
| Second residual magnitude | 96B³+8B²+4B | 6,288 |
| Final logit magnitude | 8B²+B | 132 |

The score range is large, but softmax values remain probabilities and the
attended row remains a convex combination of value rows. The residual bounds
use matrix row-input dimensions 4 and 8, respectively. GELU obeys |GELU(x)|<=|x|.
These are uniform bounds, not assertions that every maximum is attained
simultaneously. Floating-point range proofs require their own rounding margins;
real bounds cannot simply replace computed-value bounds in existing Lean calls.

For a particular final head coordinate, let c_j=sum_i W_ij beta_i+b_j. Then

    logit_j = c_j + sum_i W_ij gamma_i q_i,
    |logit_j-c_j| <= 4B².

Consequently two states with the same head and final normalization parameters
have logit distance at most **8B²=128**, even though the absolute logit magnitude
can be as large as the more permissive bound 132. A common additive shift is
irrelevant to probabilities, but the adversarial head alternates signs across
logits: its discrepancy changes logit differences.

### Which local sensitivities can be improved

For the infinity norm, the exact global Lipschitz constant of width-4
normalization before learned scaling is **3/(2 sqrt(epsilon))**. After scaling,
3B/(2 sqrt(epsilon)) is a uniform bound and is attainable with gamma_i=B.
At B=4 it is about **1,897.367**, versus the existing **2,529.822**.
The derivation and an attaining derivative at a constant vector are in
[the counterexample report](counterexample.md#the-existing-bounds-are-not-optimal).
This result uses the global epsilon floor; it does not justify replacing
constants in arbitrary endpoint-floor lemmas without redoing those arguments.
The Euclidean-norm bound is B/sqrt(epsilon), about 1,264.911. These different
numbers concern different input/output norms.

For softmax, the sharp infinity-to-l1 Jacobian norm is at most **1**, not 2.
For any direction with ||u||∞<=1,

    ||J_softmax u||₁ = E_p |u-E_p u| <= sqrt(Var_p(u)) <= 1.

Two equal probability groups with u=+1 and -1 attain it. More directly,
for g(s)=sum_i softmax(s)_i v_i,

    (gradient g)_i = p_i (v_i-g),
    ||gradient g||₁ = E_p |v-E_p v| <= (max(v)-min(v))/2 <= V

when |v_i|<=V. The variance bound on an interval proves the middle inequality;
equal endpoint masses attain it. Integrating along the score segment gives
|g(s)-g(t)|<=V||s-t||∞. The existing attention perturbation uses **2V**.
Using the value range also preserves invariance to adding a common value.

The specified tanh GELU has a simple global Lipschitz bound **7/4**, improving
the current 4 without claiming the optimum. For x>=0 put y=c*x*(1+a*x²),
where c=sqrt(2/pi), a=0.044715. Then

    G'(x) = (1+tanh(y))/2 + [r*y*sech²(y)]/2,
    r = (1+3a*x²)/(1+a*x²) <= 3.

Since cosh²(y)>=1+y²>=2y, y*sech²(y)<=1/2. Thus 0<=G'(x)<=7/4.
The identity G'(-x)=1-G'(x) extends the absolute derivative bound to x<0.
This derivative bound is deliberately simple; it is not the tight constant.

For a row-vector input and a fixed matrix, the exact infinity-norm gain is
max_j sum_i |W_ij|. Under entrywise cap B alone, nB is sharp: a rank-one
all-B matrix attains it. Reducing that particular uniform factor would require
additional structure or analyzing its interaction with neighboring operations.

### Actual sensitivity and the strict obstruction

The [explicit parameter construction and analytic proof](counterexample.md)
uses a last position embedding of ±2^-55*(1,1,-1,-1), added to (1,1,1,1).
Both round to the same binary64 row. Their ideal even-coordinate logits are
approximately +59.92580537385506 and -59.91959050362319, while both current
native hidden rows are exactly zero. The analytic argument proves values
strictly above +59 and below -59; the triangle inequality rules out a uniform
error bound of 59 or less for the existing algorithm independently of any
upper-bound computation.

Central differences at 100 decimal places, using perturbations 1e-30 and
1e-32, give the following pointwise infinity-to-infinity Jacobian norms for
the remaining real computation from a chosen intermediate to all logits:

| Intermediate perturbed | Checkpoint `Lean` | Positive adversary | Zero-position control |
|---|---:|---:|---:|
| All embedding coordinates | 70.3755 | 2.66273e17 | 6.14748e18 |
| Attention scores | 1.47056 | 1.45338e11 | 3.35544e12 |
| First residual | 37.4009 | 2.83865e8 | 6.55362e9 |
| Second residual | 27.2748 | 875.881 | 20,238.6 |
| Final hidden row | 3.21827 | 16 | 16 |

These are derivatives at individual real states, not global error bounds.
The largest relative change between step sizes is below 2.9e-28. Perturbing an
intermediate leaves other predecessors fixed and recomputes all its dependent
operations, including residual branches. Scores are treated as independently
perturbable coordinates for that diagnostic.

The checkpoint's smallest first-normalization denominator over all 1,024
individual token-position combinations is approximately 0.0301450. Its three
recorded full contexts have second/final denominators well above sqrt(epsilon).
This helps explain their benign behavior. It does not certify all 256^4 full
contexts, and it does not replace the requested universal single-cap contract.

## Audit 2: numerical algorithm and fresh rounding errors

### Validation and where the error starts

The diagnostic transcription agrees **word for word** with the pure Lean FP
model at all 20 recorded stages: 648 words per case, 3,888 across six cases.
The native existing Wasm agrees at all 24 hidden words and preserves memory.
The 768 mixed logits in the three checkpoint contexts match the retained
native WGSL execution evidence for the same parameter/artifact hashes.
Independent real evaluations at 80 and 120 decimal places agree within 1e-55.

“Local error” below means the computed stage versus its ideal formula evaluated
on the **computed predecessors**. “Total error” compares it with the stage of
the **entire ideal model**. The two quantities answer different questions.
For the positive adversary:

| Stage | Fresh local error | Total error |
|---|---:|---:|
| Embedding addition | 2.77556e-17 | 2.77556e-17 |
| First normalization | 2.43198e-16 | 3.51083e-14 |
| Attention scores | 0 | 5.08420e-11 |
| Attended values | 0 | 1.62708e-9 |
| First residual | 0 | 2.60332e-8 |
| Second normalization | 0 | 3.29297e-5 |
| FF expansion | 0 | 5.26876e-4 |
| GELU | 0 | 2.63549e-4 |
| Second residual | 0 | 8.43358e-3 |
| Final normalization | 0 | 3.74536 |
| Binary64 or mixed logits | 0 | 59.9258 |

The first normalization's local maximum comes from other context rows; the
last rounded embedding is constant and normalizes to exactly zero. Subsequent
zeros do not repair the missing signal. This is actual amplification of an
initial representational loss, not merely an exploding upper estimate.

In contrast, the three checkpoint contexts have hidden errors at most 1.87e-15,
binary64-logit errors at most 3.68e-15 and mixed-logit errors at most 7.62e-7.
Their dominant observed error is the binary32 projection. The real logits
across these contexts range approximately from -7.893 to 5.651. These three
examples say nothing about a universal “realistic range” for other models.

### Existing choices that are already sound

The affine binary64 implementation uses balanced dot4/dot8 summation. The
softmax subtracts the maximum score and divides shifted exponentials by their
sum. Negative GELU uses a logistic expression that avoids subtracting nearly
equal quantities. Those choices should be preserved when useful.

ExpNeg uses degree-18 Horner evaluation after at most six halvings, followed
by repeated squaring; arguments below -64 return zero. GELU uses its asymptotic
branches outside [-8,8]. The audit checks ten exponential inputs and eighteen
GELU inputs, including binary64 neighbors of -1, -64 and ±8. Maximum observed
absolute errors are 8.27e-17 and 1.21e-16 respectively, within their existing
proved envelopes. This is a small boundary diagnostic, not exhaustive testing.

Max-shifting prevents exponent overflow. It does **not** prevent cancellation
in sum(p_i*v_i) when nearly uniform probabilities multiply opposing values.
That is the second loss exposed after repairing the initial embedding loss.

### Equivalent formulas worth implementing and proving

The first prototype keeps token, position, attention projection/bias and FF
projection/bias as separate components until a normalization consumes them.
It uses P(sum_r x_r)=sum_r P(x_r), centering each component before adding.
Because the only uses of these residual states are through normalization in
this architecture, the exact-real function is unchanged. Residual components
must remain available across both residual additions; merely changing the first
normalization would be insufficient.

The second prototype also changes attention for score spread <=0.5. Let
m=max(s), d_i=expm1(s_i-m), vbar=sum_i v_i/n. The real identity is

    sum_i softmax(s)_i*v_i
      = vbar + sum_i d_i*(v_i-vbar)/(n+sum_i d_i).

Near equal scores, this computes the small deviation without subtracting
large opposing weighted values. The spread threshold keeps the denominator
at least n*exp(-0.5) in real arithmetic. For larger spreads the prototype uses
the existing shifted-exp division; otherwise n+sum(d) could itself suffer
cancellation. In floating-point arithmetic vbar and all intermediate steps
still require an error analysis.

| Case | Current binary64 logit error | Component centering | Also expm1 attention |
|---|---:|---:|---:|
| +2^-55 adversary | 59.9258 | 5.771e-6 | 4.613e-15 |
| -2^-55 adversary | 59.9196 | 5.774e-6 | 8.964e-16 |
| +2^-60 family member | 5.31329 | 2.979e-4 | 1.824e-15 |
| -2^-60 family member | 5.31315 | 2.980e-4 | 1.484e-15 |

The fixed diagnostic set includes both signs at 2^-60, 2^-55, 2^-50 and 2^-40,
a zero control and the three checkpoint contexts. Across all twelve, the
combined prototype's binary64-logit error is below 5.7e-15 and mixed-logit
error below 1.24e-6. The checkpoint binary64 errors sometimes increase by a
few ulps; this is not a monotonic improvement on every input. Its mixed words
on the three checkpoint cases are unchanged.

These prototypes use native `Math.expm1`, not a verified new exponential
routine. They retain binary64 scalar precision but change which intermediate
quantities are represented. They do not prove uniform small error, optimality,
or suitability for replacing the checked artifacts. A production change needs
real-formula equivalence, roundoff and range proofs, then verification of every
new Wasm artifact and any affected WGSL package.

## Audit 3: pessimism in bound propagation

### Reproduce the existing bound before changing it

[`ErrorBudget.lean`](../../proofs/talos/lean/Project/TinyGpt2/ErrorBudget.lean)
and the WGSL theorem give these allowances at B=4 and all denominator floors
sqrt(epsilon). The script recomputes the actual recurrence, not a fitted model.

| Stage | Existing absolute error allowance |
|---|---:|
| Embedding | 1.999e-15 |
| First normalization | 3.037e-10 |
| Q/K/V projections | 4.860e-9 |
| Scores | 3.742e-6 |
| Attended values | 1.444e-3 |
| First residual | 2.311e-2 |
| Second normalization | 58.4673 |
| FF expansion | 935.477 |
| GELU | 3,741.91 |
| Second residual | 119,741 |
| Final hidden row | 302,923,770 |
| Mixed logits | **4,846,780,324.436** |

The recurrence is additive and linear in the local allowances. Decomposing its
final value by origin shows **98.3251%** comes from the first normalization's
local allowance, **1.66444%** from the embedding allowance, and about 0.01045%
from all others. This is attribution of the *bound*, not observed runtime error.
The first-normalization local allowance is 2.98654e-10, while the maximum
observed local error in these six cases is 3.523e-16.

Several losses are identifiable in source:

- `LayerNorm/Wide.lean` bounds centering error by 8*M*2^-52, converts to an
  l2 allowance 16*M*2^-52, and uses the relaxed denominator floor 1/1000.
  This produces 16000*M*2^-52 before learned scaling. Even retaining that
  centering estimate, using sqrt(1e-5) would replace 16000 by about 5059.645.
  A translation-aware centering analysis can investigate further savings;
  that is a separate derivation, not yet a proved replacement.
- Computed-value safety constants 21, 31, 60000 and 200000 are reused across
  a broad parameter domain. They are much larger than the derived B=4 real
  ranges. Computed ranges need rounding margins and fresh proofs, but the
  current broad constants are not precision-optimal.
- `RuntimeErrorRules.lean` discards the factor 1/sqrt(2) when propagating score
  error and uses 2V for weighted attention. The exact scale and the sharper V
  perturbation constant can be retained.
- Normalization uses 2B/sqrt(epsilon), while 1.5B/sqrt(epsilon) suffices for
  the global epsilon-floor contract. GELU uses 4, while 7/4 suffices.
- Each error becomes an independent symmetric coordinate interval. This loses
  common-shift cancellation in normalization/softmax and dependencies between
  queries, keys and values. Multiplying local worst cases does not establish
  that the whole model can attain their product.
- Propagation continues linearly after its allowance exceeds attainable output
  variation. Final normalization and the bounded head impose a much smaller
  cap regardless of earlier errors.

No single adjustment above establishes the tight global error. In particular,
finite checkpoint denominators, actual checkpoint operator norms and stochastic
rounding assumptions would add information beyond the universal single cap.
They must remain separate certificates or diagnostics.

### A range cap including the current rounding

The exact final normalized vector has l2 norm at most 2. For the computed
centering words c, define qtilde=c/sqrt(sum(c_i²)/4+epsilon); it too has l2 norm
at most 2, even if sum(c_i) is no longer zero. The existing
`LayerNorm/Wide.lean` local argument gives, coordinatewise,

    computed_hidden_i = gamma_i*qtilde_i + beta_i + e_i,
    |e_i| <= r = (254B+2)*2^-52.

Therefore, comparing the exact head on computed hidden with the ideal model,

    |sum_i W_ij*(computed_hidden_i-ideal_hidden_i)| <= 8B²+4Br.

This uses the same gamma, beta and W on both sides. The beta and final head
bias cancel; bounding two absolute logit magnitudes separately wastes that
shared structure. The current finite-range premises are available on B<=10;
this statement is used here at B=4, not arbitrary unbounded floating inputs.

For the head under source-ordered nearest/even IEEE arithmetic with preserved
subnormals, put u=2^-24, eta=2^-150, v=2^-53, xi=2^-1075, H=8B+4r and S=B*H.
Separate binary32 products and accumulation give

    D32 = ((6u+u²)*S + eta*(1+u)*(H+4B) + 4eta² + 7eta)/(1-4u),
    E32 = D32 + v*(S+D32+B) + xi.

The conversion errors contribute (2u+u²)*S and the eta terms. Four products
and three nontrivial additions contribute the conservative gamma4 allowance
and seven additive rounding terms; adding the first product to zero is exact.
The final term accounts for the binary64 bias addition after exact promotion.
This is a derivation for the specified arithmetic, not universal native WGSL
conformance. At B=4, E32 is about 4.57764e-5. Thus

    full mixed error <= 128 + 16r + E32 < 128.000046.

For a binary64 head, the analogous conservative quantities are

    D64 = (4v*S+7xi)/(1-4v),
    E64 = D64 + v*(S+D64+B) + xi,
    full binary64 error < 128.000000000004.

The rational checker includes subnormal terms and checks these rounded-up
thresholds exactly. This is an output-range guarantee, **not a small-error
certificate**. The exact worst error of the current algorithm remains unknown:
the analytic lower result exceeds 59, the measured witness is about 59.9258,
and the derived mixed upper cap is 128.000046. No claim that 128 is optimal
survives this audit.

## Concurrent parent work and resulting engineering decisions

The checkout includes `wgsl-notes.md` from `385b05d3`. Parent `main` was
inspected at `9fb277da`, which adds checked runtime-weight inference and a
binary64 cap `1260+12*B²+B` (1456 at B=4). Those changes were not merged into
the artifacts being measured. The parent cap is consistent with, and more
conservative than, the shared-structure derivation above; it is not evidence
of useful precision. No unrelated parent artifact was regenerated here. A final fetch found parent
`529a5e85`, adding a 64-position checkpoint and sequential-sum bounds. Its
checkpoint documentation explicitly says inference implementation/proofs remain
in progress. It does not change the width-4, four-position ErrorBudget or
CheckedBounds files audited here. Its new checkpoint is outside these results.

The audit supports this order for subsequent implementation:

1. Formalize the shared final-normalization/head cap and the sharper local
   normalization, weighted-attention and GELU bounds. Preserve the single-cap
   statement and the explicit arithmetic assumptions.
2. Prove and implement component-preserving centering, then a near-uniform
   weighted-attention evaluation with a verified expm1 routine or an equivalent
   proved small-argument formula. Carry residual components through all their
   uses. The diagnostic branch threshold is not an approved universal choice.
3. Recheck artifact correspondence and arithmetic bounds for every replacement
   Wasm/WGSL artifact. Use the current witness family as regression evidence,
   while keeping universal theorems distinct from passing examples.

These are implementation findings from completed audits, not claims that the
prototype already satisfies the production verification gates.

## Reproduce and inspect

All scripts use Node and built-in modules only. Retained execution used Node
24.13.0 on macOS arm64; native Math.expm1 results can vary by runtime, so use
the pinned repository runtime when comparing the prototype evidence exactly. `check.js` reruns the numerical
diagnostics and compares them with retained reports. It executes the unchanged
Wasm; it does not build artifacts, install packages or run unrelated regressions.

```sh
node tools/wgsl/audit/check.js
```

To regenerate the pure Lean intermediate trace, first configure the repository
runtime as usual (on the authorized Mac, `source tools/macos-env.sh`), then:

```sh
node tools/wgsl/audit/trace.js
```

The driver invokes only `tools/leanrun`, sequentially, with a 90-second limit
per case. It does not opt into local mode or change priority on its own. Portable
results are retained under [`test/wgsl/numerical-audit`](../../test/wgsl/numerical-audit):
`baseline.json`, `lean-traces.json`, `stages.json`, `sensitivity.json`,
`alternatives.json`, `scalars.json` and `bounds.json`. Runner logs and exact
input word files are in the ignored `build/wgsl/numerical-audit` directory.

The BigInt real reference truncates fixed-point intermediate operations; it
is independent of the binary64 operation order but is not interval arithmetic.
The baseline checks 80/120-place agreement. Derivative step-size convergence
and prototype examples provide additional diagnostics, not mathematical proof.

## Relation to the research notes

The separation into conditioning, local rounding and forward propagation follows
[Beuzeville et al.'s neural-network rounding analysis](https://tmary.perso.lip6.fr/doc/BEA_NN.pdf).
Its probabilistic assumptions are not part of this deterministic contract.
[Castin, Ablin and Peyré](https://proceedings.mlr.press/v235/castin24a.html)
study attention sensitivity on bounded domains; those results motivate keeping
operator and normalization structure rather than multiplying entrywise ranges.
[Blanchard, Higham and Higham](https://doi.org/10.1093/imanum/draa038)
analyze shifted softmax; the existing max-shift/division choice already reflects
that concern. The cancellation identified here is in the subsequent weighted
value sum. None of these sources establishes the new implementation-specific
counterexample or a tiny universal error bound for this model.
