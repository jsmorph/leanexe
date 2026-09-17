# Scope of the impossibility claim and audit of tightness

The result below concerns the existing evaluation order and representation.
It does not establish an impossibility for all algorithms computing the same
real model. Neither the existing error analysis nor the numerical algorithm
has been established to be optimal.

This is a mathematical proof with exact rational checks and independent
execution evidence. Its complete connection to the Lean real model and
artifact has **not** been formalized as a new Lean theorem.

## Precise claim

Let F(theta,t)_j be the ideal real logit defined by `TinyGpt2.Real`, interpreting
the finite binary64 parameter words as their exact real values. Let A(theta,t)_j
be the result of the current computation: round the token-plus-position
embedding componentwise to binary64, then execute the current remaining model
and head.

There are two parameter arrays theta+ and theta-, each with every entry of
magnitude at most 4, and the same input t=(0,1,2,3), such that:

    A(theta+,t)_0 = A(theta-,t)_0,
    F(theta+,t)_0 > 59,
    F(theta-,t)_0 < -59.

It follows that no uniform absolute error bound E <= 59 can hold for A on
all parameter arrays bounded by 4. This conclusion does not use our computed
upper error bound and does not require that bound to be tight.

## Witness parameter arrays

Use width 4, context length 4, two attention heads of dimension 2, feed-forward
width 8, and epsilon=1/100000, as in the existing model. Let

    delta = 2^-55,
    s = (1,1,-1,-1).

The following parameters are common to theta+ and theta-:

- Token embeddings for tokens 0,1,2,3 are s,-s,0,(1,1,1,1), respectively.
- Position embeddings 0,1,2 are zero.
- All three normalization scale vectors are (4,4,4,4); their shifts are zero.
- Q_ij = K_ij = 4 s_i.
- V_ij = Attention_ij = 4 s_i s_j.
- Expand_ij = 4 s_i, for every one of the eight output columns.
- Contract_ij = 4 s_j, for every one of the eight input rows.
- Head_ij = 4 s_i for even j and -4 s_i for odd j.
- All biases and unspecified token embeddings are zero.

The only difference is the last position embedding:

    theta+: position[3] = delta*s,
    theta-: position[3] = -delta*s.

All these numbers are exactly representable in binary64 and have magnitude
at most 4. Alternating the head columns ensures the error changes logit
differences; it is not just a common shift canceled by a final softmax.

## Why the implemented outputs coincide

The binary64 predecessor of 1 is 1-2^-53 and the successor is 1+2^-52.
Therefore nearest/even rounding satisfies, without a tie,

    RN64(1+2^-55) = RN64(1-2^-55) = 1.

Both parameter arrays produce exactly the same four rounded embedding rows:

    s, -s, 0, (1,1,1,1).

In the current model, subsequent operations use those rounded rows and
identical remaining parameters. They do not reintroduce the unrounded
position contribution. Consequently both executions produce the same result.
The parameter memories themselves differ; the claim is equality of the
rounded embedding vectors and of all other parameters subsequently used.

This equality argument also applies if all downstream arithmetic is made
exact while that initial loss of information is retained. The full native
execution additionally confirms that the existing Wasm hidden result is
exactly (0,0,0,0) in both cases. Zero head biases then give zero logits under
either head implementation.

## Real-model separation

For theta+, let a be the first normalized last-row amplitude, q its projected
query/key amplitude, v the positive earlier-row key/value amplitude, A the
attended amplitude, and r1,r2 the centered residual amplitudes. Direct matrix
substitution gives:

    a  = 4 delta / sqrt(delta² + epsilon)
    q  = 16 a
    v  = 64 / sqrt(1 + epsilon)
    t  = sqrt(2) q v
    u  = sqrt(2) q²
    A  = [2 v sinh(t) + q exp(u)] / [2 cosh(t) + 1 + exp(u)]
    r1 = delta + 16 A
    n2 = 4 r1 / sqrt(r1² + epsilon)
    x  = 16 n2
    r2+ = r1 + 32 GELU(x)
    F(theta+,t)_0 = 64 r2+ / sqrt((r2+)² + epsilon).

For theta-, a,q,t,A,r1,n2,x change sign; v and u do not. In particular:

    r2- = -r1 + 32 GELU(-x)
    F(theta-,t)_0 = 64 r2- / sqrt((r2-)² + epsilon).

GELU is not odd, so the two final values are not exact negatives. The negative
case must be bounded separately.

The positive quantities satisfy:

    a > 3.5e-14,
    5.6e-13 < q < 6e-13,
    63.99 < v < 64,
    5.06e-11 < t < 6e-11,
    0 < u < 1e-24,
    2 cosh(t)+1+exp(u) < 4.001,
    1.61e-9 < A < 2e-9,
    2.57e-8 < r1 < 3.3e-8,
    0.00052 < x < 0.001.

These follow using:

- sqrt(delta²+epsilon) between 0.003162 and 0.003163;
- sinh(t) >= t;
- sinh(t) <= t/(1-t²), cosh(t) <= 1/(1-t²), and exp(u) <= 1/(1-u);
- the softmax denominator at least 4;
- monotonicity of r/sqrt(r²+epsilon) for positive r.

The elementary exponential/hyperbolic bounds follow from their convergent
series for the nonnegative arguments less than 1 used here. All numerical
comparisons were checked with exact BigInt fractions, including squared
comparisons for the square roots.

For x>0, GELU(x)>=x/2, hence

    r2+ > 32 * 0.00052 / 2 = 0.00832 > 0.008.

For the negative case, write y=sqrt(2/pi)*(x+0.044715*x³). Since 0<x<0.001,
sqrt(2/pi)<0.8, and 0.044715<0.05, we have 0<y<0.001. Using
0<=tanh(y)<=y,

    |GELU(-x)| = x*(1-tanh(y))/2 > 0.49*x,
    r2- < -32*0.49*0.00052 = -0.0081536 < -0.008.

Finally, r -> 64r/sqrt(r²+epsilon) is increasing, and

    64*0.008/sqrt(0.008²+0.00001) > 59.

The last comparison follows by squaring positive sides:

    0.512² = 0.262144 > 59²*0.000074 = 0.257594.

Thus F(theta+,t)_0>59 and F(theta-,t)_0<-59.

## Impossibility for the existing computation

Let z denote the common implemented output. If both errors were at most 59,
the triangle inequality would give

    F(theta+,t)_0 - F(theta-,t)_0
      <= |F(theta+,t)_0-z| + |z-F(theta-,t)_0|
      <= 118,

contradicting the strict separation above. At least one error is greater than
59. Native execution in fact returned zero for both, so both observed cases
have errors exceeding 59.

An independent full-matrix evaluator, separate from the scalar reduction,
was run at 80 and 120 decimal places. It gave:

| Position contribution | Ideal even-coordinate logit | Native hidden output |
|---|---:|---|
| +delta*s | 59.92580537385506 | four zero words |
| -delta*s | -59.91959050362319 | four zero words |
| zero | 0 | four zero words |

The 80/120-place evaluations differ by less than 1.3e-66 for the two nonzero
cases. This numerical agreement checks the reduction; the strict inequalities
above are the mathematical lower-bound argument. The existing Wasm bytes were
hash-checked and left unchanged; no new Wasm was generated.

## The existing bounds are not optimal

The range argument already improves the previous billions-sized bound to
approximately 128. That does not prove 128 is optimal.

There is also a concrete improvement to the uniform normalization sensitivity
bound. For the four-component real map

    N(x) = (x-mean(x)*1)/sqrt(||x-mean(x)*1||₂²/4+epsilon),

its exact global Lipschitz constant in the infinity norm is

    3/(2*sqrt(epsilon)).

Consequently, with fixed learned scales of magnitude at most B and fixed
shifts, 3B/(2*sqrt(epsilon)) suffices. The current uniform composition uses
2B/sqrt(epsilon). This improves that factor by 25%, although by itself it does
not make the whole-model bound useful. This statement concerns the global
epsilon floor; it does not assert an interchangeable constant for every
theorem using arbitrary endpoint denominator floors.

Here is a derivation. Put P=I-11^T/4, z=Px, and, for z nonzero,

    v=z/||z||₂,
    tau=||z||₂²/(||z||₂²+4*epsilon).

The Jacobian is

    J_N = sqrt(1-tau)/sqrt(epsilon) * (P-tau*v*v^T).

If tau<=1/2, all off-diagonal entries of P-tau*v*v^T are nonpositive:
|v_i*v_j|<=1/2. The matrix has zero row sums and nonnegative diagonal, so
each absolute row sum is twice its diagonal, at most 3/2.

If tau>=1/2, the squared Euclidean norm of each row is at most P_ii=3/4,
because (P-tau*v*v^T)^2 <= P as positive-semidefinite matrices. Each absolute
row sum is therefore at most sqrt(3). Multiplying by sqrt(1-tau) gives at
most sqrt(3/2)<3/2.

It follows that ||J_N||_infinity <= 3/(2*sqrt(epsilon)) everywhere. Integration
along a line segment gives the global Lipschitz bound. At a constant input,
J_N=P/sqrt(epsilon), whose infinity operator norm is exactly the stated
constant; no smaller global constant can work. Learned shifts have zero
derivative, and row scaling contributes at most B.

This sharper lemma is a mathematical derivation here, not a new checked Lean
lemma. It is an explicit reason to reject an assertion that our current local
constants are already best possible.

## The existing numerical algorithm is not known to be optimal

The input representation currently discards delta at the initial embedding
addition. A two-component binary64 sum can retain, exactly in this example,

    1+delta as (high=1, low=delta),
    1-delta as (high=1, low=-delta).

Keeping those components through centering prevents this specific information
loss. Another identity available for redesign is P(token+position)=P(token)+
P(position), which permits centering before combining the components for the
normalization branch. Residual branches must also be handled deliberately;
this identity alone is not a complete replacement algorithm.

Neither modification has been shown here to achieve a uniformly tiny error
for every permitted parameter array. They demonstrate that the existing
counterexample does not establish an algorithm-independent impossibility.
Other cancellation and rounding sites require their own analysis. Higher
precision, compensated representations, and certified adaptive evaluation
remain possible approaches under the same weight cap.

The justified conclusions are: the existing computation cannot have a
uniform error bound at or below 59; the current upper bounds have known
slack; and no optimality claim about the implementation is established.

Reproduce from the repository root with `node tools/wgsl/audit/baseline.js`
and `node tools/wgsl/audit/inequalities.js`. The former checks the three
checkpoint contexts and all three adversarial arrays against the existing
Wasm and an independent full-matrix reference at 80 and 120 decimal places.
Parameter construction is in `tools/wgsl/audit/cases.js`; the reference is
`tools/wgsl/audit/real.js`. Retained results are in
`test/wgsl/numerical-audit/baseline.json`.
