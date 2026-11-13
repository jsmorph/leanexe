# Discrete Fourier transform

[The implementation](Program.lean) computes the direct discrete Fourier transform of binary64
complex values.  A complex signal is an array of floats with real and imaginary parts
interleaved.  For an array of length `2 * n`, the forward transform computes the floating-point
version of `X k = Σ j, x j * exp (-2 * π * i * j * k / n)`.  It performs `n²` complex products.
An odd final float is ignored.

## Transform conventions

`dft` uses the negative sign in the exponent and keeps the interleaved layout.  `inverse` uses
the positive sign and divides every output component by `n`.  Both return an empty array for
an input with fewer than two floats.  The loops perform no division on that empty path.

`powerSpectrum` takes real samples, adds zero imaginary parts, and returns `|X k|²` for
`0 ≤ k ≤ n / 2`, including both endpoints.  Empty input returns an empty array.  The result
keeps the transform's scale and applies no normalization by the sample count.

`twiddle n m` calls the cosine and sine implementations at the rounded binary64 angle
`6.283185307179586 * (m.toFloat / n.toFloat)`.  The transform uses these factors with the
chosen sign.  [The trigonometric guide](../Float64/Trig/README.md) gives the sine and cosine
implementations and their numerical guarantees.

## Compilation and proof scope

[The compilation module](Compiled.lean) lists the trigonometric routines with the transform.
The `With` functions take the trigonometric tables as borrowed parameters.  The exported
wrappers `twiddle`, `dft`, `inverse`, and `powerSpectrum` supply those tables.

The generated execution theorems state that the compiled module computes these Lean
definitions, including their operation order and floating-point rounding.  Allocation and
call-depth premises determine when the generated trap-free theorems apply, as
[the Verified Compiler Manual](../../../docs/verified-manual.md#the-implements-and-trapfree-theorems)
explains.

## Accuracy theorems

For a signal of `n` complex values `x_j = a_j + i b_j`, the bounds use `θ_jk = 2 π j k / n`,
`M = Σ_j (|a_j| + |b_j|)`, and `γ = (n - 1) / (2^53 - (n - 1))`.  [The master theorems](Master.lean)
state the accuracy of each export on finite inputs.  For `M ≤ 2^1000`, `dft_master` states that
the export `dft` returns finite floats, each within `(γ + 2^-46) M + n / 2^1071` of the
corresponding part of `X_k = Σ_j x_j e^(-i θ_jk)`, and `inverse_master` states that the export
`inverse` returns finite floats, each within `(γ + 2^-45) M / n + 2^-1069` of the corresponding part
of `(1 / n) Σ_j x_j e^(i θ_jk)`.
`twiddle_master` bounds the error of each factor by `2^-48`, and `powerSpectrum_master` places the
float `k` of the spectrum of real samples `s_j` within `5 S E + 3 E^2 + 5 S^2 / 2^53 + 3 / 2^1075`
of `|X_k|^2`, where `S = Σ_j |s_j| ≤ 2^500` and `E` is the transform's bound for that signal.
`dft_spec` and `inverse_spec` state the transforms' bounds for the Lean functions `dft` and
`inverse`.

[The round-trip theorem](RoundTrip.lean) `inverse_dft` states that `inverse (dft xs)`, for an
array of fewer than `2^30` finite floats with `M ≤ 2^960`, returns `2 n` finite floats, each within
`(n + 512) M / 2^51 + 2^-1040` of the float of `xs` at the same index.  The proof composes the two
bounds with the exact inversion `Σ_k X_k e^(i θ_km) = n x_m` over the reals, which follows from
`Σ_k e^(2 π i k d / n) = 0` for `0 < |d| < n`.  The forward error `E` of a component moves the
exact inverse by at most `2 E`, and the inverse adds its own error for a transformed signal of mass
at most `2 n (M + E)`, which the premise `M ≤ 2^960` keeps within the inverse's domain.  Since the
execution theorems state that the exports compute `dft` and `inverse`, the bound holds for the
floats that the export `inverse` returns when called on the result of the export `dft`.

## Accuracy tests

[The accuracy test](../../../tests/TestSupport/Numerics/FourierAccuracy.lean) compares signals
with a reference computed from exact integer sums and 300-bit approximations to the trigonometric
factors.  For `n` complex samples with components `a j` and `b j`, it computes
`τ = 2 * (n + 8) * 2^-53 * Σ j, (abs (a j) + abs (b j))` in binary64 arithmetic.
The reference check divides each absolute component difference by `τ` and requires the largest ratio
to be at most 1.  The forward/inverse round trip compares absolute component differences with
`2 * τ`, about `(n + 8) M / 2^51`, a tolerance below the bound of `inverse_dft`.
The empty-input, ignored trailing-float, and impulse checks use exact equality.  Other checks
cover single-frequency signals, Parseval's identity, and the power spectrum, with the bounds
stated in the test.  The [verified compiler driver](../../../tests/verified/run.sh) builds the
module and runs its registered execution cases.  [Test suites](../../../tests/README.md) distinguishes module
execution comparisons from the native accuracy tests.
