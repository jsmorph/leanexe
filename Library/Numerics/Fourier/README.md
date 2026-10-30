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
explains.  Error bounds for the complete transform and spectrum remain open.

## Accuracy tests

[The accuracy test](../../../tests/TestSupport/Numerics/FourierAccuracy.lean) compares signals
with a reference based on exact integer sums and 300-bit approximations to the trigonometric
factors.  For `n` complex samples with components `a j` and `b j`, it computes
`τ = 2 * (n + 8) * 2^-53 * Σ j, (abs (a j) + abs (b j))` in binary64 arithmetic.
The reference check divides each absolute component difference by `τ` and requires the largest ratio
to be at most 1.  The forward/inverse round trip compares absolute component differences with
`2 * τ`.
The empty-input, ignored trailing-float, and impulse checks use exact equality.  Other checks
cover single-frequency signals, Parseval's identity, and the power spectrum, with the bounds
stated in the test.

The [verified compiler driver](../../../tests/verified/run.sh) builds the module and runs its
registered execution cases.  [Test suites](../../../tests/README.md) distinguishes module
execution comparisons from the native accuracy tests.
