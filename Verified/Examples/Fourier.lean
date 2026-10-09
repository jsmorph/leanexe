import Verified.Examples.Trig

/-! The twenty-fourth program of the verified compiler: the discrete Fourier transform.  A signal
of `n` complex values is an array of `2 n` floats, the real and imaginary parts interleaved, and
the transform computes `X k = Σ j, x j · exp (-2 π i j k / n)` in floating point, in the same
layout, by the `n²` products of the definition.  An odd last float is ignored.  The factors
`exp (-2 π i m / n)` come from `Trig.cosWith` and `Trig.sinWith` at the rounded angle `2 π m / n`,
and the program lists their definitions and compiles them with it.  The functions take Trig's
tables as parameters, and `twiddle`, `dft`, `inverse`, and `powerSpectrum` pass them.  The
compiler's theorem states that the module computes these definitions bit for bit.  For the
functions that allocate, `transformWith`, `dftWith`, `inverseWith`, and `powerSpectrumWith`, and
their wrappers, it also allows a trap at `unreachable` on any input, since an allocation traps
there when memory runs out.  `FourierAccuracy.lean` checks, in native Lean, that they behave as a
Fourier transform. -/

namespace Verified.Examples.Fourier

/-- `(cos θ, sin θ)` for `θ = 2 π m / n`, with the tables `inv` and `half` of `Trig`. -/
def twiddleWith (inv half : Array UInt64) (n m : UInt64) : Float × Float :=
  let θ := 6.283185307179586 * (m.toFloat / n.toFloat)
  (Trig.cosWith inv half θ, Trig.sinWith inv half θ)

/-- The transform of the interleaved signal `xs` with the sign `dir` of the angle: `-1` gives the
forward transform, and `1` the inverse without its factor `1 / n`.  The factors are a local table,
and the output, `2 n` zeros at first, is the outer loop's state, updated in place. -/
def transformWith (inv half : Array UInt64) (dir : Float) (xs : Array Float) : Array Float :=
  let n := xs.size.toUInt64 / 2
  let w : Array (Float × Float) := LeanExe.build n fun m => twiddleWith inv half n m
  LeanExe.loop n (LeanExe.build (2 * n) fun _ => 0.0) fun k out =>
    let s := LeanExe.loop n ((0.0 : Float), (0.0 : Float)) fun j acc =>
      let t := w[(j * k % n).toNat]!
      let c := t.1
      let d := dir * t.2
      let a := xs[(2 * j).toNat]!
      let b := xs[(2 * j + 1).toNat]!
      (acc.1 + (a * c - b * d), acc.2 + (a * d + b * c))
    (out.set! (2 * k).toNat s.1).set! (2 * k + 1).toNat s.2

/-- The forward transform. -/
def dftWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  transformWith inv half (-1.0) xs

/-- The inverse transform: `transformWith 1`, divided by `n` in place. -/
def inverseWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  let n := (xs.size.toUInt64 / 2).toFloat
  let ys := transformWith inv half 1.0 xs
  LeanExe.loop ys.size.toUInt64 ys fun i acc => acc.set! i.toNat (acc[i.toNat]! / n)

/-- The power spectrum `|X k| ^ 2` of the real samples `samples`, for `k` from 0 to `n / 2`. -/
def powerSpectrumWith (inv half : Array UInt64) (samples : Array Float) : Array Float :=
  let n := samples.size.toUInt64
  let xs := LeanExe.build (2 * n) fun i => if i % 2 == 0 then samples[(i / 2).toNat]! else 0.0
  let ys := transformWith inv half (-1.0) xs
  LeanExe.build (if n == 0 then 0 else n / 2 + 1) fun k =>
    let a := ys[(2 * k).toNat]!
    let b := ys[(2 * k + 1).toNat]!
    a * a + b * b

def twiddle (n m : UInt64) : Float × Float := twiddleWith Trig.invPi Trig.halfPi n m

def dft (xs : Array Float) : Array Float := dftWith Trig.invPi Trig.halfPi xs

def inverse (xs : Array Float) : Array Float := inverseWith Trig.invPi Trig.halfPi xs

def powerSpectrum (samples : Array Float) : Array Float :=
  powerSpectrumWith Trig.invPi Trig.halfPi samples

/-- A test signal of `n` complex values with parts in `[-1, 1)`, hashed from `seed`.  The program
does not list it. -/
def signal (n : Nat) (seed : UInt64) : Array Float :=
  (Array.range (2 * n)).map fun i =>
    let h := (UInt64.ofNat i + seed) * 0x9e3779b97f4a7c15
    (h >>> (11 : UInt64)).toFloat / 9007199254740992.0 * 2.0 - 1.0

verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Trig.remSmall, Trig.remMedium,
  Trig.mul64, Trig.clz64, Trig.window, Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2,
  Trig.sinWith, Trig.cosWith, twiddleWith, transformWith, dftWith, inverseWith, powerSpectrumWith,
  twiddle, dft, inverse, powerSpectrum]

end Verified.Examples.Fourier
