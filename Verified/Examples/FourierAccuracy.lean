import Verified.Examples.Fourier

/-! A native check that `Fourier.dft`, `Fourier.inverse`, and `Fourier.powerSpectrum` behave as
their mathematical counterparts, on finite values.  Some facts hold exactly in floating point: an
empty signal gives an empty result, an odd last float is ignored, an impulse at 0 gives 1 at every
frequency, `X 0` is the sum of the values from left to right, so that one value transforms to
itself under `==`, and a constant 1 gives `n` at frequency 0.  With
`τ = 2 (n + 8) ε Σ j, (|a j| + |b j|)`, `ε = 2 ^ -53`, and `a j + i b j` the values, the constant
gives at most `τ` elsewhere, a single frequency gives `n` there and nearly 0 elsewhere within `τ`,
the result agrees within `τ` with a transform whose factors come from the C library's `cos` and
`sin`, `inverse` undoes `dft` within `2 τ`, and Parseval's identity holds within
`4 τ √(n Σ |x j| ²)`.  For the power spectrum `P` of the real wave `sin (2 π · 5 j / 64)`,
`√(P k)` lies within `2 τ` of the magnitude 32 at frequency 5 and of 0 elsewhere, which covers the
bound `√2 τ` on the magnitude from `τ` on each part and the roundings of the squares and the root.
`τ` follows the error bound of recursive summation, `n` roundings in a sum of `n` terms, with room
for the factors' errors, and is a test tolerance, not a proved bound.  The check exits with an
error at the first failure.  Run with `lake env lean --run`. -/

namespace Verified.Examples.FourierAccuracy

open Verified.Examples

def ε : Float := Float.ofBits 0x3CA0000000000000

def tolerance (xs : Array Float) : Float :=
  let n := (xs.size / 2).toFloat
  2.0 * (n + 8.0) * ε * xs.foldl (fun s v => s + v.abs) 0.0

/-- The transform with factors from the C library's `cos` and `sin`, in the order of
`Fourier.transformWith`. -/
def reference (xs : Array Float) : Array Float := Id.run do
  let n := xs.size / 2
  let mut out := Array.replicate (2 * n) 0.0
  for k in [0:n] do
    let mut re := 0.0
    let mut im := 0.0
    for j in [0:n] do
      let θ := 6.283185307179586 * ((j * k % n).toFloat / n.toFloat)
      let c := Float.cos θ
      let d := -Float.sin θ
      let a := xs[2 * j]!
      let b := xs[2 * j + 1]!
      re := re + (a * c - b * d)
      im := im + (a * d + b * c)
    out := (out.set! (2 * k) re).set! (2 * k + 1) im
  return out

/-- Whether `xs` and `ys` have the same size and agree within `t` part by part. -/
def near (xs ys : Array Float) (t : Float) : Bool :=
  xs.size == ys.size && (List.range xs.size).all fun i => (xs[i]! - ys[i]!).abs ≤ t

def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw <| IO.userError s!"fail: {name}"

end Verified.Examples.FourierAccuracy

open Verified.Examples Verified.Examples.FourierAccuracy in
def main : IO UInt32 := do
  try
    let mut count := 0
    check "an empty signal" (Fourier.dft #[] == #[])
    for n in [1, 2, 3, 4, 5, 7, 8, 12, 16, 31, 64, 100, 256] do
      let xs := Fourier.signal n 1
      let X := Fourier.dft xs
      let t := tolerance xs
      check s!"an odd last float, n = {n}" ((Fourier.dft (xs.push 0.5)).map Float.toBits ==
        X.map Float.toBits)
      -- `X 0` is the sum of the values from left to right.
      let (sa, sb) := (List.range n).foldl
        (fun (sa, sb) j => (sa + xs[2 * j]!, sb + xs[2 * j + 1]!)) ((0.0 : Float), (0.0 : Float))
      check s!"X 0 as the sum, n = {n}" (X[0]! == sa && X[1]! == sb)
      -- An impulse at 0.
      let impulse := (Array.range (2 * n)).map fun i => if i == 0 then 1.0 else 0.0
      check s!"an impulse, n = {n}"
        ((Fourier.dft impulse).toList.zipIdx.all fun (v, i) => v == if i % 2 == 0 then 1.0 else 0.0)
      -- A constant.
      let constant := (Array.range (2 * n)).map fun i => if i % 2 == 0 then 1.0 else 0.0
      let C := Fourier.dft constant
      check s!"a constant, n = {n}" (C[0]! == n.toFloat && C[1]! == 0.0 &&
        (List.range (2 * n - 2)).all fun i => C[i + 2]!.abs ≤ tolerance constant)
      -- The inverse, Parseval's identity, and the reference transform.
      check s!"the round trip, n = {n}" (near (Fourier.inverse X) xs (2.0 * t))
      let energy := xs.foldl (fun s v => s + v * v) 0.0
      let energyX := X.foldl (fun s v => s + v * v) 0.0
      check s!"Parseval's identity, n = {n}"
        ((energyX - n.toFloat * energy).abs ≤ 4.0 * t * Float.sqrt (n.toFloat * energy))
      check s!"the reference transform, n = {n}" (near X (reference xs) t)
      count := count + 1
    -- A single frequency `f`.
    for (n, f) in [(8, 1), (12, 5), (64, 3), (100, 33), (256, 128)] do
      let wave := (Array.range n).foldl (fun acc j =>
        let θ := 6.283185307179586 * ((j * f % n).toFloat / n.toFloat)
        (acc.push (Float.cos θ)).push (Float.sin θ)) #[]
      let X := Fourier.dft wave
      let t := tolerance wave
      check s!"a single frequency {f}, n = {n}" ((List.range n).all fun k =>
        let target := if k == f then n.toFloat else 0.0
        (X[2 * k]! - target).abs ≤ t && X[2 * k + 1]!.abs ≤ t)
      count := count + 1
    -- The power spectrum of a real wave.
    let samples := (Array.range 64).map fun j =>
      Float.sin (6.283185307179586 * ((j * 5 % 64).toFloat / 64.0))
    let P := Fourier.powerSpectrum samples
    let t := tolerance (samples.flatMap fun v => #[v, 0.0])
    check "the power spectrum of a real wave" (P.size == 33 &&
      (List.range 33).all fun k => (Float.sqrt P[k]! - if k == 5 then 32.0 else 0.0).abs ≤ 2.0 * t)
    IO.println s!"fourier accuracy: {count + 2} signals behave as their transforms should"
    return 0
  catch e =>
    IO.eprintln e
    return 1
