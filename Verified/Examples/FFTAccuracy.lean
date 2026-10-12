import Verified.Examples.FFT
import Verified.Examples.FourierAccuracy

namespace Verified.Examples.FFTAccuracy

open FourierAccuracy

def tolerance (xs : Array Float) : Float :=
  let n := xs.size / 2
  let mass := (xs.toList.take (2 * n)).foldl (fun s v => s + v.abs) 0.0
  let steps := if FFT.isRadix2 (UInt64.ofNat n) then Nat.log2 n + 1 else n + 8
  max (256.0 * steps.toFloat * ε * mass) (8.0 * n.toFloat * Float.ofBits 1)

def finite (x : Float) : Bool := (x.toBits >>> 52 &&& 0x7FF) != 0x7FF

def run : IO Unit := do
  check "FFT empty" (FFT.fft #[] == #[] && FFT.inverse #[] == #[] &&
    FFT.powerSpectrum #[] == #[])
  let mut count := 0
  let mut worst : Float := 0.0
  for n in [1, 2, 3, 4, 5, 8, 16, 31, 32, 64, 128] do
    let random := Fourier.signal n 17
    let impulse := (Array.range (2 * n)).map fun i => if i == 0 then 1.0 else 0.0
    let constant := (Array.range (2 * n)).map fun i => if i % 2 == 0 then 1.0 else 0.0
    let cancellation := (Array.range (2 * n)).map fun i =>
      if i % 2 != 0 then 0.0 else if i % 4 == 0 then 1.0 else -1.0
    let subnormal := (Array.range (2 * n)).map fun i =>
      Float.ofBits (if i % 2 == 0 then 1 else 0x8000000000000001)
    for xs in [random, impulse, constant, cancellation, subnormal] do
      let ys := FFT.fft xs
      let t := tolerance xs
      check s!"FFT size and finiteness, n={n}" (ys.size == 2 * n && ys.all finite)
      check s!"FFT odd tail, n={n}" ((FFT.fft (xs.push (Float.ofBits 0x7FF8000000000042))).map
        Float.toBits == ys.map Float.toBits)
      let distance := distanceIn ys (exact xs) t
      check s!"FFT exact reference, n={n}" (distance ≤ 1.0)
      worst := max worst distance
      check s!"FFT inverse round trip, n={n}" (near (FFT.inverse ys) xs (4.0 * t))
      count := count + 1
    for frequency in [0, 1, n / 2] do
      let wave := (Array.range n).foldl (fun acc j =>
        let (c, s) := cosSin (j * frequency % n) n
        (acc.push c).push s) #[]
      check s!"FFT frequency {frequency}, n={n}"
        (near (FFT.fft wave) (exact wave) (tolerance wave))
      count := count + 1
    let samples := (Array.range n).map fun j => (cosSin (j % n) n).2
    let xs := samples.flatMap fun x => #[x, 0.0]
    let reference := exact xs
    let power := FFT.powerSpectrum samples
    let t := tolerance xs
    let mass := samples.foldl (fun a x => a + x.abs) 0.0
    let countPower := n / 2 + 1
    check s!"FFT power spectrum, n={n}" (power.size == countPower &&
      (List.range countPower).all fun k =>
        let a := reference[2 * k]!
        let b := reference[2 * k + 1]!
        finite power[k]! && power[k]! ≥ 0.0 &&
          (power[k]! - (a * a + b * b)).abs ≤ 8.0 * (mass + t) * t)
    count := count + 1
  IO.println s!"FFT accuracy: {count} signals; maximum component distance {worst} times tolerance"

end Verified.Examples.FFTAccuracy

#eval Verified.Examples.FFTAccuracy.run
