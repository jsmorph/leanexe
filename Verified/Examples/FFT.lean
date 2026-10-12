import Verified.Examples.Fourier

namespace Verified.Examples.FFT

def isRadix2 (n : UInt64) : Bool :=
  n != 0 && (n &&& (n - 1)) == 0

def stageCount (n : UInt64) : UInt64 :=
  (LeanExe.loop (64 : UInt64) (n, (0 : UInt64)) fun _ s =>
    if s.1 > 1 then (s.1 / 2, s.2 + 1) else s).2

def reverseBits (p j : UInt64) : UInt64 :=
  (LeanExe.loop p (j, (0 : UInt64)) fun _ s =>
    (s.1 / 2, 2 * s.2 + s.1 % 2)).2

def copyReversed (p n : UInt64) (xs : Array Float) : Array Float :=
  LeanExe.loop n (LeanExe.build (2 * n) fun _ => (0.0 : Float)) fun j acc =>
    let k := reverseBits p j
    (acc.set! (2 * k).toNat xs[(2 * j).toNat]!).set! (2 * k + 1).toNat
      xs[(2 * j + 1).toNat]!

def stageWith (w : Array (Float × Float)) (dir : Float) (n width : UInt64)
    (ys : Array Float) : Array Float :=
  let h := width / 2
  LeanExe.loop (n / 2) ys fun i acc =>
    let j := i % h
    let lo := (i / h) * width + j
    let hi := lo + h
    let t := w[(j * (n / width)).toNat]!
    let c := t.1
    let d := dir * t.2
    let ar := acc[(2 * lo).toNat]!
    let ai := acc[(2 * lo + 1).toNat]!
    let br := acc[(2 * hi).toNat]!
    let bi := acc[(2 * hi + 1).toNat]!
    let tr := br * c - bi * d
    let ti := br * d + bi * c
    (((acc.set! (2 * lo).toNat (ar + tr)).set! (2 * lo + 1).toNat (ai + ti)).set!
      (2 * hi).toNat (ar - tr)).set! (2 * hi + 1).toNat (ai - ti)

def radix2With (inv half : Array UInt64) (dir : Float) (xs : Array Float) : Array Float :=
  let n := xs.size.toUInt64 / 2
  let p := stageCount n
  let w : Array (Float × Float) := LeanExe.build (n / 2) fun m =>
    Fourier.twiddleWith inv half n m
  let out := copyReversed p n xs
  (LeanExe.loop p (out, (2 : UInt64)) fun _ state =>
    (stageWith w dir n state.2 state.1, 2 * state.2)).1

def fftTransformWith (inv half : Array UInt64) (dir : Float) (xs : Array Float) : Array Float :=
  let n := xs.size.toUInt64 / 2
  if isRadix2 n then radix2With inv half dir xs else Fourier.transformWith inv half dir xs

def fftWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  fftTransformWith inv half (-1.0) xs

def inverseWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  let n := (xs.size.toUInt64 / 2).toFloat
  let ys := fftTransformWith inv half 1.0 xs
  LeanExe.loop ys.size.toUInt64 ys fun i acc => acc.set! i.toNat (acc[i.toNat]! / n)

def powerSpectrumWith (inv half : Array UInt64) (samples : Array Float) : Array Float :=
  let n := samples.size.toUInt64
  let xs := LeanExe.build (2 * n) fun i => if i % 2 == 0 then samples[(i / 2).toNat]! else 0.0
  let ys := fftTransformWith inv half (-1.0) xs
  LeanExe.build (if n == 0 then 0 else n / 2 + 1) fun k =>
    let a := ys[(2 * k).toNat]!
    let b := ys[(2 * k + 1).toNat]!
    a * a + b * b

def fft (xs : Array Float) : Array Float := fftWith Trig.invPi Trig.halfPi xs

def inverse (xs : Array Float) : Array Float := inverseWith Trig.invPi Trig.halfPi xs

def powerSpectrum (samples : Array Float) : Array Float :=
  powerSpectrumWith Trig.invPi Trig.halfPi samples

end Verified.Examples.FFT
