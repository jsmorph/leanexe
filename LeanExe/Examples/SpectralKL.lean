import LeanExe.Float64
import LeanExe.Examples.SpectralKL.Coefficients

/-! Numerical building blocks for Bach's regularized spectral KL estimator.
Inputs and outputs use binary64 bit patterns. -/
namespace LeanExe.Examples.SpectralKL

structure Result where
  status : UInt64
  bits : UInt64
  deriving Inhabited

/-- First end-to-end case: one feature, A = B = 1, and |mean difference| ≤ 1.
Status 1 rejects inputs outside the stated finite domain. -/
def equalMoments (difference : UInt64) : Result :=
  if (difference &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FF0000000000000 then
    ⟨0, LeanExe.Float64.mulBits 0x3FE0000000000000
      (LeanExe.Float64.mulBits difference difference)⟩
  else ⟨1, 0⟩

/-- Degree-two approximation to h(1 + delta), evaluated without cancellation. -/
def kernel2Polynomial (delta : UInt64) : UInt64 :=
  LeanExe.Float64.addBits
    (LeanExe.Float64.mulBits
      (LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits 0x3FB5555555555555 delta)
        0xBFC5555555555555) delta)
    0x3FE0000000000000

/-- Accept |delta| ≤ 1/2. The exact target is h(1 + delta). -/
def kernel2 (delta : UInt64) : Result :=
  if (delta &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000 then
    ⟨0, kernel2Polynomial delta⟩
  else ⟨1, 0⟩

/-- Horner evaluation, ascending coefficient table traversed in reverse. -/
def kernel40Polynomial (delta : UInt64) : UInt64 := Id.run do
  let cs := coefficients40
  let mut i := cs.size
  let mut result : UInt64 := 0
  while i > 0 do
    i := i - 1
    result := LeanExe.Float64.addBits (LeanExe.Float64.mulBits result delta) cs[i]!
  return result

/-- High-accuracy kernel on |delta| ≤ 1/2, including both signed zeros. -/
def kernel40 (delta : UInt64) : Result :=
  if (delta &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000 then
    ⟨0, kernel40Polynomial delta⟩
  else ⟨1, 0⟩

/-- Scalar moment input. Means are bounded by 16, uncentered second moments
by 256, and regularization is in [2^-20, 256]. Status 2 reports a ratio outside
the current kernel interval [1/2, 3/2]. -/
def scalarMoments (meanP meanQ secondP secondQ regularization : UInt64) : Result :=
  if (meanP &&& 0x7FFFFFFFFFFFFFFF) > 0x4030000000000000 ||
      (meanQ &&& 0x7FFFFFFFFFFFFFFF) > 0x4030000000000000 ||
      secondP > 0x4070000000000000 || secondQ > 0x4070000000000000 ||
      regularization < 0x3EB0000000000000 || regularization > 0x4070000000000000 then
    ⟨1, 0⟩
  else
    let a := LeanExe.Float64.addBits secondP regularization
    let b := LeanExe.Float64.addBits secondQ regularization
    let ratio := LeanExe.Float64.divBits a b
    let delta := LeanExe.Float64.subBits ratio 0x3FF0000000000000
    if (delta &&& 0x7FFFFFFFFFFFFFFF) > 0x3FE0000000000000 then
      ⟨2, 0⟩
    else
      let difference := LeanExe.Float64.subBits meanP meanQ
      let square := LeanExe.Float64.mulBits difference difference
      let scale := LeanExe.Float64.divBits square b
      ⟨0, LeanExe.Float64.mulBits scale (kernel40Polynomial delta)⟩

structure ScalarStats where
  status : UInt64
  mean : UInt64
  second : UInt64
  deriving Inhabited

/-- CPU reduction of up to 2^20 scalar samples in [-16,16]. -/
def scalarStats (samples : Array UInt64) : ScalarStats := Id.run do
  if samples.isEmpty || samples.size > 1048576 then
    return ⟨1, 0, 0⟩
  let mut sum : UInt64 := 0
  let mut squares : UInt64 := 0
  let mut count : UInt64 := 0
  let mut i := 0
  while i < samples.size do
    let x := samples[i]!
    if (x &&& 0x7FFFFFFFFFFFFFFF) > 0x4030000000000000 then
      return ⟨1, 0, 0⟩
    sum := LeanExe.Float64.addBits sum x
    squares := LeanExe.Float64.addBits squares (LeanExe.Float64.mulBits x x)
    count := LeanExe.Float64.addBits count 0x3FF0000000000000
    i := i + 1
  return ⟨0, LeanExe.Float64.divBits sum count, LeanExe.Float64.divBits squares count⟩

/-- First complete estimator: observations → moments → regularization → score. -/
def fromSamples (p q : Array UInt64) (regularization : UInt64) : Result :=
  let ps := scalarStats p
  let qs := scalarStats q
  if ps.status != 0 || qs.status != 0 then ⟨1, 0⟩
  else scalarMoments ps.mean qs.mean ps.second qs.second regularization

end LeanExe.Examples.SpectralKL
