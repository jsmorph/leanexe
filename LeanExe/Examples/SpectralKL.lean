import LeanExe.IEEE64
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
    ⟨0, LeanExe.IEEE64.mulBits 0x3FE0000000000000
      (LeanExe.IEEE64.mulBits difference difference)⟩
  else ⟨1, 0⟩

/-- Degree-two approximation to h(1 + delta), evaluated without cancellation. -/
def kernel2Polynomial (delta : UInt64) : UInt64 :=
  LeanExe.IEEE64.addBits
    (LeanExe.IEEE64.mulBits
      (LeanExe.IEEE64.addBits
        (LeanExe.IEEE64.mulBits 0x3FB5555555555555 delta)
        0xBFC5555555555555) delta)
    0x3FE0000000000000

/-- Accept |delta| ≤ 1/2. The exact target is h(1 + delta). -/
def kernel2 (delta : UInt64) : Result :=
  if (delta &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000 then
    ⟨0, kernel2Polynomial delta⟩
  else ⟨1, 0⟩

/-- Fixed-degree Horner evaluation. The explicit sequence avoids unsupported
recursive closures in the compiler. Executable.kernel40_model proves this
function equal to the general IEEE Horner computation for every input word. -/
def kernel40Polynomial (delta : UInt64) : UInt64 :=
  let cs := coefficients40
  let r : UInt64 := 0
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[40]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[39]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[38]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[37]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[36]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[35]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[34]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[33]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[32]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[31]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[30]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[29]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[28]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[27]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[26]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[25]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[24]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[23]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[22]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[21]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[20]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[19]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[18]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[17]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[16]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[15]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[14]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[13]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[12]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[11]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[10]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[9]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[8]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[7]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[6]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[5]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[4]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[3]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[2]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[1]!
  let r := LeanExe.IEEE64.addBits (LeanExe.IEEE64.mulBits r delta) cs[0]!
  r

/-- High-accuracy kernel on |delta| ≤ 1/2, including both signed zeros. -/
def kernel40 (delta : UInt64) : Result :=
  if (delta &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000 then
    ⟨0, kernel40Polynomial delta⟩
  else ⟨1, 0⟩

/-- The complete arithmetic used by the scalar estimator. Callers establish
the numerical domain before invoking this function. -/
def scalarScore (meanP meanQ secondP secondQ regularization : UInt64) : UInt64 :=
  let a := LeanExe.IEEE64.addBits secondP regularization
  let b := LeanExe.IEEE64.addBits secondQ regularization
  let ratio := LeanExe.IEEE64.divBits a b
  let delta := LeanExe.IEEE64.subBits ratio 0x3FF0000000000000
  let difference := LeanExe.IEEE64.subBits meanP meanQ
  let square := LeanExe.IEEE64.mulBits difference difference
  let scale := LeanExe.IEEE64.divBits square b
  LeanExe.IEEE64.mulBits scale (kernel40Polynomial delta)

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
    let a := LeanExe.IEEE64.addBits secondP regularization
    let b := LeanExe.IEEE64.addBits secondQ regularization
    let ratio := LeanExe.IEEE64.divBits a b
    let delta := LeanExe.IEEE64.subBits ratio 0x3FF0000000000000
    if (delta &&& 0x7FFFFFFFFFFFFFFF) > 0x3FE0000000000000 then
      ⟨2, 0⟩
    else
      ⟨0, scalarScore meanP meanQ secondP secondQ regularization⟩

structure ScalarStats where
  status : UInt64
  mean : UInt64
  second : UInt64
  deriving Inhabited

def sampleSum (samples : Array UInt64) : UInt64 :=
  samples.foldl (fun s x => LeanExe.IEEE64.addBits s x) 0

def sampleSquares (samples : Array UInt64) : UInt64 :=
  samples.foldl (fun s x => LeanExe.IEEE64.addBits s (LeanExe.IEEE64.mulBits x x)) 0

def sampleCount (samples : Array UInt64) : UInt64 :=
  samples.foldl (fun s _ => LeanExe.IEEE64.addBits s 0x3FF0000000000000) 0

def samplesBounded (samples : Array UInt64) (bound : UInt64) : Bool :=
  samples.foldl (fun valid x => valid && decide ((x &&& 0x7FFFFFFFFFFFFFFF) ≤ bound)) true

/-- CPU reduction of up to 2^20 scalar samples in [-16,16]. Each reduction is
an explicit fold, shared by execution and the numerical induction proof. -/
def scalarStats (samples : Array UInt64) : ScalarStats :=
  if samples.isEmpty || samples.size > 1048576 || !samplesBounded samples 0x4030000000000000 then
    ⟨1, 0, 0⟩
  else
    let count := sampleCount samples
    ⟨0, LeanExe.IEEE64.divBits (sampleSum samples) count,
      LeanExe.IEEE64.divBits (sampleSquares samples) count⟩

/-- First complete estimator: observations → moments → regularization → score. -/
def fromSamples (p q : Array UInt64) (regularization : UInt64) : Result :=
  let ps := scalarStats p
  let qs := scalarStats q
  if ps.status != 0 || qs.status != 0 then ⟨1, 0⟩
  else scalarMoments ps.mean qs.mean ps.second qs.second regularization

/-- Complete scalar estimator with ridge in [1,256] and samples in [-1/2,1/2].
The output is computed by the estimator itself; no proposed score or numerical
acceptance checker is an input to this function. -/
def fromBoundedSamples (p q : Array UInt64) (regularization : UInt64) : Result :=
  if regularization < 0x3FF0000000000000 || regularization > 0x4070000000000000 ||
      !samplesBounded p 0x3FE0000000000000 || !samplesBounded q 0x3FE0000000000000 then ⟨1,0⟩
  else
    let ps := scalarStats p
    let qs := scalarStats q
    if ps.status != 0 || qs.status != 0 then ⟨1,0⟩
    else ⟨0, scalarScore ps.mean qs.mean ps.second qs.second regularization⟩

/-- Ridge-one specialization of the complete scalar estimator. -/
def fromUnitSamples (p q : Array UInt64) : Result :=
  fromBoundedSamples p q 0x3FF0000000000000

end LeanExe.Examples.SpectralKL
