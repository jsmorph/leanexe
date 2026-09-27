import LeanExe.Float64

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

end LeanExe.Examples.SpectralKL
