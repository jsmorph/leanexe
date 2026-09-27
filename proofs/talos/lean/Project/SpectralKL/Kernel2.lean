import Project.SpectralKL.Real
import Project.ProofKit.F64Horner

namespace Project.SpectralKL
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096

def kernel2Bits (d : UInt64) : UInt64 :=
  Wasm.IEEE64.add
    (Wasm.IEEE64.mul
      (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x3FB5555555555555 d) 0xBFC5555555555555) d)
    0x3FE0000000000000

private theorem c2 : Approximation 0x3FB5555555555555 (1/12) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem c1 : Approximation 0xBFC5555555555555 (-1/6) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem c0 : Approximation 0x3FE0000000000000 (1/2) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

theorem kernel2_roundoff (d : UInt64) (hd : Finite d) (bd : |value d| ≤ 1) :
    Finite (kernel2Bits d) ∧
      |value (kernel2Bits d) - polynomial2 (value d)| ≤ 71*arithmeticEpsilon := by
  have h1 := step c2 c1 hd bd (by norm_num)
  have h0 := step h1 c0 hd bd (by norm_num)
  refine ⟨h0.finite, ?_⟩
  convert h0.accuracy using 1 <;> (try dsimp only [kernel2Bits, polynomial2]) <;> ring

/-- Rounding and approximation error are both included. -/
theorem kernel2_error (d : UInt64) (hd : Finite d) (bd : |value d| ≤ 1/2) :
    Finite (kernel2Bits d) ∧
      |value (kernel2Bits d) - kernel (1+value d)| ≤
        |value d|^3/10 + 71*arithmeticEpsilon := by
  have hn := kernel2_roundoff d hd (bd.trans (by norm_num))
  refine ⟨hn.1, ?_⟩
  have hr := polynomial2_error (value d) bd
  rw [abs_sub_comm] at hr
  exact (abs_sub_le _ _ _).trans ((add_le_add hn.2 hr).trans_eq (add_comm _ _))

#print axioms kernel2_error
end Project.SpectralKL
