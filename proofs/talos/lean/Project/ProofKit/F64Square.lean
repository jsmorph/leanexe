import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64Square
open CodeLib.IEEE64 F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem approximation (word : UInt64) (exactValue error lower : ℝ)
    (hf : Finite word) (hv : 0 ≤ exactValue ∧ exactValue ≤ 1)
    (he : |value word - exactValue| ≤ error) (hb : error ≤ 1/100)
    (hl : 0 ≤ lower) (hw : lower ≤ value word) :
    Finite (Wasm.IEEE64.mul word word) ∧
    lower^2 - 2*arithmeticEpsilon ≤ value (Wasm.IEEE64.mul word word) ∧
    |value (Wasm.IEEE64.mul word word) - exactValue^2| ≤
      (2+error)*error + 2*arithmeticEpsilon := by
  have hn : 0 ≤ error := (abs_nonneg _).trans he
  have ha := abs_le.mp he
  have hp : 0 ≤ value word := hl.trans hw
  have hu : value word ≤ 101/100 := by linarith
  have hs := mul_error word word hf hf 2 (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg (mul_self_nonneg _)]; nlinarith)
  have hr := abs_le.mp hs.2
  refine ⟨hs.1, by nlinarith, ?_⟩
  have hfactor : |value word + exactValue| ≤ 2+error := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hd : |value word * value word - exactValue^2| ≤ error * (2+error) := by
    rw [show value word * value word - exactValue^2 =
      (value word-exactValue)*(value word+exactValue) by ring, abs_mul]
    exact mul_le_mul he hfactor (abs_nonneg _) hn
  have ht := abs_sub_le (value (Wasm.IEEE64.mul word word))
    (value word * value word) (exactValue^2)
  nlinarith

#print axioms approximation
end Project.ProofKit.F64Square
