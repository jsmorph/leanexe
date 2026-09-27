import Project.ExpArm.ReductionError

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem reduced_word_bound (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    Finite (reducedWord x) ∧ |value (reducedWord x)| ≤ 3/1000 := by
  let kd := Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000
  let high := Wasm.IEEE64.mul kd 0xBF762E42FEFA0000
  let low := Wasm.IEEE64.mul kd 0xBD0CF79ABC9E3B3A
  let first := Wasm.IEEE64.add x high
  let k := (reductionInteger x : ℝ)
  let ideal := value x-k*(Real.log 2/128)
  have hs := integer_selection x hf hx
  have hk : |k| ≤ 189441 := by
    have h := reductionInteger_abs x hf hx
    dsimp [k]
    linarith
  have hi : |ideal| ≤ 11/4000 := ideal_reduction_bound x hf hx
  have hhi : |value 0xBF762E42FEFA0000| ≤ 3/500 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hhprod : |k*value 0xBF762E42FEFA0000| ≤ 1137 := by
    rw [abs_mul]
    exact (mul_le_mul hk hhi (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hh := F64MulBounds.mul_real_mixed kd 0xBF762E42FEFA0000 hs.2.2.1 (by rfl)
    (by rw [hs.2.2.2.1]; exact hhprod.trans_lt (by norm_num))
  have hhe : |value high-k*value 0xBF762E42FEFA0000| ≤ 1/1000000000000 := by
    have he := hh.2
    rw [hs.2.2.2.1] at he
    apply he.trans
    calc
      _ ≤ unitRoundoff64*1137+multiplicationUnderflowEpsilon := by
        gcongr
        norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
  have hlprod : |k*value 0xBD0CF79ABC9E3B3A| ≤ 189441/10000000000000 := by
    rw [abs_mul]
    exact (mul_le_mul hk low_log_bound (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hl := F64MulBounds.mul_real_mixed kd 0xBD0CF79ABC9E3B3A hs.2.2.1 (by rfl)
    (by rw [hs.2.2.2.1]; exact hlprod.trans_lt (by norm_num))
  have hlv : |value low| ≤ 1/50000000 := by
    have he := hl.2
    rw [hs.2.2.2.1] at he
    have herr : |value low-k*value 0xBD0CF79ABC9E3B3A| ≤ 1/100000000000000000000000 := by
      apply he.trans
      calc
        _ ≤ unitRoundoff64*(189441/10000000000000)+multiplicationUnderflowEpsilon := by
          gcongr
          norm_num [unitRoundoff64]
        _ ≤ _ := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
    have ht := abs_add_le (value low-k*value 0xBD0CF79ABC9E3B3A) (k*value 0xBD0CF79ABC9E3B3A)
    rw [sub_add_cancel] at ht
    linarith
  have hd : |k*(value 0xBF762E42FEFA0000+value 0xBD0CF79ABC9E3B3A+Real.log 2/128)| ≤
      189441/(2 : ℝ)^100 := by
    rw [abs_mul]
    exact (mul_le_mul hk split_log_error (abs_nonneg _) (by norm_num)).trans (by ring_nf; rfl)
  have hsum : |value x+value high| ≤ 2751/1000000 := by
    have hid : value x+value high = ideal+
        k*(value 0xBF762E42FEFA0000+value 0xBD0CF79ABC9E3B3A+Real.log 2/128)-
        k*value 0xBD0CF79ABC9E3B3A+(value high-k*value 0xBF762E42FEFA0000) := by
      dsimp [ideal]
      ring
    rw [hid]
    have h1 := abs_le.mp hi
    have h2 := abs_le.mp hd
    have h3 := abs_le.mp hlprod
    have h4 := abs_le.mp hhe
    apply abs_le.mpr
    constructor <;> linarith
  have hfirst := F64AddBounds.add_real_relative x high hf hh.1 (hsum.trans_lt (by norm_num))
  have hfv : |value first| ≤ 2752/1000000 := by
    have herr : |value first-(value x+value high)| ≤ 1/1000000000000000000 := by
      apply hfirst.2.trans
      calc
        _ ≤ unitRoundoff64*(2751/1000000) := by gcongr; norm_num [unitRoundoff64]
        _ ≤ _ := by norm_num [unitRoundoff64]
    have ht := abs_add_le (value first-(value x+value high)) (value x+value high)
    rw [sub_add_cancel] at ht
    linarith
  have hlast : |value first+value low| ≤ 2753/1000000 := (abs_add_le _ _).trans (by linarith)
  have hr := F64AddBounds.add_real_relative first low hfirst.1 hl.1 (hlast.trans_lt (by norm_num))
  have herr : |value (reducedWord x)-(value first+value low)| ≤ 1/1000000000000000000 := by
    apply hr.2.trans
    calc
      _ ≤ unitRoundoff64*(2753/1000000) := by gcongr; norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64]
  refine ⟨hr.1, ?_⟩
  have ht := abs_add_le (value (reducedWord x)-(value first+value low)) (value first+value low)
  rw [sub_add_cancel] at ht
  linarith

#print axioms reduced_word_bound
end Project.ExpArm
