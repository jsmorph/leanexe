import Project.ExpArm.HighProduct

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

def reducedWord (x : UInt64) : UInt64 :=
  let kd := Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000
  Wasm.IEEE64.add (Wasm.IEEE64.add x (Wasm.IEEE64.mul kd 0xBF762E42FEFA0000))
    (Wasm.IEEE64.mul kd 0xBD0CF79ABC9E3B3A)

theorem low_log_bound : |value 0xBD0CF79ABC9E3B3A| ≤ 1/10000000000000 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem reduction_error (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 800) :
    Finite (reducedWord x) ∧
    |value (reducedWord x) - (value x - (reductionInteger x : ℝ) * (Real.log 2/128))| ≤
      1/1000000000000000000 ∧
    |value (reducedWord x)| ≤ 3/1000 := by
  let kd := Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000
  let high := Wasm.IEEE64.mul kd 0xBF762E42FEFA0000
  let low := Wasm.IEEE64.mul kd 0xBD0CF79ABC9E3B3A
  let first := Wasm.IEEE64.add x high
  let k := (reductionInteger x : ℝ)
  let ideal := value x - k * (Real.log 2/128)
  have hx' : |value x| ≤ 1024 := hx.trans (by norm_num)
  have hs := integer_selection x hf hx'
  have hk : |k| ≤ 148001 := by
    have h := reductionInteger_abs x hf hx'
    dsimp [k]
    linarith
  have hi : |ideal| ≤ 11/4000 := ideal_reduction_bound x hf hx'
  have hh := reduction_high_product x hf hx
  have hd : |k * (value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128)| ≤
      148001/(2 : ℝ)^100 := by
    rw [abs_mul]
    calc
      _ ≤ 148001 * (1/(2 : ℝ)^100) :=
        mul_le_mul hk split_log_error (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hlp : |k * value 0xBD0CF79ABC9E3B3A| ≤ 148001/10000000000000 := by
    rw [abs_mul]
    calc
      _ ≤ 148001 * (1/10000000000000) :=
        mul_le_mul hk low_log_bound (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hl := F64MulBounds.mul_real_mixed kd 0xBD0CF79ABC9E3B3A hs.2.2.1 (by rfl)
    (by rw [hs.2.2.2.1]; exact hlp.trans_lt (by norm_num))
  have hle : |value low - k * value 0xBD0CF79ABC9E3B3A| ≤ 1/100000000000000000000000 := by
    have h := hl.2
    rw [hs.2.2.2.1] at h
    refine h.trans ?_
    calc
      _ ≤ unitRoundoff64 * (148001/10000000000000) + multiplicationUnderflowEpsilon := by
        gcongr
        norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
  have hlv : |value low| ≤ 15/1000000000 := by
    have ht := abs_add_le (value low-k*value 0xBD0CF79ABC9E3B3A)
      (k*value 0xBD0CF79ABC9E3B3A)
    rw [sub_add_cancel] at ht
    linarith
  have hfirst : |value x + value high| ≤ 2751/1000000 := by
    have he : value x + value high = ideal +
        k*(value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128) -
        k*value 0xBD0CF79ABC9E3B3A := by
      rw [hh.2]
      dsimp [ideal, k]
      ring
    rw [he]
    have ht := abs_sub
      (ideal + k*(value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128))
      (k*value 0xBD0CF79ABC9E3B3A)
    have ha := abs_add_le ideal
      (k*(value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128))
    linarith
  have hf1 := F64AddBounds.add_real_relative x high hf hh.1 (hfirst.trans_lt (by norm_num))
  have he1 : |value first - (value x + value high)| ≤ 31/100000000000000000000 := by
    refine hf1.2.trans ?_
    calc
      _ ≤ unitRoundoff64 * (2751/1000000) := by gcongr; norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64]
  have hv1 : |value first| ≤ 2752/1000000 := by
    have ht := abs_add_le (value first-(value x+value high)) (value x+value high)
    rw [sub_add_cancel] at ht
    linarith
  have hsum : |value first + value low| ≤ 2753/1000000 := by
    exact (abs_add_le _ _).trans ((add_le_add hv1 hlv).trans (by norm_num))
  have hf2 := F64AddBounds.add_real_relative first low hf1.1 hl.1 (hsum.trans_lt (by norm_num))
  have he2 : |value (reducedWord x) - (value first + value low)| ≤ 31/100000000000000000000 := by
    refine hf2.2.trans ?_
    calc
      _ ≤ unitRoundoff64 * (2753/1000000) := by gcongr; norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64]
  have herr : |value (reducedWord x)-ideal| ≤ 1/1000000000000000000 := by
    have he : value (reducedWord x)-ideal =
        (value (reducedWord x)-(value first+value low)) +
        (value first-(value x+value high)) +
        (value low-k*value 0xBD0CF79ABC9E3B3A) +
        k*(value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128) := by
      rw [hh.2]
      dsimp [ideal, k]
      ring
    rw [he]
    calc
      _ ≤ |value (reducedWord x)-(value first+value low)| +
          |value first-(value x+value high)| + |value low-k*value 0xBD0CF79ABC9E3B3A| +
          |k*(value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128)| := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := (add_le_add (add_le_add (add_le_add he2 he1) hle) hd).trans (by norm_num)
  refine ⟨hf2.1, herr, ?_⟩
  have ht := abs_add_le (value (reducedWord x)-ideal) ideal
  rw [sub_add_cancel] at ht
  linarith

#print axioms reduction_error
end Project.ExpArm
