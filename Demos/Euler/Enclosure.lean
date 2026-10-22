import Library.Numerics.Bounds.Proof
import Demos.Euler.ReconstructedSpec
import Demos.Euler.Outward
import Demos.Euler.RealState
import LeanExe.ProofKit.F64OutwardAccepted
import LeanExe.ProofKit.F64AdjacentSigned

/-! Real-number bounds for the reconstructed Euler solver: its outward operations agree with
the word-level outward operations of `LeanExe.ProofKit.F64Outward`, whose results bound the exact
result from above or below. -/

namespace Demos.Euler

open Demos.Euler LeanExe.ProofKit

set_option exponentiation.threshold 4096

export Library.Numerics.Bounds (checkedWord endpoint_word endpoint_rejected outAdd_word outAdd_accepted outSub_word outSub_accepted outMul_word outMul_accepted outDiv_word outDiv_accepted outSqrt_word outSqrt_accepted)

open CodeLib.IEEE64 (value Finite)

theorem real_half : real 0.5 = 1 / 2 := by
  rw [real, half_toBits, value, show Wasm.IEEE64.scaledValue 0x3FE0000000000000 = 2 ^ 1073 by
    decide +kernel]
  push_cast
  norm_num

theorem real_twoFifths : 2 / 5 ≤ real 0.4 := by
  rw [real, twoFifths_toBits, value, show Wasm.IEEE64.scaledValue 0x3FD999999999999A =
    7205759403792794 * 2 ^ 1020 by decide +kernel]
  push_cast
  norm_num

theorem real_gammaUp : 7 / 5 ≤ real 1.4000000000000001 := by
  rw [real, gammaUp_toBits, value, show Wasm.IEEE64.scaledValue 0x3FF6666666666667 =
    6305039478318695 * 2 ^ 1022 by decide +kernel]
  push_cast
  norm_num

theorem sound_upper' {up : Bool} {c : Library.Numerics.Bounds.Checked} {x : ℝ}
    (h : LeanExe.ProofKit.F64Outward.Sound up (checkedWord c) x) (hu : up = true) :
    x ≤ real c.value := by
  subst hu
  exact h.2.2

theorem sound_lower' {up : Bool} {c : Library.Numerics.Bounds.Checked} {x : ℝ}
    (h : LeanExe.ProofKit.F64Outward.Sound up (checkedWord c) x) (hu : up = false) :
    real c.value ≤ x := by
  subst hu
  exact h.2.2

/-- The lower bound on the kinetic energy is at most `(mx² + my²) / (2ρ)`. -/
theorem kineticLower_le {rho mx my : Float} (h : (kineticLower rho mx my).status = 0)
    (hrho : 0 < real rho) :
    real (kineticLower rho mx my).value ≤ (real mx ^ 2 + real my ^ 2) / (2 * real rho) := by
  unfold kineticLower at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hxx, hyy⟩, hsum⟩, hhalf⟩, hk⟩ := hc
  have bxx := sound_lower' (outMul_accepted hxx).2.2 rfl
  have byy := sound_lower' (outMul_accepted hyy).2.2 rfl
  have bsum := sound_lower' (outAdd_accepted hsum).2.2 rfl
  have bhalf := sound_lower' (outMul_accepted hhalf).2.2 rfl
  have bk := sound_lower' (outDiv_accepted hk).2.2.2 rfl
  simp only [real] at *
  rw [show value (0.5 : Float).toBits = 1 / 2 from real_half] at bhalf
  calc value (Library.Numerics.Bounds.outDiv false (Library.Numerics.Bounds.outMul false 0.5 (Library.Numerics.Bounds.outAdd false (Library.Numerics.Bounds.outMul false mx mx).value
        (Library.Numerics.Bounds.outMul false my my).value).value).value rho).value.toBits
      ≤ value (Library.Numerics.Bounds.outMul false 0.5 (Library.Numerics.Bounds.outAdd false (Library.Numerics.Bounds.outMul false mx mx).value
        (Library.Numerics.Bounds.outMul false my my).value).value).value.toBits / value rho.toBits := bk
    _ ≤ (value mx.toBits ^ 2 + value my.toBits ^ 2) / (2 * value rho.toBits) := by
      rw [div_le_div_iff₀ hrho (by positivity)]
      nlinarith

/-- The internal energy `E - (mx² + my²) / (2ρ)` of a state, in exact arithmetic. -/
noncomputable abbrev internalEnergy (rho mx my energy : ℝ) : ℝ :=
  energy - (mx ^ 2 + my ^ 2) / (2 * rho)

/-- The signal speed `|u| + c` in the direction of `mx` of a state, in exact arithmetic with
γ = 7/5, where the square root of a negative number is 0. -/
noncomputable def physicalSpeed (rho mx my energy : ℝ) : ℝ :=
  |mx| / rho + Real.sqrt (7 / 5 * (2 / 5 * internalEnergy rho mx my energy) / rho)

theorem pressureUpper_ge {rho mx my energy : Float} (h : (pressureUpper rho mx my energy).status = 0)
    (hrho : 0 < real rho)
    (hE : 0 ≤ internalEnergy (real rho) (real mx) (real my) (real energy)) :
    2 / 5 * internalEnergy (real rho) (real mx) (real my) (real energy) ≤
      real (pressureUpper rho mx my energy).value := by
  unfold pressureUpper at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hk, hi⟩, hp⟩ := hc
  have bk := kineticLower_le hk hrho
  have bi := sound_upper' (outSub_accepted hi).2.2 rfl
  have bp := sound_upper' (outMul_accepted hp).2.2 rfl
  have c04 := real_twoFifths
  simp only [real, internalEnergy] at *
  have hint : value energy.toBits - (value mx.toBits ^ 2 + value my.toBits ^ 2) /
      (2 * value rho.toBits) ≤ value (Library.Numerics.Bounds.outSub true energy (kineticLower rho mx my).value).value.toBits :=
    le_trans (by linarith) bi
  nlinarith

theorem soundUpper_ge {rho mx my energy : Float} (h : (soundUpper rho mx my energy).status = 0)
    (hrho : 0 < real rho) :
    Real.sqrt (7 / 5 * (2 / 5 * internalEnergy (real rho) (real mx) (real my) (real energy)) /
      real rho) ≤ real (soundUpper rho mx my energy).value := by
  unfold soundUpper at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hp, hr⟩, hq⟩, hs⟩ := hc
  have br := sound_upper' (outDiv_accepted hr).2.2.2 rfl
  have bq := sound_upper' (outMul_accepted hq).2.2 rfl
  have bs := sound_upper' (outSqrt_accepted hs).2.2 rfl
  have c14 := real_gammaUp
  simp only [real] at *
  set P := 2 / 5 * internalEnergy (value rho.toBits) (value mx.toBits) (value my.toBits)
    (value energy.toBits)
  by_cases hE : 0 ≤ internalEnergy (value rho.toBits) (value mx.toBits) (value my.toBits)
    (value energy.toBits)
  · have bp : P ≤ value (pressureUpper rho mx my energy).value.toBits := pressureUpper_ge hp hrho hE
    have hP : 0 ≤ P := by positivity
    have hratio : P / value rho.toBits ≤ value (Library.Numerics.Bounds.outDiv true (pressureUpper rho mx my energy).value
        rho).value.toBits :=
      le_trans (div_le_div_of_nonneg_right bp hrho.le) br
    have hrad : 7 / 5 * P / value rho.toBits ≤ value (Library.Numerics.Bounds.outMul true 1.4000000000000001
        (Library.Numerics.Bounds.outDiv true (pressureUpper rho mx my energy).value rho).value).value.toBits := by
      have h0 : 0 ≤ P / value rho.toBits := div_nonneg hP hrho.le
      rw [mul_div_assoc]
      nlinarith
    exact le_trans (Real.sqrt_le_sqrt hrad) bs
  · have hneg : 7 / 5 * P / value rho.toBits ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hrho.le
      have : P < 0 := by simp only [P]; linarith
      linarith
    rw [Real.sqrt_eq_zero'.mpr hneg]
    exact le_trans (Real.sqrt_nonneg _) bs

/-- An accepted outward speed bound is at least the exact signal speed, and the density is
positive. -/
theorem speedUpper_ge {rho mx my energy : Float} (h : (speedUpper rho mx my energy).status = 0) :
    0 < real rho ∧ physicalSpeed (real rho) (real mx) (real my) (real energy) ≤
      real (speedUpper rho mx my energy).value := by
  have hpos := speedUpper_ok h
  have hrho : 0 < real rho := by
    have := (F64Order.positiveBits_spec rho.toBits (by simpa [positive,
      F64Order.positiveBits] using hpos)).2
    simpa [real] using this
  refine ⟨hrho, ?_⟩
  unfold speedUpper at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨-, hv⟩, hs⟩, ha⟩ := hc
  have bv := sound_upper' (outDiv_accepted hv).2.2.2 rfl
  have bs := soundUpper_ge hs hrho
  have ba := sound_upper' (outAdd_accepted ha).2.2 rfl
  rw [toBits_ofBits_abs] at bv
  have habs : value (mx.toBits &&& 0x7FFFFFFFFFFFFFFF) = |value mx.toBits| :=
    F64Order.absBits_value mx.toBits
  rw [habs] at bv
  simp only [real, physicalSpeed] at *
  linarith

/-! The sign of an accepted speed bound. -/

/-- Finite words whose scaled values sum to 0 add to a word whose scaled value is 0. -/
theorem add_zero_sum {a b : UInt64} (ha : Finite a) (hb : Finite b)
    (hz : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = 0 := by
  have hna := CodeLib.IEEE64.not_nan_of_finite ha
  have hnb := CodeLib.IEEE64.not_nan_of_finite hb
  have hia := CodeLib.IEEE64.not_infinite_of_finite ha
  have hib := CodeLib.IEEE64.not_infinite_of_finite hb
  simp [Wasm.IEEE64.add, hna, hnb, hia, hib, hz]
  split <;> decide

set_option maxRecDepth 8192 in
/-- A word of nonnegative value other than negative zero has sign bit 0. -/
theorem word_lt_of_value_nonneg {w : UInt64} (hw : 0 ≤ value w) (hz : w ≠ 0x8000000000000000) :
    w.toNat < 2 ^ 63 := by
  by_contra hlt
  have hge : 2 ^ 63 ≤ w.toNat := by omega
  have hne : w.toNat ≠ 2 ^ 63 := fun h => hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hv := F64Adjacent.negative_word_value w hge
  have hpos : 0 < F64Order.unsignedScaled (w.toNat - 2 ^ 63) := by
    have hm : 0 < w.toNat - 2 ^ 63 := by omega
    generalize w.toNat - 2 ^ 63 = m at hm
    unfold F64Order.unsignedScaled
    split
    · rename_i h0
      have : m < 2 ^ 52 := by
        rcases Nat.div_eq_zero_iff.mp h0 with h | h
        · exact absurd h (by positivity)
        · exact h
      rw [Nat.mod_eq_of_lt this]
      exact hm
    · positivity
  have : value w < 0 := by
    rw [hv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    simp only [neg_neg_iff_pos]  
    exact_mod_cast hpos
  linarith

/-- An accepted upward sum is the successor of the rounded sum, which is finite. -/
theorem outAdd_up_value {a b : Float} (h : (Library.Numerics.Bounds.outAdd true a b).status = 0) :
    Finite (Wasm.IEEE64.add a.toBits b.toBits) ∧
      (Library.Numerics.Bounds.outAdd true a b).value.toBits = F64Adjacent.nextUp (Wasm.IEEE64.add a.toBits b.toBits) := by
  have hw := outAdd_word true a b
  have hs : (F64Outward.add true a.toBits b.toBits).status = 0 := by rw [← hw]; exact h
  have hv : (Library.Numerics.Bounds.outAdd true a b).value.toBits = (F64Outward.add true a.toBits b.toBits).value := by
    rw [← hw]; rfl
  rw [hv]
  unfold F64Outward.add F64Outward.endpoint F64Outward.neighbor at hs ⊢
  split_ifs at hs ⊢ with h1 h2 h3 <;> simp_all [F64Outward.rejected]
  refine ⟨(F64Order.finiteBits_iff _).mp h2, ?_⟩
  by_cases h3 : F64Order.finiteBits (F64Adjacent.nextUp (Wasm.IEEE64.add a.toBits b.toBits)) = true
  · simp [h3]
  · simp [h3] at hs

set_option maxRecDepth 8192 in
/-- An accepted speed bound has sign bit 0. -/
theorem speedUpper_word {rho mx my energy : Float} (h : (speedUpper rho mx my energy).status = 0) :
    (speedUpper rho mx my energy).value.toBits.toNat < 2 ^ 63 := by
  obtain ⟨hrho, hphys⟩ := speedUpper_ge h
  unfold speedUpper at h hphys ⊢
  dsimp only at h hphys ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc] at hphys ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨-, hv⟩, hs⟩, ha⟩ := hc
  set v := Library.Numerics.Bounds.outDiv true (Float.ofBits (Library.Numerics.Bounds.absBits mx.toBits)) rho
  set c := soundUpper rho mx my energy
  have bv := sound_upper' (outDiv_accepted hv).2.2.2 rfl
  rw [toBits_ofBits_abs, show value (mx.toBits &&& 0x7FFFFFFFFFFFFFFF) = |value mx.toBits| from
    F64Order.absBits_value mx.toBits] at bv
  have bc := soundUpper_ge hs hrho
  have hv0 : 0 ≤ value v.value.toBits :=
    le_trans (div_nonneg (abs_nonneg _) hrho.le) bv
  have hc0 : 0 ≤ value c.value.toBits := le_trans (Real.sqrt_nonneg _) bc
  obtain ⟨hfin, hval⟩ := outAdd_up_value ha
  have hge := sound_upper' (outAdd_accepted ha).2.2 rfl
  simp only [real] at hge
  refine word_lt_of_value_nonneg (le_trans (add_nonneg hv0 hc0) hge) fun hz => ?_
  rw [hval] at hz
  set r := Wasm.IEEE64.add v.value.toBits c.value.toBits
  have hr : r = 0x8000000000000001 := by
    unfold F64Adjacent.nextUp at hz
    have hrf := hfin
    rw [← F64Order.finiteBits_iff] at hrf
    split_ifs at hz with h1 h2
    · simp at hz
    · have : r = 0x7FFFFFFFFFFFFFFF := by
        apply UInt64.toNat_inj.mp
        have := congrArg UInt64.toNat hz
        have hlt := UInt64.lt_iff_toNat_lt.mp h2
        simp at hlt this ⊢
        omega
      rw [this] at hrf
      exact absurd hrf (by decide)
    · apply UInt64.toNat_inj.mp
      have := congrArg UInt64.toNat hz
      have hnl : ¬r.toNat < 2 ^ 63 := fun h' => h2 (UInt64.lt_iff_toNat_lt.mpr (by simpa using h'))
      have hle : (1 : UInt64) ≤ r := UInt64.le_iff_toNat_le.mpr (by simp; omega)
      rw [UInt64.toNat_sub_of_le _ _ hle] at this
      simp at this ⊢
      omega
  have henc := (F64Adjacent.add_enclosure v.value.toBits c.value.toBits
    (outAdd_accepted ha).1 (outAdd_accepted ha).2.1 hfin).2
  rw [hz, show value 0x8000000000000000 = 0 by
    simp [value, show Wasm.IEEE64.scaledValue 0x8000000000000000 = 0 by decide +kernel]] at henc
  have hsum : value v.value.toBits + value c.value.toBits = 0 := by linarith
  have hscaled : Wasm.IEEE64.scaledValue v.value.toBits +
      Wasm.IEEE64.scaledValue c.value.toBits = 0 := by
    have : ((Wasm.IEEE64.scaledValue v.value.toBits + Wasm.IEEE64.scaledValue c.value.toBits : ℤ) : ℝ)
        = 0 := by
      simp only [value] at hsum
      push_cast
      field_simp at hsum
      linarith
    exact_mod_cast this
  have h0 := add_zero_sum (outAdd_accepted ha).1 (outAdd_accepted ha).2.1 hscaled
  rw [show Wasm.IEEE64.add v.value.toBits c.value.toBits = r from rfl, hr] at h0
  exact absurd h0 (by decide)

end Demos.Euler
