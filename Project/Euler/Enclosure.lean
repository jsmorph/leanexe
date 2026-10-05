import Project.Euler.ReconstructedSpec
import Project.Euler.Outward
import Project.ProofKit.F64OutwardAccepted
import Project.ProofKit.F64AdjacentSigned
import Project.ProofKit.F64DyadicBounds
import Project.ProofKit.F64Convert

/-! Real-number bounds for the reconstructed Euler solver: its outward operations agree with
the word-level outward operations of `Project.ProofKit.F64Outward`, whose results bound the exact
result from above or below. -/

namespace Project.Euler

open LeanExe.Examples.Euler Project.ProofKit

set_option exponentiation.threshold 4096

/-- A checked value as a word-level checked value. -/
def checkedWord (c : Checked) : Project.ProofKit.F64Outward.Checked := ⟨c.status, c.value.toBits⟩

theorem endpoint_word (up : Bool) (r : Float) :
    checkedWord (endpoint up r) = Project.ProofKit.F64Outward.endpoint up r.toBits := by
  have hn : (if up then nextUpBits r.toBits else nextDownBits r.toBits) =
      Project.ProofKit.F64Outward.neighbor up r.toBits := by
    cases up <;> simp [nextUpBits, nextDownBits, Project.ProofKit.F64Outward.neighbor,
      Project.ProofKit.F64Adjacent.nextUp, Project.ProofKit.F64Adjacent.nextDown]
  unfold endpoint Project.ProofKit.F64Outward.endpoint
  dsimp only
  rw [hn]
  generalize Project.ProofKit.F64Outward.neighbor up r.toBits = b
  by_cases h1 : r.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    by_cases h2 : b &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    simp [h1, h2, finite, absBits, Project.ProofKit.F64Order.finiteBits,
      Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
      Project.ProofKit.F64Outward.rejected, zero_toBits]
  exact toBits_ofBits_of_finite h2

open CodeLib.IEEE64 (value Finite)

theorem endpoint_rejected {up : Bool} {r : Float} (h : ¬(endpoint up r).status = 0) :
    endpoint up r = rejectedChecked := by
  unfold endpoint at h ⊢
  dsimp only at h ⊢
  generalize (if up then nextUpBits r.toBits else nextDownBits r.toBits) = w at h ⊢
  by_cases hc : (finite r && decide (absBits w < 0x7FF0000000000000)) = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ite_false]

theorem outAdd_word (up : Bool) (a b : Float) :
    checkedWord (outAdd up a b) = Project.ProofKit.F64Outward.add up a.toBits b.toBits := by
  unfold outAdd Project.ProofKit.F64Outward.add
  dsimp only
  rw [← F64Bits.toBits_add, ← endpoint_word]
  by_cases he : (endpoint up (a + b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outAdd_accepted {up : Bool} {a b : Float} (h : (outAdd up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outAdd up a b)) (value a.toBits + value b.toBits) := by
  have := Project.ProofKit.F64Outward.add_accepted up a.toBits b.toBits
    (by rw [← outAdd_word]; exact h)
  rwa [← outAdd_word] at this

theorem outSub_word (up : Bool) (a b : Float) :
    checkedWord (outSub up a b) = Project.ProofKit.F64Outward.sub up a.toBits b.toBits := by
  unfold outSub Project.ProofKit.F64Outward.sub
  dsimp only
  rw [← F64Bits.toBits_sub, ← endpoint_word]
  by_cases he : (endpoint up (a - b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSub_accepted {up : Bool} {a b : Float} (h : (outSub up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outSub up a b)) (value a.toBits - value b.toBits) := by
  have := Project.ProofKit.F64Outward.sub_accepted up a.toBits b.toBits
    (by rw [← outSub_word]; exact h)
  rwa [← outSub_word] at this

theorem outMul_word (up : Bool) (a b : Float) :
    checkedWord (outMul up a b) = Project.ProofKit.F64Outward.mul up a.toBits b.toBits := by
  unfold outMul Project.ProofKit.F64Outward.mul
  dsimp only
  rw [← F64Bits.toBits_mul, ← endpoint_word]
  by_cases he : (endpoint up (a * b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outMul_accepted {up : Bool} {a b : Float} (h : (outMul up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outMul up a b)) (value a.toBits * value b.toBits) := by
  have := Project.ProofKit.F64Outward.mul_accepted up a.toBits b.toBits
    (by rw [← outMul_word]; exact h)
  rwa [← outMul_word] at this

theorem outDiv_word (up : Bool) (a b : Float) :
    checkedWord (outDiv up a b) = Project.ProofKit.F64Outward.div up a.toBits b.toBits := by
  unfold outDiv Project.ProofKit.F64Outward.div
  dsimp only
  rw [← F64Bits.toBits_div, ← endpoint_word]
  by_cases he : (endpoint up (a / b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hz : 0 < b.toBits &&& 0x7FFFFFFFFFFFFFFF <;>
      simp [ha, hb, hz, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outDiv_accepted {up : Bool} {a b : Float} (h : (outDiv up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧ Wasm.IEEE64.scaledMagnitude b.toBits ≠ 0 ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outDiv up a b))
        (value a.toBits / value b.toBits) := by
  have := Project.ProofKit.F64Outward.div_accepted up a.toBits b.toBits
    (by rw [← outDiv_word]; exact h)
  rwa [← outDiv_word] at this

theorem outSqrt_word (up : Bool) (a : Float) :
    checkedWord (outSqrt up a) = Project.ProofKit.F64Outward.sqrt up a.toBits := by
  unfold outSqrt Project.ProofKit.F64Outward.sqrt
  dsimp only
  rw [← F64Bits.toBits_sqrt, ← endpoint_word]
  by_cases he : (endpoint up a.sqrt).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hs : a.toBits ≤ 0x8000000000000000 <;>
      simp [ha, hs, he, finite, absBits, Project.ProofKit.F64Order.finiteBits,
        Project.ProofKit.F64Order.absBits, checkedWord, rejectedChecked,
        Project.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, rejectedChecked, Project.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSqrt_accepted {up : Bool} {a : Float} (h : (outSqrt up a).status = 0) :
    Finite a.toBits ∧ 0 ≤ value a.toBits ∧
      Project.ProofKit.F64Outward.Sound up (checkedWord (outSqrt up a))
        (Real.sqrt (value a.toBits)) := by
  have := Project.ProofKit.F64Outward.sqrt_accepted up a.toBits (by rw [← outSqrt_word]; exact h)
  rwa [← outSqrt_word] at this

/-- The real value of a float's bits. -/
noncomputable abbrev real (x : Float) : ℝ := value x.toBits

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

/-- A selection between a checked value and `rejectedChecked` with status 0 selects the value. -/
theorem rejectedChecked_status {c : Prop} [Decidable c] {u : Checked}
    (h : (if c then u else rejectedChecked).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

theorem sound_upper' {up : Bool} {c : Checked} {x : ℝ}
    (h : Project.ProofKit.F64Outward.Sound up (checkedWord c) x) (hu : up = true) :
    x ≤ real c.value := by
  subst hu
  exact h.2.2

theorem sound_lower' {up : Bool} {c : Checked} {x : ℝ}
    (h : Project.ProofKit.F64Outward.Sound up (checkedWord c) x) (hu : up = false) :
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
  calc value (outDiv false (outMul false 0.5 (outAdd false (outMul false mx mx).value
        (outMul false my my).value).value).value rho).value.toBits
      ≤ value (outMul false 0.5 (outAdd false (outMul false mx mx).value
        (outMul false my my).value).value).value.toBits / value rho.toBits := bk
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
      (2 * value rho.toBits) ≤ value (outSub true energy (kineticLower rho mx my).value).value.toBits :=
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
    have hratio : P / value rho.toBits ≤ value (outDiv true (pressureUpper rho mx my energy).value
        rho).value.toBits :=
      le_trans (div_le_div_of_nonneg_right bp hrho.le) br
    have hrad : 7 / 5 * P / value rho.toBits ≤ value (outMul true 1.4000000000000001
        (outDiv true (pressureUpper rho mx my energy).value rho).value).value.toBits := by
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
theorem outAdd_up_value {a b : Float} (h : (outAdd true a b).status = 0) :
    Finite (Wasm.IEEE64.add a.toBits b.toBits) ∧
      (outAdd true a b).value.toBits = F64Adjacent.nextUp (Wasm.IEEE64.add a.toBits b.toBits) := by
  have hw := outAdd_word true a b
  have hs : (F64Outward.add true a.toBits b.toBits).status = 0 := by rw [← hw]; exact h
  have hv : (outAdd true a b).value.toBits = (F64Outward.add true a.toBits b.toBits).value := by
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
  set v := outDiv true (Float.ofBits (absBits mx.toBits)) rho
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

/-! The CFL bound of an accepted timestep. -/

theorem absBits_of_word {w : UInt64} (hw : w.toNat < 2 ^ 63) : F64Order.absBits w = w := by
  apply UInt64.toNat_inj.mp
  rw [F64Order.absBits, UInt64.toNat_and,
    show (0x7FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hw]

theorem value_nonneg_of_word {w : UInt64} (hw : w.toNat < 2 ^ 63) : 0 ≤ value w := by
  rw [F64Adjacent.unsigned_word_value w hw]
  positivity

/-- On words with sign bit 0, word order implies real order. -/
theorem value_le_of_word {a b : UInt64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : a ≤ b) : value a ≤ value b := by
  have := F64Order.abs_value_mono a b (by rwa [absBits_of_word ha, absBits_of_word hb])
  rwa [abs_of_nonneg (value_nonneg_of_word ha), abs_of_nonneg (value_nonneg_of_word hb)] at this

/-- The larger of two floats in word order. -/
abbrev wordMax (a b : Float) : Float := if a.toBits ≤ b.toBits then b else a

theorem wordMax_ge {a b : Float} (ha : a.toBits.toNat < 2 ^ 63) (hb : b.toBits.toNat < 2 ^ 63) :
    (wordMax a b).toBits.toNat < 2 ^ 63 ∧ real a ≤ real (wordMax a b) ∧
      real b ≤ real (wordMax a b) := by
  by_cases hle : a.toBits ≤ b.toBits
  · simp only [wordMax, hle, ite_true]
    exact ⟨hb, value_le_of_word ha hb hle, le_rfl⟩
  · simp only [wordMax, hle, ite_false]
    refine ⟨ha, le_rfl, value_le_of_word hb ha ?_⟩
    rw [UInt64.le_iff_toNat_le] at hle ⊢
    omega

theorem real_pos_of_positive {x : Float} (h : 0 < x.toBits ∧ x.toBits < 0x7FF0000000000000) :
    0 < real x :=
  (F64Order.positiveBits_spec x.toBits (by simpa [F64Order.positiveBits] using h)).2

/-- The density of `q` is positive, and `s` bounds its signal speed in both directions. -/
def SpeedBound (q : Conserved) (s : ℝ) : Prop :=
  0 < real q.density ∧
    physicalSpeed (real q.density) (real q.mx) (real q.my) (real q.energy) ≤ s ∧
    physicalSpeed (real q.density) (real q.my) (real q.mx) (real q.energy) ≤ s

theorem SpeedBound.mono {q : Conserved} {s t : ℝ} (h : SpeedBound q s) (hst : s ≤ t) :
    SpeedBound q t :=
  ⟨h.1, h.2.1.trans hst, h.2.2.trans hst⟩

/-- An accepted cell bound has sign bit 0 and bounds the signal speed in both directions. -/
theorem cellUpper_ge {q : Conserved} (h : (cellUpper q.density q.mx q.my q.energy).status = 0) :
    (cellUpper q.density q.mx q.my q.energy).value.toBits.toNat < 2 ^ 63 ∧
      SpeedBound q (real (cellUpper q.density q.mx q.my q.energy).value) := by
  unfold cellUpper mergeChecked at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hx, hy⟩ := hc
  obtain ⟨hrho, bx⟩ := speedUpper_ge hx
  obtain ⟨-, byy⟩ := speedUpper_ge hy
  obtain ⟨w, hxm, hym⟩ := wordMax_ge (speedUpper_word hx) (speedUpper_word hy)
  exact ⟨w, hrho, bx.trans hxm, byy.trans hym⟩

/-- A property of `LeanExe.loop`'s state that holds at index 0, and that each step below `k`
carries from index `i` to `i + 1`, holds at every index up to `k`. -/
theorem loop_inv {P : Nat → α → Prop} {f : UInt64 → α → α} {init : α} {k : Nat}
    (h0 : P 0 init) (hStep : ∀ i < k, ∀ a, P i a → P (i + 1) (f (UInt64.ofNat i) a)) :
    ∀ m ≤ k, P m (Nat.fold m (fun i _ a => f (UInt64.ofNat i) a) init) := by
  intro m hm
  induction m with
  | zero => exact h0
  | succ m ih =>
    rw [Nat.fold_succ]
    exact hStep m (by omega) _ (ih (by omega))

/-- `gridUpper` with its loop's step named. -/
theorem gridUpper_loop (grid : Array Cell) :
    ∃ f : UInt64 → UInt64 × Float → UInt64 × Float,
      (∀ i acc, f i acc =
        (if acc.1 == 0 && (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
            grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).status == 0 then 0 else 1,
          if acc.1 == 0 && (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
              grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).status == 0 then
            wordMax acc.2 (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
              grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).value
          else 0)) ∧
      gridUpper grid =
        match LeanExe.loop grid.size.toUInt64 ((0 : UInt64), (0 : Float)) f with
        | (status, value) => ⟨status, value⟩ :=
  ⟨_, fun _ _ => rfl, rfl⟩

/-- An accepted grid bound has sign bit 0 and bounds the signal speed of every cell. -/
theorem gridUpper_ge {grid : Array Cell} (h : (gridUpper grid).status = 0)
    (hSize : grid.size < 2 ^ 64) :
    (gridUpper grid).value.toBits.toNat < 2 ^ 63 ∧
      ∀ i (hi : i < grid.size), SpeedBound grid[i].state (real (gridUpper grid).value) := by
  have hk : grid.size.toUInt64.toNat = grid.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hSize]
  obtain ⟨f, hf, hDef⟩ := gridUpper_loop grid
  have hInv := loop_inv (P := fun m (acc : UInt64 × Float) => acc.1 = 0 →
      acc.2.toBits.toNat < 2 ^ 63 ∧
        ∀ i (hi : i < grid.size), i < m → SpeedBound grid[i].state (real acc.2))
    (f := f) (init := ((0 : UInt64), (0 : Float))) (k := grid.size.toUInt64.toNat)
    (fun _ => ⟨by rw [zero_bits]; decide, fun _ _ hm => absurd hm (Nat.not_lt_zero _)⟩)
    (fun i hi acc hacc => by
      rw [hf]
      have hig : i < grid.size := by omega
      have hi' : (UInt64.ofNat i).toNat = i :=
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
      simp only [hi', getElem!_pos grid i hig]
      intro h0
      by_cases hs : acc.1 = 0 ∧
          (cellUpper grid[i].state.density grid[i].state.mx grid[i].state.my
            grid[i].state.energy).status = 0
      · obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, hs2, beq_self_eq_true, Bool.and_self, ite_true]
        obtain ⟨wa, ba⟩ := hacc hs1
        obtain ⟨wc, bc⟩ := cellUpper_ge hs2
        obtain ⟨w, ham, hcm⟩ := wordMax_ge wa wc
        refine ⟨w, fun j hj hji => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
        · exact (ba j hj hji).mono ham
        · exact bc.mono hcm
      · simp only [Bool.and_eq_true, beq_iff_eq] at h0
        rw [ite_eq_right hs] at h0
        exact absurd h0 (by decide))
    grid.size.toUInt64.toNat le_rfl
  rw [hDef] at h ⊢
  unfold LeanExe.loop at h ⊢
  generalize Nat.fold grid.size.toUInt64.toNat _ ((0 : UInt64), (0 : Float)) = R at h hInv ⊢
  obtain ⟨status, value⟩ := R
  obtain ⟨w, hB⟩ := hInv h
  exact ⟨w, fun i hi => hB i hi (by omega)⟩

/-- Converting a word below `2^53` to binary64 is exact. -/
theorem real_toFloat {n : UInt64} (hn : n.toNat < 2 ^ 53) : real n.toFloat = n.toNat := by
  have hr : CodeLib.IEEE64.roundedMagnitude (n.toNat * 2 ^ 1074) = n.toNat * 2 ^ 1074 := by
    by_cases hz : n.toNat = 0
    · rw [hz, Nat.zero_mul]
      exact CodeLib.IEEE64.roundedMagnitude_eq_self (by norm_num)
    · have hL1 : 2 ^ Nat.log2 n.toNat ≤ n.toNat := Nat.log2_self_le hz
      have hL2 : n.toNat < 2 ^ (Nat.log2 n.toNat + 1) := Nat.lt_log2_self
      have hL : Nat.log2 n.toNat ≤ 52 := by
        by_contra hc
        have : 2 ^ 53 ≤ 2 ^ Nat.log2 n.toNat := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hsplit : n.toNat * 2 ^ 1074 =
          n.toNat * 2 ^ (52 - Nat.log2 n.toNat) * 2 ^ (1022 + Nat.log2 n.toNat) := by
        rw [Nat.mul_assoc, ← pow_add]
        congr 2
        omega
      rw [hsplit]
      apply F64DyadicBounds.roundedMagnitude_shifted
      · calc 2 ^ 52 = 2 ^ Nat.log2 n.toNat * 2 ^ (52 - Nat.log2 n.toNat) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ n.toNat * 2 ^ (52 - Nat.log2 n.toNat) := Nat.mul_le_mul_right _ hL1
      · calc n.toNat * 2 ^ (52 - Nat.log2 n.toNat)
            ≤ 2 ^ (Nat.log2 n.toNat + 1) * 2 ^ (52 - Nat.log2 n.toNat) :=
              Nat.mul_le_mul_right _ hL2.le
          _ = 2 ^ 53 := by rw [← pow_add]; congr 1; omega
  have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.convertI64U n) = (n.toNat * 2 ^ 1074 : Nat) := by
    show Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude false (n.toNat * 2 ^ 1074)) = _
    rw [F64Packing.scaledValue_pack false _ (by
      calc n.toNat * 2 ^ 1074 < 2 ^ 53 * 2 ^ 1074 :=
            Nat.mul_lt_mul_of_pos_right hn (by positivity)
        _ ≤ 2 ^ 2097 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega))]
    simp only [Bool.false_eq_true, ite_false, hr]
  rw [real, F64Convert.toBits_toFloat, value, hv, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, mul_div_assoc, div_self (by positivity), mul_one]

/-- An accepted ratio bounds `dt · n` from above, and its product with `alpha` is at most 1/2. -/
theorem gridRatio_le {n : UInt64} {dt alpha : Float} (h : (gridRatio n dt alpha).status = 0) :
    0 < real dt ∧ 0 < real alpha ∧ real dt * n.toNat ≤ real (gridRatio n dt alpha).value ∧
      real (gridRatio n dt alpha).value * real alpha ≤ 1 / 2 := by
  unfold gridRatio at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h2, h800⟩, hsp⟩, hdt⟩, hspp⟩, hal⟩, hr⟩, hco⟩, hle⟩ := hc
  have hn2 : 2 ≤ n.toNat := UInt64.le_iff_toNat_le.mp h2
  have hn800 : n.toNat ≤ 800 := UInt64.le_iff_toNat_le.mp h800
  have hnreal := real_toFloat (n := n) (by omega)
  have bsp := sound_lower' (outDiv_accepted hsp).2.2.2 rfl
  have br := sound_upper' (outDiv_accepted hr).2.2.2 rfl
  have bco := sound_upper' (outMul_accepted hco).2.2 rfl
  have hdt' := real_pos_of_positive hdt
  have hsp' := real_pos_of_positive hspp
  have hal' := real_pos_of_positive hal
  have hcourant := value_le_of_word (b := 0x3FE0000000000000)
    (by have := UInt64.le_iff_toNat_le.mp hle; simp at this; omega) (by decide) hle
  rw [← half_toBits, show value (0.5 : Float).toBits = 1 / 2 from real_half] at hcourant
  have hone : value (1 : Float).toBits = 1 := by
    rw [one_toBits, value, show Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 by
      decide +kernel, Int.cast_pow, Int.cast_ofNat, div_self (by positivity)]
  simp only [real] at *
  rw [hone, hnreal] at bsp
  have hnpos : (0 : ℝ) < n.toNat := by exact_mod_cast (by omega : 0 < n.toNat)
  refine ⟨hdt', hal', ?_, le_trans bco hcourant⟩
  refine le_trans ?_ br
  rw [le_div_iff₀ hsp']
  have : value (outDiv false 1 n.toFloat).value.toBits * n.toNat ≤ 1 := by
    rwa [le_div_iff₀ hnpos] at bsp
  nlinarith

/-- `reconstructedAttempt` returns status 0 only with the grid that `reconstructedStepGrid`
computes with an accepted ratio for its timestep. -/
theorem reconstructedAttempt_ratio {n trials : UInt64} {time alpha : Float} {grid : Array Cell}
    {dt : Float} {old : Array Cell}
    (h : (reconstructedAttempt n trials time alpha grid dt old).1 = 0) :
    (gridRatio n (reconstructedAttempt n trials time alpha grid dt old).2.1 alpha).status = 0 ∧
      (reconstructedAttempt n trials time alpha grid dt old).2.2 = reconstructedStepGrid n trials
        (gridRatio n (reconstructedAttempt n trials time alpha grid dt old).2.1 alpha).value
        grid := by
  unfold reconstructedAttempt at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    split
    · rename_i hR
      rw [ite_eq_left hR] at h
      unfold reconstructedTry at h ⊢
      dsimp only at h ⊢
      split
      · exact ⟨by simpa using hR, rfl⟩
      · rename_i hA
        rw [ite_eq_right hA] at h
        simp at h
    · rename_i hR
      rw [ite_eq_right hR] at h
      simp at h
  · rename_i hV
    rw [ite_eq_right hV] at h
    simp at h

theorem reconstructedAdvanceWith_ratio {n trials : UInt64} {time dt alpha : Float}
    {grid : Array Cell} (h : (reconstructedAdvanceWith n trials time dt alpha grid).1 = 0) :
    ∃ dt' : Float, (gridRatio n dt' alpha).status = 0 ∧
      (reconstructedAdvanceWith n trials time dt alpha grid).2.1 = time + dt' ∧
      (reconstructedAdvanceWith n trials time dt alpha grid).2.2 =
        reconstructedStepGrid n trials (gridRatio n dt' alpha).value grid := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell => s.1 = 0 →
      (gridRatio n s.2.1 alpha).status = 0 ∧
        s.2.2 = reconstructedStepGrid n trials (gridRatio n s.2.1 alpha).value grid)
    (cond := cond) (step := step) (x0 := ((9 : UInt64), dt, (#[] : Array Cell))) 2048 (by simp)
    (fun x _ _ hx => by rw [hStepEq] at hx ⊢; exact reconstructedAttempt_ratio hx)
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step = R
    at h hInv ⊢
  obtain ⟨status, dt', trial⟩ := R
  dsimp only at h hInv ⊢
  split
  · rename_i hS
    obtain ⟨hr, ht⟩ := hInv (by simpa using hS)
    exact ⟨dt', hr, rfl, ht⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    split at h
    · simp at h
    · simp only at h
      exact absurd (by simp [h]) hS

/-- A timestep that advances the time by some `dt > 0` and updates the grid with a ratio
`r ≥ dt · n`, where `n` is the number of cells per side, such that `r` times the signal speed of
every cell in either direction is at most 1/2. -/
def CflStep (n trials : UInt64) (a b : Float × Array Cell) : Prop :=
  ∃ dt r : Float, 0 < real dt ∧ b.1 = a.1 + dt ∧ b.2 = reconstructedStepGrid n trials r a.2 ∧
    real dt * n.toNat ≤ real r ∧
    ∀ i (hi : i < a.2.size), 0 < real a.2[i].state.density ∧
      real r * physicalSpeed (real a.2[i].state.density) (real a.2[i].state.mx)
        (real a.2[i].state.my) (real a.2[i].state.energy) ≤ 1 / 2 ∧
      real r * physicalSpeed (real a.2[i].state.density) (real a.2[i].state.my)
        (real a.2[i].state.mx) (real a.2[i].state.energy) ≤ 1 / 2

/-- An accepted reconstructed timestep is a `CflStep`. -/
theorem reconstructedAdvanceStep_cfl {n trials : UInt64} {time : Float} {grid : Array Cell}
    (h : (reconstructedAdvanceStep n trials time grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    CflStep n trials (time, grid) ((reconstructedAdvanceStep n trials time grid).2.1,
      (reconstructedAdvanceStep n trials time grid).2.2) := by
  unfold CflStep
  unfold reconstructedAdvanceStep at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hS
    rw [ite_eq_left hS] at h
    obtain ⟨-, hB⟩ := gridUpper_ge (by simpa using hS) hSize
    obtain ⟨dt, hR, ht, hg⟩ := reconstructedAdvanceWith_ratio h
    obtain ⟨hdt, -, hdn, hra⟩ := gridRatio_le hR
    refine ⟨dt, _, hdt, ht, hg, hdn, fun i hi => ?_⟩
    obtain ⟨hrho, bx, byy⟩ := hB i hi
    have hr0 := le_trans (mul_nonneg hdt.le (Nat.cast_nonneg _)) hdn
    exact ⟨hrho, le_trans (mul_le_mul_of_nonneg_left bx hr0) hra,
      le_trans (mul_le_mul_of_nonneg_left byy hr0) hra⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    simp at h

/-- Every timestep of a reconstructed run that returns status 0 is a `CflStep`: a chain of them
leads from time 0 and the initial grid to the run's final time and grid. -/
theorem reconstructedRunFrom_cfl {n trials : UInt64} (h : (reconstructedRunFrom n trials).1 = 0) :
    Relation.ReflTransGen (CflStep n trials) (0, initialCells n)
      ((reconstructedRunFrom n trials).2.1, (reconstructedRunFrom n trials).2.2) := by
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = (n * n).toNat ∧
        (s.1 = 0 → Relation.ReflTransGen (CflStep n trials) (0, initialCells n) (s.2.1, s.2.2)))
    (cond := cond) (step := step) (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 ⟨initialCells_size n, fun _ => .refl⟩
    (fun x hc hx => by
      rw [hStepEq]
      have hc' : x.1 = 0 := by
        rw [hCondEq] at hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1
      have hs1 := hx.1
      refine ⟨(reconstructedAdvanceStep_size (by omega)).trans hs1, fun hs => ?_⟩
      exact (hx.2 hc').tail (reconstructedAdvanceStep_cfl hs (by omega)))
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
    step = R at h hInv ⊢
  obtain ⟨status, time, grid⟩ := R
  dsimp only at h hInv ⊢
  split at h
  · simp at h
  · rename_i hT
    rw [ite_eq_right hT]
    subst h
    exact hInv.2 rfl

theorem reconstructedRun_cfl {n trials : UInt64} (h : (reconstructedRun n trials).1 = 0) :
    Relation.ReflTransGen (CflStep n trials) (0, initialCells n)
      ((reconstructedRun n trials).2.1, (reconstructedRun n trials).2.2) := by
  unfold reconstructedRun at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    exact reconstructedRunFrom_cfl h
  · simp at h

end Project.Euler
