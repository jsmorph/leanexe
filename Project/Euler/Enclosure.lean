import Project.Euler.ReconstructedSpec
import Project.Euler.Outward
import Project.ProofKit.F64OutwardAccepted

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

end Project.Euler
