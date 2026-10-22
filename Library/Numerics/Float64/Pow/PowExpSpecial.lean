import Library.Numerics.Float64.Pow.PowExpPaths

/-!
The special paths of `Pow.powExp` with `signBias = 0`, for `512 ≤ |x| < 1024`.  Up to 768 the
reconstruction lies within `Library.Numerics.Float64.Exp.ArmTight.allowance` of its target, and `Library.Numerics.Float64.Exp.ArmTight.positive1009_tight`
or `Library.Numerics.Float64.Exp.ArmTight.negative_tight` gives one step against `exp L`.  Beyond 768 the residual stays
within `1/128` and the evaluation within `1/64`: for positive `x` the scale exceeds `2 ^ 98` and
the result is positive infinity, and `exp L` reaches `2 ^ 1024`; for negative `x` the scale is
below `2 ^ -85`, the compensated sum applies, and `exp L` is below `2 ^ -1100`.
-/

namespace Library.Numerics.Float64.Pow.PowExpSpecial
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude Library.Numerics.Float64.Exp.ExpSpecialNegative PowExpPaths

set_option exponentiation.threshold 4096

theorem scale_word (x : Float) :
    PowExpCore.scaleWord x = Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) := by
  rw [PowExpCore.scaleWord, Library.Numerics.Float64.Exp.ExpCoreBounds.floatShifted_bits]

/-- The positive special path, `512 ≤ x ≤ 768`. -/
theorem positive_within (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits) (hx : |value x.toBits| ≤ 768) (hxpos : 512 ≤ value x.toBits)
    (ht : |value xtail.toBits| ≤ 1 / 2 ^ 14)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 (Real.exp L)
      (Pow.powExpCore Exp.expTable x xtail 0 true).toBits := by
  obtain ⟨k, q, j, hkv, hk, hki, hj, hkn, _, hRt, htmf, htmb, htme⟩ :=
    PowExpCore.core_state x xtail L hxf htf hx ht hL
  have hq := Library.Numerics.Float64.Exp.ExpSpecialScale.positive_quotient x.toBits k q j hxf hx hxpos hkv hk
  have hqb := Library.Numerics.Float64.Exp.ExpSpecialScale.quotient_bounds k q j hk hkn
  have hk0 : ¬ k < 0 := by have := j.isLt; omega
  have hguard : Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits &&& 0x80000000 = 0 := by
    simpa only [ite_eq_right hk0] using
      Library.Numerics.Float64.Exp.ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  obtain ⟨hsf, hsv, _, _⟩ := Library.Numerics.Float64.Exp.ExpSpecialScale.positive_scale_value _ k q j hki hk hj hq (by omega)
  rw [PowExpCore.core_eq]
  simp only [ite_true]
  rw [scale_word, Library.Numerics.Float64.Exp.ExpCoreBounds.floatShifted_bits,
    positive_bits (PowExpCore.tmpFloat x xtail)
      (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits))
      (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) (by rw [hguard]; rfl) hsf]
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hRt
  have h := Library.Numerics.Float64.Exp.ArmTight.positive1009_tight _ _ q j _ hsf htmf hsv hq (by omega) htmb htme hρl hρu
  rwa [PowExpCore.target_eq L k q j hk] at h

/-- The negative special path, `-768 ≤ x ≤ -512`. -/
theorem negative_within (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits) (hx : |value x.toBits| ≤ 768) (hxneg : value x.toBits ≤ -512)
    (ht : |value xtail.toBits| ≤ 1 / 2 ^ 14)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 (Real.exp L)
      (Pow.powExpCore Exp.expTable x xtail 0 true).toBits := by
  obtain ⟨k, q, j, hkv, hk, hki, hj, hkn, _, hRt, htmf, htmb, htme⟩ :=
    PowExpCore.core_state x xtail L hxf htf hx ht hL
  have hq := Library.Numerics.Float64.Exp.ExpSpecialScale.negative_quotient x.toBits k q j hxf hx hxneg hkv hk
  have hqb := Library.Numerics.Float64.Exp.ExpSpecialScale.quotient_bounds k q j hk hkn
  have hkneg : k < 0 := by have := j.isLt; omega
  have hguard := Library.Numerics.Float64.Exp.ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  rw [ite_eq_left hkneg] at hguard
  have hg : ¬ (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits &&& 0x80000000 == 0) = true := by
    rw [hguard]
    decide
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    Library.Numerics.Float64.Exp.ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) hq
  set s := Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) with hsdef
  set w := (PowExpCore.tmpFloat x xtail).toBits
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hRt
  have hρ : |Real.exp (L - k * (Real.log 2 / 128)) - 1| ≤ 1 / 256 := by
    rw [abs_le]
    constructor <;> linarith
  have htb := (Library.Numerics.Float64.Exp.ExpTableBounds.entry_bounds j).2.2.2.2
  obtain ⟨hpf, hPm, _⟩ := Library.Numerics.Float64.Exp.ArmTight.presum_tight s w _ _ hsf htmf hslo (hshi.trans (by norm_num))
    htmb htme hρ htb
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hsum : |value s + value (Wasm.IEEE64.mul s w)| < (2 : ℝ) ^ 1023 := by
    have := abs_add_le (value s) (value (Wasm.IEEE64.mul s w))
    rw [abs_of_pos hS] at this
    have : (2 : ℝ) ^ 1000 + 2 ^ 1000 / 128 < 2 ^ 1023 := by norm_num
    linarith
  obtain ⟨hyf, hye⟩ := F64AddBounds.add_real_relative s _ hsf hpf hsum
  have hypos : 0 < value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have h1 := (abs_le.mp hye).1
    have h2 := (abs_le.mp hPm).1
    have h3 : |value s + value (Wasm.IEEE64.mul s w)| ≤ value s + value s / 128 := by
      have := abs_add_le (value s) (value (Wasm.IEEE64.mul s w))
      rw [abs_of_pos hS] at this
      linarith
    have h4 : unitRoundoff64 * |value s + value (Wasm.IEEE64.mul s w)| ≤
        1 / 2 ^ 53 * (value s + value s / 128) := by
      rw [hu]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  rw [PowExpCore.core_eq]
  simp only [ite_true]
  rw [scale_word, Library.Numerics.Float64.Exp.ExpCoreBounds.floatShifted_bits]
  have hsd : Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) +
      ((1022 : UInt64) <<< (52 : UInt64)) = s := rfl
  rw [negative_bits (PowExpCore.tmpFloat x xtail)
      (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits))
      (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) hg (by rw [hsd]; exact hsf)
      (by rw [hsd]; exact sign_of_pos _ hS) (by rw [hsd]; exact hyf) (by rw [hsd]; exact hypos),
    hsd]
  have h := Library.Numerics.Float64.Exp.ArmTight.negative_tight s w q j _ hsf htmf hsv (by omega) hq htmb htme hρl hρu
  rwa [PowExpCore.target_eq L k q j hk] at h

#print axioms scale_word
#print axioms positive_within
#print axioms negative_within

end Library.Numerics.Float64.Pow.PowExpSpecial
