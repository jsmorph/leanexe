import Library.Numerics.Float64.Pow.PowExpFar

/-!
`Pow.powExp` with `signBias = 0` within one step of `exp L`, for finite `x` and `xtail` with
`|xtail| ≤ 17 · 2 ^ -28 |x|` and a target `L` with `|x + xtail - L| ≤ |L| / 2 ^ 65`.  These are
the conditions that `pow` meets with `x + xtail` its product `y log x`.  Every path of `powExp`
is covered: `1 + x` below `2 ^ -54`, the ordinary reconstruction below 512, the special paths
below 1024, and the overflow and underflow products from 1024 on.
-/

namespace Library.Numerics.Float64.Pow.PowExpTheorem
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude Library.Numerics.Float64.Exp.ExpBranches F64ExponentBounds

set_option exponentiation.threshold 4096

theorem sign_shift_one (x : UInt64) : (x >>> 63 == 1) = Wasm.IEEE64.sign x := by
  have hlt := x.toNat_lt
  simp only [Wasm.IEEE64.sign]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h]
    apply beq_iff_eq.mpr
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight]
    change x.toNat >>> 63 = 1
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg UInt64.toNat heq
    rw [UInt64.toNat_shiftRight] at this
    change x.toNat >>> 63 = 1 at this
    rw [Nat.shiftRight_eq_div_pow] at this
    omega

theorem powExp_within (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ |L| / 2 ^ 65) :
    F64SignedRounding.WithinSteps 1 (Real.exp L) (Pow.powExp Exp.expTable x xtail 0).toBits := by
  set X := value x.toBits
  set T := value xtail.toBits
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  -- `|L|` against `|x|`
  have hLb : |L| ≤ (1 + 1 / 2 ^ 23) * |X| := by
    have h1 := abs_sub_abs_le_abs_sub L (X + T)
    have h2 : |X + T| ≤ |X| + |T| := abs_add_le X T
    rw [abs_sub_comm] at h1
    have h3 : |L| * (1 - 1 / 2 ^ 65) ≤ |X| * (1 + 17 / 2 ^ 28) := by nlinarith
    have hX := abs_nonneg X
    nlinarith
  have hLe : |X + T - L| ≤ (1 + 1 / 2 ^ 23) * |X| / 2 ^ 65 :=
    hL.trans (div_le_div_of_nonneg_right hLb (by positivity))
  rcases (show Wasm.IEEE64.exponent x.toBits < 969 ∨
      (969 ≤ Wasm.IEEE64.exponent x.toBits ∧ Wasm.IEEE64.exponent x.toBits < 1032) ∨
      Wasm.IEEE64.exponent x.toBits = 1032 ∨ 1033 ≤ Wasm.IEEE64.exponent x.toBits by omega)
    with he | ⟨he1, he2⟩ | he | he
  · have hx : |X| ≤ 1 / 2 ^ 54 := by
      have h := magnitude_le_boundary x.toBits 969 (by decide) he
      rwa [tiny_boundary, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 54)] at h
    rw [PowExpBranches.tiny_selected _ x xtail he, ExpTinyError.float_result_bits]
    apply PowExpPaths.tiny_within _ hxf hx
    have h1 : |T| ≤ 17 / 2 ^ 28 * (1 / 2 ^ 54) := htail.trans (by gcongr)
    have h2 : (1 + 1 / 2 ^ 23) * |X| / 2 ^ 65 ≤ (1 + 1 / 2 ^ 23) * (1 / 2 ^ 54) / 2 ^ 65 := by
      gcongr
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp (hLe.trans h2)
    have hn : (17 : ℝ) / 2 ^ 28 * (1 / 2 ^ 54) + (1 + 1 / 2 ^ 23) * (1 / 2 ^ 54) / 2 ^ 65 ≤
        1 / 2 ^ 70 := by norm_num
    rw [abs_le]
    constructor <;> linarith
  · have hx := magnitude_lt x.toBits 1032 9 (by norm_num) (by norm_num) he2
    norm_num at hx
    rw [PowExpBranches.ordinary_selected _ x xtail he1 he2]
    apply PowExpPaths.ordinary_within x xtail L hxf htf hx
    · calc
        _ ≤ 17 / 2 ^ 28 * |X| := htail
        _ ≤ 17 / 2 ^ 28 * 512 := by gcongr
        _ ≤ 1 / 2 ^ 14 := by norm_num
    · calc
        _ ≤ (1 + 1 / 2 ^ 23) * |X| / 2 ^ 65 := hLe
        _ ≤ (1 + 1 / 2 ^ 23) * 512 / 2 ^ 65 := by gcongr
        _ ≤ 1 / 2 ^ 55 := by norm_num
  · have hlo := magnitude_ge x.toBits 1032 9 (by norm_num) (by norm_num) (by norm_num) he.ge
    have hhi := magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
    norm_num at hlo hhi
    rw [PowExpBranches.special_selected _ x xtail he]
    have hT13 : |T| ≤ 1 / 2 ^ 13 := by
      calc
        _ ≤ 17 / 2 ^ 28 * |X| := htail
        _ ≤ 17 / 2 ^ 28 * 1024 := by gcongr
        _ ≤ 1 / 2 ^ 13 := by norm_num
    have hL1 : |X + T - L| ≤ 1 := by
      calc
        _ ≤ (1 + 1 / 2 ^ 23) * |X| / 2 ^ 65 := hLe
        _ ≤ (1 + 1 / 2 ^ 23) * 1024 / 2 ^ 65 := by gcongr
        _ ≤ 1 := by norm_num
    by_cases h768 : |X| ≤ 768
    · have hT14 : |T| ≤ 1 / 2 ^ 14 := by
        calc
          _ ≤ 17 / 2 ^ 28 * |X| := htail
          _ ≤ 17 / 2 ^ 28 * 768 := by gcongr
          _ ≤ 1 / 2 ^ 14 := by norm_num
      have hL55 : |X + T - L| ≤ 1 / 2 ^ 55 := by
        calc
          _ ≤ (1 + 1 / 2 ^ 23) * |X| / 2 ^ 65 := hLe
          _ ≤ (1 + 1 / 2 ^ 23) * 768 / 2 ^ 65 := by gcongr
          _ ≤ 1 / 2 ^ 55 := by norm_num
      rcases le_or_gt 0 X with hpos | hneg
      · rw [abs_of_nonneg hpos] at hlo
        exact PowExpSpecial.positive_within x xtail L hxf htf h768 hlo hT14 hL55
      · rw [abs_of_neg hneg] at hlo
        exact PowExpSpecial.negative_within x xtail L hxf htf h768 (by linarith) hT14 hL55
    · push Not at h768
      rcases le_or_gt 0 X with hpos | hneg
      · rw [abs_of_nonneg hpos] at h768
        exact PowExpFar.far_positive x xtail L hxf htf hhi h768 hT13 hL1
      · rw [abs_of_neg hneg] at h768
        exact PowExpFar.far_negative x xtail L hxf htf hhi (by linarith) hT13 hL1
  · have hge := magnitude_ge x.toBits 1033 10 (by norm_num) (by norm_num) (by norm_num) he
    norm_num at hge
    change 1024 ≤ |X| at hge
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
      simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
        show Wasm.IEEE64.exponent x.toBits ≠ 0 by omega, ite_false]
      positivity
    have hT : |T| ≤ 17 / 2 ^ 28 * |X| := htail
    have hLe' := abs_le.mp hLe
    have hT' := abs_le.mp hT
    rw [PowExpBranches.big_selected _ x xtail he, sign_shift_one]
    by_cases hs : Wasm.IEEE64.sign x.toBits = true
    · rw [ite_eq_left hs, PowExpBranches.underflow_bits]
      have hneg := (sign_value _ hmag).mp hs
      rw [abs_of_neg hneg] at hge hLe' hT'
      apply Library.Numerics.Float64.Exp2.Exp2Theorem.zero_within _ (Real.exp_pos _)
      have hLt : L ≤ -763 := by nlinarith
      exact (PowExpPaths.exp_tiny L hLt).trans (by norm_num)
    · rw [ite_eq_right hs, PowExpBranches.overflow_bits]
      have hpos : 0 < X := by
        rcases lt_or_ge X 0 with h | h
        · exact absurd ((sign_value _ hmag).mpr h) hs
        · rcases h.lt_or_eq with h | h
          · exact h
          · rw [← h] at hge
            norm_num at hge
      rw [abs_of_pos hpos] at hge hLe' hT'
      apply Library.Numerics.Float64.Exp2.Exp2Theorem.overflow_within
      apply PowExpPaths.exp_overflow
      nlinarith

#print axioms sign_shift_one
#print axioms powExp_within

end Library.Numerics.Float64.Pow.PowExpTheorem
