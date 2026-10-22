import LeanExe.ProofKit.TaylorRemainder
import Library.Numerics.Float64.Exp.ExpReductionBounds

/-!
The approximation errors of the two polynomials of Arm's `log2`.  The main path approximates
`log2 (1 + r)` by `r (invln2hi + invln2lo) + r ^ 2 (A0 + ... + A5 r ^ 5)` for `|r| ≤ 1/128`, and the
path near 1 by `r (invln2hi + invln2lo) + B0 r ^ 2 + ... + B9 r ^ 11` for `r` from `-0.0424` to
`0.04428`.  Each check compares the Taylor polynomial of `log (1 + r)` with the product of the
code's polynomial and `S`, the rational split of `log 2` within `2 ^ -92` of it from
`ExpReductionBounds`, and the bound divides by `log 2` at the end.
-/

namespace Library.Numerics.Float64.Log2.Log2KernelPoly
open LeanExe.ProofKit PolyBound TaylorRemainder

/-- `r (invln2hi + invln2lo) + A0 r ^ 2 + ... + A5 r ^ 7`, lowest degree first. -/
def main2 : List ℚ :=
  [0, ratOfWord 0x3FF7154765200000 + ratOfWord 0x3DE705FC2EEFA200,
    ratOfWord 0xBFE71547652B8339, ratOfWord 0x3FDEC709DC3A04BE, ratOfWord 0xBFD7154764702FFB,
    ratOfWord 0x3FD2776C50034C48, ratOfWord 0xBFCEC7B328EA92BC, ratOfWord 0x3FCA6225E117F92E]

/-- `invln2hi + invln2lo + B0 r + ... + B9 r ^ 10`, the near-1 polynomial divided by `r`. -/
def near2 : List ℚ :=
  [ratOfWord 0x3FF7154765200000 + ratOfWord 0x3DE705FC2EEFA200,
    ratOfWord 0xBFE71547652B82FE, ratOfWord 0x3FDEC709DC3A03F7, ratOfWord 0xBFD71547652B7C3F,
    ratOfWord 0x3FD2776C50F05BE4, ratOfWord 0xBFCEC709DD768FE5, ratOfWord 0x3FCA61761EC4E736,
    ratOfWord 0xBFC7153FBC64A79B, ratOfWord 0x3FC484D154F01B4A, ratOfWord 0xBFC289E4A72C383C,
    ratOfWord 0x3FC0B32F285AEE66]

theorem main2_check :
    check (subP (log1pCoeffs 12) (scaleP Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo main2)) (-1 / 128)
      (1 / 128) (1 / 2 ^ 64) 16 = true := by
  decide +kernel

theorem near2_check :
    check (subP (log1pQuotCoeffs 24) (scaleP Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo near2))
      (-424 / 10000) (4428 / 100000) (1 / 2 ^ 62) 16 = true := by
  decide +kernel

theorem split_bounds :
    |Real.log 2 - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)| ≤ 1 / 2 ^ 92 ∧
      (69 / 100 : ℝ) ≤ Real.log 2 := by
  obtain ⟨hL1, hL2⟩ := Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_enclosure
  simp only [Library.Numerics.Float64.Exp.ExpReductionBounds.lowerLogTwo, Library.Numerics.Float64.Exp.ExpReductionBounds.upperLogTwo] at hL1 hL2
  push_cast at hL1 hL2
  have hSq : (69 / 100 + 1 / 2 ^ 92 : ℚ) ≤ Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo := by decide +kernel
  have hS : (69 / 100 + 1 / 2 ^ 92 : ℝ) ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) := by
    have h := Rat.cast_le (K := ℝ) |>.mpr hSq
    push_cast at h
    exact h
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

theorem log1p_abs (r : ℝ) (hr : |r| < 1) : |Real.log (1 + r)| ≤ |r| / (1 - |r|) := by
  have h := log1p_remainder r hr 0
  have h0 : eval (log1pCoeffs 0) r = 0 := by
    simp [log1pCoeffs, log1pQuotCoeffs]
  rw [h0, sub_zero, zero_add, pow_one] at h
  exact h

/-- From a bound on `|S Q - T|` and the Taylor remainder, a bound on `|Q - log (1 + r) / log 2|`. -/
theorem divide_log2 (Q T r B M : ℝ)
    (hST : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * Q - T| ≤ B)
    (hT : |T - Real.log (1 + r)| ≤ B / 2 ^ 20) (hQ : |Q| ≤ M) (hM : M / 2 ^ 84 ≤ B) :
    |Q - Real.log (1 + r) / Real.log 2| ≤ B * (3 / 2) := by
  obtain ⟨hS, hl2⟩ := split_bounds
  have hl2pos : (0 : ℝ) < Real.log 2 := by linarith
  have h1 : |(Real.log 2 - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)) * Q| ≤ B / 2 ^ 8 := by
    rw [abs_mul]
    have h2 : |Real.log 2 - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)| * |Q| ≤ 1 / 2 ^ 92 * M :=
      mul_le_mul hS hQ (abs_nonneg _) (by norm_num)
    have h3 : (1 : ℝ) / 2 ^ 92 * M = M / 2 ^ 84 / 2 ^ 8 := by ring
    have h4 : M / 2 ^ 84 / 2 ^ 8 ≤ B / 2 ^ 8 := div_le_div_of_nonneg_right hM (by positivity)
    linarith
  have hnum : |Real.log 2 * Q - Real.log (1 + r)| ≤ B / 2 ^ 8 + B + B / 2 ^ 20 := by
    have hsplit : Real.log 2 * Q - Real.log (1 + r) =
        (Real.log 2 - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)) * Q +
          ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * Q - T) + (T - Real.log (1 + r)) := by ring
    rw [hsplit]
    calc _ ≤ |(Real.log 2 - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)) * Q| +
          |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * Q - T| + |T - Real.log (1 + r)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  rw [show Q - Real.log (1 + r) / Real.log 2 = (Real.log 2 * Q - Real.log (1 + r)) / Real.log 2 by
    field_simp, abs_div, abs_of_pos hl2pos, div_le_iff₀ hl2pos]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) hST
  nlinarith

/-- The error of `log2`'s main polynomial for `|r| ≤ 1/128`. -/
theorem main2_error (r : ℝ) (hr : |r| ≤ 1 / 128) :
    |eval main2 r - Real.log (1 + r) / Real.log 2| ≤ 1 / 2 ^ 63 := by
  obtain ⟨hS, hl2⟩ := split_bounds
  have hr1 : |r| < 1 := hr.trans_lt (by norm_num)
  have hrem := log1p_remainder r hr1 12
  obtain ⟨hlo, hhi⟩ := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ main2_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP, eval_scaleP] at hc
  have hc' : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval main2 r - eval (log1pCoeffs 12) r| ≤
      1 / 2 ^ 64 := by
    rw [abs_sub_comm]
    exact hc.trans (le_of_eq (by norm_num))
  have ht : |eval (log1pCoeffs 12) r - Real.log (1 + r)| ≤ 1 / 2 ^ 64 / 2 ^ 20 := by
    rw [abs_sub_comm]
    refine hrem.trans ?_
    have h1 : 0 < 1 - |r| := by linarith
    have hp : |r| ^ 13 ≤ (1 / 128) ^ 13 := pow_le_pow_left₀ (abs_nonneg r) hr 13
    rw [div_le_iff₀ h1]
    calc |r| ^ (12 + 1) ≤ (1 / 128) ^ 13 := hp
      _ ≤ 1 / 2 ^ 64 / 2 ^ 20 * (127 / 128) := by norm_num
      _ ≤ 1 / 2 ^ 64 / 2 ^ 20 * (1 - |r|) := by gcongr; linarith
  have hQ : |eval main2 r| ≤ 2 := by
    have hlog := log1p_abs r hr1
    have hlog' : |Real.log (1 + r)| ≤ 1 / 127 := by
      refine hlog.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hSpos : (689 / 1000 : ℝ) ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) := by
      have := abs_le.mp hS
      have h9 : (1 : ℝ) / 2 ^ 92 ≤ 1 / 1000 := by norm_num
      linarith
    have h5 : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval main2 r| ≤ 1 := by
      have h6 := abs_sub_abs_le_abs_sub ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval main2 r)
        (Real.log (1 + r))
      have h7 : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval main2 r - Real.log (1 + r)| ≤
          1 / 2 ^ 64 + 1 / 2 ^ 64 / 2 ^ 20 :=
        (abs_sub_le _ (eval (log1pCoeffs 12) r) _).trans (add_le_add hc' ht)
      have h8 : (1 : ℝ) / 2 ^ 64 + 1 / 2 ^ 64 / 2 ^ 20 ≤ 1 / 2 := by norm_num
      have h9 : (1 : ℝ) / 127 ≤ 1 / 2 := by norm_num
      linarith
    rw [abs_mul, abs_of_pos (by linarith)] at h5
    by_contra hcon
    push_neg at hcon
    have : (689 / 1000 : ℝ) * 2 ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * |eval main2 r| :=
      mul_le_mul hSpos hcon.le (by norm_num) (by linarith)
    linarith
  have h := divide_log2 (eval main2 r) (eval (log1pCoeffs 12) r) r (1 / 2 ^ 64) 2 hc' ht hQ
    (by norm_num)
  exact h.trans (by norm_num)

/-- The error of `log2`'s near-1 polynomial, relative to `r`. -/
theorem near2_error (r : ℝ) (hlo : -424 / 10000 ≤ r) (hhi : r ≤ 4428 / 100000) :
    |r * eval near2 r - Real.log (1 + r) / Real.log 2| ≤ |r| / 2 ^ 61 := by
  obtain ⟨hS, hl2⟩ := split_bounds
  have hr : |r| ≤ 4428 / 100000 := abs_le.mpr ⟨by linarith, hhi⟩
  have hr1 : |r| < 1 := hr.trans_lt (by norm_num)
  have hrem := log1p_remainder r hr1 24
  have hc := check_sound _ _ _ _ _ near2_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP, eval_scaleP] at hc
  have hc0 : |eval (log1pQuotCoeffs 24) r - (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval near2 r| ≤
      1 / 2 ^ 62 := hc.trans (le_of_eq (by norm_num))
  have hc' : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * (r * eval near2 r) -
      eval (log1pCoeffs 24) r| ≤ |r| * (1 / 2 ^ 62) := by
    rw [eval_log1pCoeffs, show (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * (r * eval near2 r) -
      r * eval (log1pQuotCoeffs 24) r = -(r * (eval (log1pQuotCoeffs 24) r -
        (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * eval near2 r)) by ring, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left hc0 (abs_nonneg r)
  have ht : |eval (log1pCoeffs 24) r - Real.log (1 + r)| ≤ |r| * (1 / 2 ^ 62) / 2 ^ 20 := by
    rw [abs_sub_comm]
    refine hrem.trans ?_
    have h1 : 0 < 1 - |r| := by linarith
    have hp : |r| ^ 24 ≤ (4428 / 100000) ^ 24 := pow_le_pow_left₀ (abs_nonneg r) hr 24
    rw [div_le_iff₀ h1, pow_succ]
    have h2 : (4428 / 100000 : ℝ) ^ 24 ≤ 1 / 2 ^ 62 / 2 ^ 20 * (95 / 100) := by norm_num
    have h3 : |r| ^ 24 * |r| ≤ (1 / 2 ^ 62 / 2 ^ 20 * (95 / 100)) * |r| :=
      mul_le_mul_of_nonneg_right (hp.trans h2) (abs_nonneg r)
    have h4 : (1 / 2 ^ 62 / 2 ^ 20 * (95 / 100)) * |r| ≤ |r| * (1 / 2 ^ 62) / 2 ^ 20 * (1 - |r|) := by
      have : (95 / 100 : ℝ) ≤ 1 - |r| := by linarith
      nlinarith
    linarith
  have hQ : |r * eval near2 r| ≤ 2 * |r| := by
    have hlog := log1p_abs r hr1
    have hlog' : |Real.log (1 + r)| ≤ |r| * (100 / 95) := by
      refine hlog.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg r]
    have hSpos : (689 / 1000 : ℝ) ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) := by
      have := abs_le.mp hS
      have h9 : (1 : ℝ) / 2 ^ 92 ≤ 1 / 1000 := by norm_num
      linarith
    have h7 : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * (r * eval near2 r) - Real.log (1 + r)| ≤
        |r| * (1 / 2 ^ 62) + |r| * (1 / 2 ^ 62) / 2 ^ 20 :=
      (abs_sub_le _ (eval (log1pCoeffs 24) r) _).trans (add_le_add hc' ht)
    have h5 : |(Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * (r * eval near2 r)| ≤ |r| * (11 / 10) := by
      have h6 := abs_sub_abs_le_abs_sub ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * (r * eval near2 r))
        (Real.log (1 + r))
      nlinarith [abs_nonneg r]
    rw [abs_mul (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ), abs_of_pos (by linarith)] at h5
    by_contra hcon
    push_neg at hcon
    have : (689 / 1000 : ℝ) * (2 * |r|) ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) * |r * eval near2 r| :=
      mul_le_mul hSpos hcon.le (by positivity) (by linarith)
    nlinarith [abs_nonneg r]
  have h := divide_log2 (r * eval near2 r) (eval (log1pCoeffs 24) r) r (|r| * (1 / 2 ^ 62))
    (2 * |r|) hc' ht hQ (by nlinarith [abs_nonneg r])
  refine h.trans ?_
  rw [div_eq_mul_one_div]
  nlinarith [abs_nonneg r]

#print axioms divide_log2
#print axioms main2_check
#print axioms near2_check
#print axioms main2_error
#print axioms near2_error

end Library.Numerics.Float64.Log2.Log2KernelPoly
