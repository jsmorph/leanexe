import Library.Numerics.Float64.Lgamma.LgammaLogdAcc

/-!
**`Lgamma.asLogdAccurate` relative to `log y` next to 1** (`acc_one`): for `y ≠ 1` with
`|log y| ≤ 2^-12`, the result lies within `|log y|/2^78` of `log y`.  The branch `|x - 2| < 1/4`
of `Lgamma.accurate` adds the logarithm of `x - 1` to a multiple of `x - 2`, and `lgamma`
vanishes at 2, so that branch needs a bound relative to `log (x - 1)`.  Such a `y` lies in
`[4095/4096, 4096/4095]`, so the reduction has `E = 0` and `t = y`, or `E = -1` and `t = 2y`.
Every factor `r1 i1 · r2 i2` other than 1, and twice every factor other than 1/2, lies at least
`6.79 · 10^-4` from 1 (`one_ok`), while `|r t - 1| ≤ 1/2400`, so `r = 1` in the first case and
`r = 1/2` (`i1 = 32`) in the second.  Then `r t` is exact, `X = r t - 1 = y - 1` is a nonzero
multiple of `2^-53`, the low part of the kernel's argument is 0, and the table's terms cancel
`E log 2` to within `2^-140` (`tab_one`).  Every error is then at most `2^-134` or proportional
to `|X|`, and `|X| ≤ (2401/2400) |log y|` (`abs_le_log`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaLogdOne
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaMul LgammaLogAccKern
  LgammaLogAccTail LgammaLogdAcc

set_option exponentiation.threshold 4096

/-- The factors `r1 i · r2 j` of the reduction next to 1 and next to 1/2. -/
def oneOk : Bool :=
  (List.range 33).all fun i => (List.range 32).all fun j =>
    let ρ := LgammaApprox.r1 i * LgammaApprox.r2 j
    decide (48 / 100 ≤ ρ) && decide (ρ ≤ 1) &&
      (if ρ = 1 then decide (i = 0 ∧ j = 0) else decide (ρ ≤ 1 - 679 / 10 ^ 6)) &&
      (if 2 * ρ = 1 then decide (i = 32 ∧ j = 0)
        else decide (2 * ρ ≤ 1 - 679 / 10 ^ 6 ∨ 1 + 679 / 10 ^ 6 ≤ 2 * ρ))

theorem one_ok : oneOk = true := by decide +kernel

theorem one_facts (i j : ℕ) (hi : i < 33) (hj : j < 32) :
    48 / 100 ≤ LgammaApprox.r1 i * LgammaApprox.r2 j ∧ LgammaApprox.r1 i * LgammaApprox.r2 j ≤ 1 ∧
      (LgammaApprox.r1 i * LgammaApprox.r2 j = 1 → i = 0 ∧ j = 0) ∧
      (LgammaApprox.r1 i * LgammaApprox.r2 j ≠ 1 →
        LgammaApprox.r1 i * LgammaApprox.r2 j ≤ 1 - 679 / 10 ^ 6) ∧
      (2 * (LgammaApprox.r1 i * LgammaApprox.r2 j) = 1 → i = 32 ∧ j = 0) ∧
      (2 * (LgammaApprox.r1 i * LgammaApprox.r2 j) ≠ 1 →
        2 * (LgammaApprox.r1 i * LgammaApprox.r2 j) ≤ 1 - 679 / 10 ^ 6 ∨
          1 + 679 / 10 ^ 6 ≤ 2 * (LgammaApprox.r1 i * LgammaApprox.r2 j)) := by
  have h := one_ok
  unfold oneOk at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h i hi j hj
  refine ⟨h1, h2, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [if_pos e] at h3; simpa using h3
  · rw [if_neg e] at h3; simpa using h3
  · rw [if_pos e] at h4; simpa using h4
  · rw [if_neg e] at h4; simpa using h4

/-- The table's triples for `r = 1/2^g` against `E ln 2` with `E = -g`: the high parts cancel,
and the middle and low parts cancel to within `2^-140`. -/
theorem tab_one (g : ℕ) (hg : g ≤ 1) :
    hiN (3 * (32 * g) + 2) + hiN (99 + 3 * 0 + 2) = g * 3048493539143 ∧
      |-(g : ℚ) * (1063452974651 / 2 ^ 84) - g * (8092541269670408 / 2 ^ 139) +
          ((midN (3 * (32 * g) + 1) : ℚ) / 2 ^ 94 + (midN (99 + 3 * 0 + 1) : ℚ) / 2 ^ 94) +
          (PolyBound.ratOfWord H[3 * (32 * g)]! + PolyBound.ratOfWord H[99 + 3 * 0]!)| ≤
        1 / 2 ^ 140 ∧
      |-(g : ℚ) * (1063452974651 / 2 ^ 84) +
          ((midN (3 * (32 * g) + 1) : ℚ) / 2 ^ 94 + (midN (99 + 3 * 0 + 1) : ℚ) / 2 ^ 94)| ≤
        1 / 2 ^ 86 := by
  interval_cases g <;> decide +kernel

theorem c2_word : PolyBound.ratOfWord 0x3A8CC01F97B57A08 = 8092541269670408 / 2 ^ 139 := by
  decide +kernel

/-- `|X| ≤ (2401/2400) |log (1 + X)|` for `|X| ≤ 1/2400`. -/
theorem abs_le_log (X : ℝ) (hX : |X| ≤ 1 / 2400) :
    |X| ≤ 2401 / 2400 * |Real.log (1 + X)| := by
  have hX' := abs_le.mp hX
  have h1X : 0 < 1 + X := by linarith
  have hne : 1 + X ≠ 0 := h1X.ne'
  have hl1 := Real.log_le_sub_one_of_pos h1X
  have hl2 := Real.one_sub_inv_le_log_of_pos h1X
  have hinv : 1 - (1 + X)⁻¹ = X / (1 + X) := by
    rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne, one_mul]; ring
  rw [hinv] at hl2
  rcases le_or_gt 0 X with h0 | h0
  · have h3 : X / (2401 / 2400) ≤ X / (1 + X) :=
      div_le_div_of_nonneg_left h0 h1X (by linarith)
    have h4 : 0 ≤ Real.log (1 + X) := by linarith [div_nonneg h0 h1X.le]
    rw [abs_of_nonneg h0, abs_of_nonneg h4]
    have : X / (2401 / 2400) = 2400 / 2401 * X := by ring
    linarith
  · have h4 : Real.log (1 + X) < 0 := by linarith
    rw [abs_of_neg h0, abs_of_neg h4]
    linarith

set_option maxHeartbeats 4000000 in
/-- **`asLogdAccurate` within `|log y|/2^78` of `log y`** for `y ≠ 1` with `|log y| ≤ 2^-12`.
The middle part is at most `|log y|/2^43 + 2^-84` and the low part is 0. -/
theorem acc_one (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (y : Float)
    (hy : Finite y.toBits) (hpos : 0 < value y.toBits) (hy1 : value y.toBits ≠ 1)
    (hly : |Real.log (value y.toBits)| ≤ 1 / 2 ^ 12) :
    Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits ∧
      Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits ∧
      Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits ∧
      |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits +
          value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits +
          value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits -
          Real.log (value y.toBits)| ≤ |Real.log (value y.toBits)| / 2 ^ 78 ∧
      |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits| ≤
        |Real.log (value y.toBits)| / 2 ^ 43 + 1 / 2 ^ 84 ∧
      value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits = 0 := by
  -- `y` in `[4095/4096, 4096/4095]`
  have hyl : 4095 / 4096 ≤ value y.toBits := by
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 := (abs_le.mp hly).1
    linarith
  have hyu : value y.toBits ≤ 4096 / 4095 := by
    have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h2 := (abs_le.mp hly).2
    have h3 : 4095 / 4096 ≤ (value y.toBits)⁻¹ := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h4
    linarith
  obtain ⟨E, hEb, hRt, hRt1, hRt2, hRr, hRrv, hRrt, hRed, hRedv, hRi1, hRi2, hyv, k, hk, hkv⟩ :=
    LgammaLogAccRed.reduce_spec y hy hpos
  obtain ⟨T, hT⟩ : ∃ T, Lgamma.asLogdAccurate Tgamma.logdTable H y = T := ⟨_, rfl⟩
  rw [hT]
  unfold Lgamma.asLogdAccurate at hT
  generalize hR : Lgamma.logReduce Tgamma.logdTable y = R at hT hRt hRt1 hRt2 hRr hRrv hRrt hRed hRedv hRi1 hRi2 hyv hkv
  obtain ⟨t, r, ed, i1, i2⟩ := R
  dsimp only at hT hRt hRt1 hRt2 hRr hRrv hRrt hRed hRedv hRi1 hRi2 hyv hkv
  generalize hD : fastTwoSum (r * t - 1.0) (Library.Numerics.Arithmetic.Fma.fma r t (-(r * t))) = D at hT
  generalize hP : Lgamma.polyDD H 198 6 D.1 D.2
    (D.1 * (entry H 210 + D.1 * (entry H 212 + D.1 * entry H 214))) = P at hT
  generalize hQ : mulDD D.1 D.2 P.1 P.2 = Q at hT
  generalize hS1 : sumDD (Float.ofBits 0x3D2EF35793C76000 * ed) (Float.ofBits 0x3A8CC01F97B57A08 * ed)
    (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)) (entry H (3 * i1) + entry H (99 + 3 * i2)) =
    S1 at hT
  generalize hS2 : sumDD S1.1 S1.2 Q.1 Q.2 = S2 at hT
  generalize hF1 : fastTwoSum (Float.ofBits 0x3FE62E42FEFA3800 * ed +
    (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2))) S2.1 = F1 at hT
  generalize hF2 : fastTwoSum F1.2 S2.2 = F2 at hT
  subst hT
  dsimp only
  -- the reduction's values
  generalize hτ : value t.toBits = τ at hRt1 hRt2 hRrt hyv hkv
  generalize hρ : value r.toBits = ρ at hRrv hRrt
  obtain ⟨X, hXdef⟩ : ∃ X, ρ * τ - 1 = X := ⟨_, rfl⟩
  rw [hXdef] at hRrt
  have hX : |X| ≤ 1 / 2400 := hRrt
  have hr1 := (Rat.cast_lt (K := ℝ)).mpr (r_pos.1 i1.toNat hRi1)
  have hr2 := (Rat.cast_lt (K := ℝ)).mpr (r_pos.2 i2.toNat hRi2)
  push_cast at hr1 hr2
  have hρ0 : 0 < ρ := by rw [hRrv]; exact mul_pos hr1 hr2
  have hρq : ρ = ((LgammaApprox.r1 i1.toNat * LgammaApprox.r2 i2.toNat : ℚ) : ℝ) := by
    rw [hRrv, Rat.cast_mul]
  -- the exponent is 0 or -1
  have hE2 : E = 0 ∨ E = -1 := by
    rcases le_or_gt E (-2) with h | h
    · exfalso
      have h1 : (2 : ℝ) ^ E ≤ 2 ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) h
      have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
      have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ τ)
      rw [h2, ← hyv] at h3
      linarith
    rcases le_or_gt 1 E with h' | h'
    · exfalso
      have h1 : (2 : ℝ) ^ (1 : ℤ) ≤ 2 ^ E := zpow_le_zpow_right₀ (by norm_num) h'
      rw [zpow_one] at h1
      have h3 := mul_le_mul h1 hRt1 (by norm_num) (by positivity)
      rw [← hyv] at h3
      linarith
    omega
  -- `r = 1/2^g` with `E = -g`
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := one_facts i1.toNat i2.toNat hRi1 hRi2
  obtain ⟨g, hg, hEg, hn1, hn2, hρg, hyX⟩ : ∃ g : ℕ, g ≤ 1 ∧ E = -(g : ℤ) ∧
      i1.toNat = 32 * g ∧ i2.toNat = 0 ∧ ρ = 1 / 2 ^ g ∧ value y.toBits = 1 + X := by
    have hXl := abs_le.mp hX
    rcases hE2 with h | h
    · rw [h, zpow_zero, one_mul] at hyv
      have hq : LgammaApprox.r1 i1.toNat * LgammaApprox.r2 i2.toNat = 1 := by
        by_contra hne
        have h4 : ρ ≤ 1 - 679 / 10 ^ 6 := by
          have := (Rat.cast_le (K := ℝ)).mpr (f4 hne)
          rw [hρq]; push_cast at this ⊢; linarith
        have h5 : ρ * τ ≤ ρ * (4096 / 4095) :=
          mul_le_mul_of_nonneg_left (by rw [← hyv]; exact hyu) hρ0.le
        linarith
      obtain ⟨a1, a2⟩ := f3 hq
      have hρ1 : ρ = 1 := by rw [hρq, hq]; norm_num
      refine ⟨0, by norm_num, by rw [h]; simp, by omega, a2, by rw [hρ1]; norm_num, ?_⟩
      rw [← hXdef, hρ1, hyv]; ring
    · rw [h, zpow_neg_one, ← div_eq_inv_mul] at hyv
      have hq : 2 * (LgammaApprox.r1 i1.toNat * LgammaApprox.r2 i2.toNat) = 1 := by
        by_contra hne
        rcases f6 hne with h4 | h4
        · have h4' : 2 * ρ ≤ 1 - 679 / 10 ^ 6 := by
            have := (Rat.cast_le (K := ℝ)).mpr h4
            rw [hρq]; push_cast at this ⊢; linarith
          have h5 : ρ * τ < ρ * 2 := mul_lt_mul_of_pos_left hRt2 hρ0
          linarith
        · have h4' : 1 + 679 / 10 ^ 6 ≤ 2 * ρ := by
            have := (Rat.cast_le (K := ℝ)).mpr h4
            rw [hρq]; push_cast at this ⊢; linarith
          have h5 : ρ * (2 * (4095 / 4096)) ≤ ρ * τ :=
            mul_le_mul_of_nonneg_left (by linarith) hρ0.le
          linarith
      obtain ⟨a1, a2⟩ := f5 hq
      have hρ1 : ρ = 1 / 2 := by
        rw [hρq]
        have : LgammaApprox.r1 i1.toNat * LgammaApprox.r2 i2.toNat = 1 / 2 := by linarith
        rw [this]; norm_num
      refine ⟨1, by norm_num, by rw [h]; simp, by omega, a2, by rw [hρ1]; norm_num, ?_⟩
      rw [← hXdef, hρ1, hyv]; ring
  -- `X` is a nonzero multiple of `2^-53`
  have hX0 : X ≠ 0 := by
    intro h; apply hy1; rw [hyX, h, add_zero]
  have hXlo : 1 / 2 ^ 53 ≤ |X| := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, X = m / 2 ^ 53 := by
      interval_cases g
      · exact ⟨2 * k - 2 ^ 53, by rw [← hXdef, hρg, hkv]; push_cast; ring⟩
      · exact ⟨k - 2 ^ 53, by rw [← hXdef, hρg, hkv]; push_cast; ring⟩
    have hm0 : m ≠ 0 := by rintro rfl; apply hX0; rw [hm]; simp
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
    rw [hm, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  -- `r t` exact, the low part of `r t - 1` zero, and the kernel
  obtain ⟨hrtf, hrtv⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_mul r t hRr hRt 1 k g 52 (by simp [hρ, hρg])
    (by simp [hτ, hkv]) (by simpa using hk) (by omega)
  rw [hρ, hτ] at hrtv
  have z0 := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_finite
  have zv := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_value
  obtain ⟨-, -, hxv, hxf, hlf, -, -, -, -, -, -⟩ := Library.Numerics.Float64.Tgamma.TgammaLogdKernel.kernel_spec hF r t 0.0 0.0
    0.0 0.0 hRr hRt z0 z0 z0 z0 (by rw [hρ, hτ, hXdef]; exact hX) (by rw [zv]; norm_num)
    (by rw [zv]; norm_num) (by rw [zv]; norm_num) (by rw [zv]; norm_num)
  obtain ⟨hnf, hnv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.neg_float (r * t) hrtf
  have hfz : value (Library.Numerics.Arithmetic.Fma.fma r t (-(r * t))).toBits = 0 := by
    have hsum : value r.toBits * value t.toBits + value (-(r * t)).toBits = 0 := by
      rw [hnv, hrtv, hρ, hτ]; ring
    obtain ⟨-, hnear⟩ := hF r t (-(r * t)) hRr hRt hnf (by rw [hsum]; norm_num)
    have h := hnear _ z0
    rw [hsum, zv, sub_zero, sub_zero, abs_zero] at h
    exact abs_nonpos_iff.mp h
  have hxv' : value (r * t - 1.0).toBits = X := by rw [hxv, hrtv, hXdef]
  obtain ⟨hD1f, hD2f, hDs, hD2a, -⟩ := fastTwoSum_spec (r * t - 1.0) (Library.Numerics.Arithmetic.Fma.fma r t (-(r * t)))
    hxf hlf (by rw [hfz, abs_zero]; exact abs_nonneg _)
    (by rw [hxv']; linarith [(by norm_num : (1 : ℝ) / 2400 < 2 ^ 900)])
  rw [hD] at hD1f hD2f hDs hD2a
  rw [hxv', hfz, add_zero] at hDs
  rw [hfz, abs_zero] at hD2a
  have hD2z : value D.2.toBits = 0 := abs_nonpos_iff.mp hD2a
  have hD1v : value D.1.toBits = X := by linarith
  obtain ⟨hQ1f, hQ2f, hQe, hQ2b, hQ1b⟩ := kern_spec hF D.1 D.2 hD1f hD2f 0
    (by rw [hD1v]; linarith [(by norm_num : (1 : ℝ) / 2400 ≤ 1 / 2400 + 1 / 2 ^ 51)])
    (by rw [hD2z]; simp) (by norm_num)
  rw [hP, hQ] at hQ1f hQ2f hQe hQ2b hQ1b
  simp only [hD1v, hD2z, add_zero, zero_div, mul_zero] at hQe hQ2b hQ1b
  have hQlog : |value Q.1.toBits + value Q.2.toBits - Real.log (1 + X)| ≤
      |X| / 2 ^ 93 + 1 / 2 ^ 80 * |X| + 1 / 2 ^ 1060 := by
    have e1 := abs_le.mp hQe
    have e2 := abs_le.mp (hLA.1 X hX)
    rw [abs_le]; constructor <;> linarith
  have hQ1b' : |value Q.1.toBits| ≤ 4185 / 10 ^ 7 := by
    have h4 : |X| * (1 + 1 / 2 ^ 8) ≤ 1 / 2400 * (1 + 1 / 2 ^ 8) :=
      mul_le_mul_of_nonneg_right hX (by norm_num)
    linarith [(by norm_num : (1 / 2400 : ℝ) * (1 + 1 / 2 ^ 8) + 1 / 2 ^ 1060 ≤ 4185 / 10 ^ 7)]
  -- the words of the table
  obtain ⟨-, hhi1, hhi2, hmid1, hmid2, hlo1, hlo2⟩ := words_ok
  obtain ⟨ia0, ia1, ia2⟩ := ix_a i1 hRi1
  obtain ⟨ib0, ib1, ib2⟩ := ix_b i2 hRi2
  obtain ⟨hh1, hh1a, hh1b⟩ := hhi1 (32 * g) (by omega)
  obtain ⟨hh2, hh2a, hh2b⟩ := hhi2 0 (by omega)
  obtain ⟨hm1, hm1a, hm1b⟩ := hmid1 (32 * g) (by omega)
  obtain ⟨hm2, hm2a, hm2b⟩ := hmid2 0 (by omega)
  obtain ⟨hl1a, hl1b⟩ := hlo1 (32 * g) (by omega)
  obtain ⟨hl2a, hl2b⟩ := hlo2 0 (by omega)
  obtain ⟨fe1h, ve1h⟩ := entry_val (3 * (32 * g) + 2) (by omega) (3 * i1 + 2) (by rw [ia2, hn1])
  obtain ⟨fe2h, ve2h⟩ := entry_val (99 + 3 * 0 + 2) (by omega) (99 + 3 * i2 + 2) (by rw [ib2, hn2])
  obtain ⟨fe1m, ve1m⟩ := entry_val (3 * (32 * g) + 1) (by omega) (3 * i1 + 1) (by rw [ia1, hn1])
  obtain ⟨fe2m, ve2m⟩ := entry_val (99 + 3 * 0 + 1) (by omega) (99 + 3 * i2 + 1) (by rw [ib1, hn2])
  obtain ⟨fe1l, ve1l⟩ := entry_val (3 * (32 * g)) (by omega) (3 * i1) (by rw [ia0, hn1])
  obtain ⟨fe2l, ve2l⟩ := entry_val (99 + 3 * 0) (by omega) (99 + 3 * i2) (by rw [ib0, hn2])
  rw [hh1] at ve1h
  rw [hh2] at ve2h
  rw [hm1] at ve1m
  rw [hm2] at ve2m
  push_cast at ve1h ve2h ve1m ve2m
  have hl1a' := (Rat.cast_le (K := ℝ)).mpr hl1a
  have hl1b' := (Rat.cast_le (K := ℝ)).mpr hl1b
  have hl2a' := (Rat.cast_le (K := ℝ)).mpr hl2a
  have hl2b' := (Rat.cast_le (K := ℝ)).mpr hl2b
  push_cast at hl1a' hl1b' hl2a' hl2b'
  rw [← ve1l] at hl1a' hl1b'
  rw [← ve2l] at hl2a' hl2b'
  obtain ⟨t1, t2, t3⟩ := tab_one g hg
  have t1R : (hiN (3 * (32 * g) + 2) : ℝ) + (hiN (99 + 3 * 0 + 2) : ℝ) = (g : ℝ) * 3048493539143 := by
    exact_mod_cast t1
  have t2R := (Rat.cast_le (K := ℝ)).mpr t2
  have t3R := (Rat.cast_le (K := ℝ)).mpr t3
  push_cast at t2R t3R
  -- the words of `ln 2` and the exponent
  obtain ⟨wc0, wc1, -, wc2b, fc0, fc1, fc2⟩ := ln2_words
  have vc0 : value (Float.ofBits 0x3FE62E42FEFA3800).toBits = 3048493539143 / 2 ^ 42 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ fc0, wc0]; push_cast; ring
  have vc1 : value (Float.ofBits 0x3D2EF35793C76000).toBits = 1063452974651 / 2 ^ 84 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ fc1, wc1]; push_cast; ring
  have vc2 : value (Float.ofBits 0x3A8CC01F97B57A08).toBits = 8092541269670408 / 2 ^ 139 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ fc2, c2_word]; push_cast; ring
  have ffc0 := Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ fc0
  have ffc1 := Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ fc1
  have ffc2 := Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ fc2
  have hEr : (E : ℝ) = -(g : ℝ) := by simp [hEg]
  have hEn : E.natAbs ≤ 1 := by rw [hEg]; simpa using hg
  have hg01 : (g : ℝ) ≤ 1 := by exact_mod_cast hg
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  -- `l₀ + s₂`: exactly 0
  obtain ⟨hs2f, hs2v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_add (entry H (3 * i1 + 2)) (entry H (99 + 3 * i2 + 2))
    fe1h fe2h (hiN (3 * (32 * g) + 2) + hiN (99 + 3 * 0 + 2)) 42
    (by rw [ve1h, ve2h]; push_cast; ring)
    (by rw [abs_le, show (2 : ℤ) ^ 53 = 9007199254740992 by norm_num]; constructor <;> omega)
    (by norm_num)
  obtain ⟨hl0f, hl0v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_mul (Float.ofBits 0x3FE62E42FEFA3800) ed ffc0 hRed
    3048493539143 E 42 0 (by rw [vc0]; norm_num) (by rw [hRedv]; norm_num)
    (by rw [show (3048493539143 : ℤ).natAbs = 3048493539143 from rfl]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hEn) (by norm_num)) (by norm_num)
  have hl0s : value (Float.ofBits 0x3FE62E42FEFA3800 * ed).toBits +
      value (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2)).toBits = 0 := by
    rw [hl0v, hs2v, vc0, ve1h, ve2h, hRedv, hEr]
    linarith [t1R]
  obtain ⟨hl0'f, hl0'v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_add (Float.ofBits 0x3FE62E42FEFA3800 * ed)
    (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2)) hl0f hs2f 0 42
    (by rw [hl0s]; simp) (by norm_num) (by norm_num)
  have hl0'z : value (Float.ofBits 0x3FE62E42FEFA3800 * ed +
      (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2))).toBits = 0 := by
    rw [hl0'v, hl0s]
  -- `l₁`, `l₂`, and `s₁`, exact, and `s₀`
  obtain ⟨hl1f, hl1v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_mul (Float.ofBits 0x3D2EF35793C76000) ed ffc1 hRed
    1063452974651 E 84 0 (by rw [vc1]; norm_num) (by rw [hRedv]; norm_num)
    (by rw [show (1063452974651 : ℤ).natAbs = 1063452974651 from rfl]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hEn) (by norm_num)) (by norm_num)
  obtain ⟨hl2f, hl2v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_mul (Float.ofBits 0x3A8CC01F97B57A08) ed ffc2 hRed
    8092541269670408 E 139 0 (by rw [vc2]; norm_num) (by rw [hRedv]; norm_num)
    (by rw [show (8092541269670408 : ℤ).natAbs = 8092541269670408 from rfl]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hEn) (by norm_num)) (by norm_num)
  obtain ⟨hs1f, hs1v⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc1.grid_add (entry H (3 * i1 + 1)) (entry H (99 + 3 * i2 + 1))
    fe1m fe2m (midN (3 * (32 * g) + 1) + midN (99 + 3 * 0 + 1)) 94
    (by rw [ve1m, ve2m]; push_cast; ring)
    (by rw [abs_le, show (2 : ℤ) ^ 53 = 9007199254740992 by norm_num]; constructor <;> omega)
    (by norm_num)
  have fs0 := fapprox_add (fapprox_self _ fe1l) (fapprox_self _ fe2l) (2 / 2 ^ 93)
    (by rw [add_zero, abs_of_nonneg (by linarith)]; linarith) (by norm_num)
  have vl1 : value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits =
      -(g : ℝ) * (1063452974651 / 2 ^ 84) := by
    rw [hl1v, vc1, hRedv, hEr]; ring
  have vl2 : value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits =
      -(g : ℝ) * (8092541269670408 / 2 ^ 139) := by
    rw [hl2v, vc2, hRedv, hEr]; ring
  have vs1 : value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits =
      (midN (3 * (32 * g) + 1) : ℝ) / 2 ^ 94 + (midN (99 + 3 * 0 + 1) : ℝ) / 2 ^ 94 := by
    rw [hs1v, ve1m, ve2m]
  have hs0e : |value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits -
      (value (entry H (3 * i1)).toBits + value (entry H (99 + 3 * i2)).toBits)| ≤ 1 / 2 ^ 145 := by
    have := fs0.2
    linarith [(by norm_num : (0 : ℝ) + 0 + 2 / 2 ^ 93 / 2 ^ 53 ≤ 1 / 2 ^ 145)]
  have hs0b : |value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits| ≤ 1 / 2 ^ 91 := by
    have h1 := fs0.2
    have h3 := abs_sub_abs_le_abs_sub (value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits)
      (value (entry H (3 * i1)).toBits + value (entry H (99 + 3 * i2)).toBits)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ value (entry H (3 * i1)).toBits +
      value (entry H (99 + 3 * i2)).toBits)] at h3
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 93 + (0 + 0 + 2 / 2 ^ 93 / 2 ^ 53) ≤ 1 / 2 ^ 91)]
  have hs1b : |value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits| ≤ 1 / 2 ^ 40 := by
    rw [vs1]
    have h1 : ((midN (3 * (32 * g) + 1) : ℤ) : ℝ) ≤ 4312648921537145 := by exact_mod_cast hm1b
    have h2 : ((midN (99 + 3 * 0 + 1) : ℤ) : ℝ) ≤ 4496283226037544 := by exact_mod_cast hm2b
    have h3 : (0 : ℝ) ≤ ((midN (3 * (32 * g) + 1) : ℤ) : ℝ) := by exact_mod_cast hm1a
    have h4 : (0 : ℝ) ≤ ((midN (99 + 3 * 0 + 1) : ℤ) : ℝ) := by exact_mod_cast hm2a
    rw [abs_le]
    constructor <;> linarith [(by norm_num : ((4312648921537145 : ℝ) + 4496283226037544) / 2 ^ 94 ≤
      1 / 2 ^ 40)]
  have hls1 : |value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits +
      value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits| ≤ 1 / 2 ^ 86 := by
    rw [vl1, vs1]
    have := abs_le.mp t3R
    rw [abs_le]; constructor <;> linarith
  have hl2b : |value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits| ≤ 1 / 2 ^ 86 := by
    rw [vl2, abs_le]
    constructor <;> linarith [(by norm_num : (8092541269670408 : ℝ) / 2 ^ 139 ≤ 1 / 2 ^ 86)]
  -- `S₁`: at most `2^-136`
  obtain ⟨hS1f1, hS1f2, hS1e, hS1l, hS1h⟩ := sumDD_spec _ _ _ _ hl1f hl2f hs1f fs0.1
    (by rw [vl1, abs_lt]; constructor <;> linarith [(by norm_num : (1063452974651 : ℝ) / 2 ^ 84 < 2 ^ 898)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 40 < 2 ^ 898)])
    (1 / 2 ^ 86 + 1 / 2 ^ 91) (by linarith) (by norm_num)
  rw [hS1] at hS1f1 hS1f2 hS1e hS1l hS1h
  have hS1hb : |value S1.1.toBits| ≤ 1 / 2 ^ 85 := by
    have h2 : |value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits +
        value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits| * (1 + 1 / 2 ^ 51) ≤
        1 / 2 ^ 86 * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right hls1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 86 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 1 / 2 ^ 85)]
  have hS1lb : |value S1.2.toBits| ≤ 1 / 2 ^ 85 := by
    have h2 : |value S1.1.toBits| / 2 ^ 51 ≤ 1 / 2 ^ 85 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS1hb (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 86 + 1 / 2 ^ 91 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 85 / 2 ^ 51 +
      1 / 2 ^ 1073 ≤ 1 / 2 ^ 85)]
  have hS1sum : |value S1.1.toBits + value S1.2.toBits| ≤ 1 / 2 ^ 136 := by
    have h2 : |value S1.1.toBits| / 2 ^ 52 ≤ 1 / 2 ^ 85 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS1hb (by norm_num)
    have e1 := abs_le.mp hS1e
    have e2 := abs_le.mp t2R
    have e3 := abs_le.mp hs0e
    rw [vl1, vl2, vs1] at e1
    rw [abs_le]
    constructor <;> linarith [(by norm_num : (3 * (1 / 2 ^ 86 + 1 / 2 ^ 91) + 1 / 2 ^ 85 / 2 ^ 52 +
      1 / 2 ^ 1074 : ℝ) / 2 ^ 53 + 1 / 2 ^ 140 + 1 / 2 ^ 145 ≤ 1 / 2 ^ 136)]
  -- `S₂`
  obtain ⟨hS2f1, hS2f2, hS2e, hS2l, hS2h⟩ := sumDD_spec _ _ _ _ hS1f1 hS1f2 hQ1f hQ2f
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 85 < 2 ^ 898)])
    (by linarith [(by norm_num : (4185 : ℝ) / 10 ^ 7 < 2 ^ 898)])
    (1 / 2 ^ 85 + (|X| / 2 ^ 44 + 1 / 2 ^ 1060)) (by linarith)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 85 + (1 / 2400 / 2 ^ 44 + 1 / 2 ^ 1060) ≤ 2 ^ 800)])
  rw [hS2] at hS2f1 hS2f2 hS2e hS2l hS2h
  have hS2hb : |value S2.1.toBits| ≤ |X| * (1 + 1 / 2 ^ 7) + 1 / 2 ^ 84 := by
    have h1 := abs_add_le (value S1.1.toBits) (value Q.1.toBits)
    have h0 := abs_nonneg X
    have h2 : |value S1.1.toBits + value Q.1.toBits| * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 85 + (|X| * (1 + 1 / 2 ^ 8) + 1 / 2 ^ 1060)) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hS2lb : |value S2.2.toBits| ≤ |X| * (1 + 1 / 2 ^ 6) / 2 ^ 44 + 1 / 2 ^ 84 := by
    have h2 : |value S2.1.toBits| / 2 ^ 51 ≤ (|X| * (1 + 1 / 2 ^ 7) + 1 / 2 ^ 84) / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS2hb (by norm_num)
    have h0 := abs_nonneg X
    linarith
  -- `F₁` and `F₂`: the high part `l₀ + s₂` is 0
  obtain ⟨hF1f1, hF1f2, hF1v1, hF1v2⟩ := fts_zero _ S2.1 hl0'f hS2f1 hl0'z
    (by linarith [abs_nonneg X, (by norm_num : (1 : ℝ) / 2400 * (1 + 1 / 2 ^ 7) + 1 / 2 ^ 84 < 2 ^ 1000)])
  rw [hF1] at hF1f1 hF1f2 hF1v1 hF1v2
  obtain ⟨hF2f1, hF2f2, hF2v1, hF2v2⟩ := fts_zero F1.2 S2.2 hF1f2 hS2f2 hF1v2
    (by linarith [abs_nonneg X,
      (by norm_num : (1 : ℝ) / 2400 * (1 + 1 / 2 ^ 6) / 2 ^ 44 + 1 / 2 ^ 84 < 2 ^ 1000)])
  rw [hF2] at hF2f1 hF2f2 hF2v1 hF2v2
  -- the bounds relative to `log y = log (1 + X)`
  have hlogX := abs_le_log X hX
  have hL0 := abs_nonneg (Real.log (1 + X))
  rw [hyX]
  refine ⟨hF1f1, hF2f1, hF2f2, ?_, ?_, hF2v2⟩
  · rw [hF1v1, hF2v1, hF2v2, add_zero]
    have h2 : |value S2.1.toBits| / 2 ^ 52 ≤ (|X| * (1 + 1 / 2 ^ 7) + 1 / 2 ^ 84) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS2hb (by norm_num)
    have e1 := abs_le.mp hS2e
    have e2 := abs_le.mp hS1sum
    have e3 := abs_le.mp hQlog
    have hc : 1 / 2 ^ 134 ≤ |X| / 2 ^ 81 := by
      have := div_le_div_of_nonneg_right hXlo (by norm_num : (0 : ℝ) ≤ 2 ^ 81)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 / 2 ^ 81 = 1 / 2 ^ 134)]
    have h0 := abs_nonneg X
    rw [abs_le]; constructor <;> linarith
  · rw [hF2v1]
    linarith [abs_nonneg X]

#print axioms acc_one

end Library.Numerics.Float64.Lgamma.LgammaLogdOne
