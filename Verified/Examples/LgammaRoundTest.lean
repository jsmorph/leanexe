import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.F64TwoSum

/-!
The rounding test of CORE-MATH's fast paths.  The code returns `ub = fh + (fl + eps)` when it
equals `lb = fh + (fl - eps)` and calls the accurate path otherwise.  When the two agree, the exact
sums `A ≥ B` before the last rounding have the same nearest word `U`, so `[B, A]` lies in the
rounding cell of `U`.  `steps_pos` shows that every number within `3/5 (A - B)` of `[B, A]` has a
nearest word within one step of `U`: the cells of the neighbours of `U` are at least two thirds as
long as the cell of `U`, from the spacing facts `sp_mono` and `sp_two`.  `within_of_test` states
this for signed numbers with `Rounded` words, and `round_test` for the code's `Float` operations:
an error of at most `2 eps` in `fh + fl` gives one step when the test passes.  The bound covers the
code's `eps` with a factor of two, which the approximation facts of `LgammaApprox` need next to the
zeros of `log |Γ|`.
-/

namespace Verified.Examples.LgammaRoundTest
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative F64RoundNearest F64Approx

set_option exponentiation.threshold 4096

/-! ### The grid of nonnegative words -/

/-- The value of the nonnegative word `k`. -/
noncomputable def v (k : ℕ) : ℝ := value (UInt64.ofNat k)

/-- The spacing after the nonnegative word `k`. -/
noncomputable def sp (k : ℕ) : ℝ := (2 : ℝ) ^ (k / 2 ^ 52 - 1) / 2 ^ 1074

theorem word (k : ℕ) (hk : k < 9223372036854775808) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 18446744073709551616 := rfl; omega)

theorem limit_eq : limit = 9218868437227405312 := rfl

theorem gap (k : ℕ) (hk : k + 1 < 9223372036854775808) : v (k + 1) - v k = sp k := by
  have hg := F64Adjacent.positive_successor_gap (UInt64.ofNat k)
    (by rw [word k (by omega)]; norm_num; omega)
  have hi : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := (UInt64.ofNat_add k 1).symm
  rw [hi, word k (by omega)] at hg
  exact hg

theorem sp_pos (k : ℕ) : 0 < sp k := by unfold sp; positivity

theorem sp_mono {j k : ℕ} (h : j ≤ k) : sp j ≤ sp k := by
  unfold sp
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  have h52 : (2 : ℕ) ^ 52 = 4503599627370496 := by norm_num
  rw [h52]
  omega

theorem sp_two (k : ℕ) : sp (k + 2) ≤ 2 * sp k := by
  unfold sp
  have h52 : (2 : ℕ) ^ 52 = 4503599627370496 := by norm_num
  have h : (k + 2) / 2 ^ 52 - 1 ≤ k / 2 ^ 52 - 1 + 1 := by rw [h52]; omega
  rw [show (2 : ℝ) * (2 ^ (k / 2 ^ 52 - 1) / 2 ^ 1074) = 2 ^ (k / 2 ^ 52 - 1 + 1) / 2 ^ 1074 by
    ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h

theorem sp_small (k : ℕ) (hk : k < 2 ^ 52) : sp k = 1 / 2 ^ 1074 := by
  unfold sp
  rw [Nat.div_eq_of_lt hk]
  norm_num

theorem v_zero : v 0 = 0 := F64Magnitude.value_zero

theorem v_mono {j k : ℕ} (h : j ≤ k) (hk : k < 9223372036854775808) : v j ≤ v k := by
  unfold v
  exact (F64PositiveOrder.value_le_iff (by rw [word j (by omega)]; norm_num; omega)
    (by rw [word k hk]; norm_num; omega)).mpr (by rw [word j (by omega), word k hk]; exact h)

theorem v_ge_sp (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 9223372036854775808) : sp k ≤ v k := by
  unfold v sp
  rw [F64Adjacent.unsigned_word_value _ (by rw [word k hk]; norm_num; omega), word k hk]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold F64Order.unsignedScaled
  split
  · rename_i h0
    have hlt : k < 2 ^ 52 := by
      have h52 : (2 : ℕ) ^ 52 = 4503599627370496 := by norm_num
      rw [h52] at h0 ⊢; omega
    rw [h0, Nat.mod_eq_of_lt hlt]
    norm_num
    exact_mod_cast hk1
  · rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    apply le_mul_of_one_le_left (by positivity)
    have : (1 : ℕ) ≤ 2 ^ 52 + k % 2 ^ 52 := by have : 1 ≤ 2 ^ 52 := Nat.one_le_two_pow; omega
    exact_mod_cast this

theorem v_one : v 1 = 1 / 2 ^ 1074 := by
  have h := gap 0 (by norm_num)
  rw [v_zero, sp_small 0 (by norm_num)] at h
  simpa using h

/-! ### Numbers near the rounding cell of a positive word -/

/-- **Every number within `3/5 (A - B)` of `[B, A]`**, where `A` and `B` have the nearest word `w`,
has a nearest word within one step of `w`. -/
theorem steps_pos (w : ℕ) (A B y : ℝ) (hwl : w + 2 < limit)
    (hA : Nearest A (UInt64.ofNat w)) (hB : Nearest B (UInt64.ofNat w)) (hB0 : 0 < B)
    (hgap : 1 / 2 ^ 1074 < A - B) (hy1 : B - 3 / 5 * (A - B) ≤ y)
    (hy2 : y ≤ A + 3 / 5 * (A - B)) (r : UInt64) (hr : Nearest y r) :
    0 < y ∧ w ≤ r.toNat + 1 ∧ r.toNat ≤ w + 1 := by
  have hl := limit_eq
  have hAup : 2 * A ≤ v w + v (w + 1) := by
    have h := hA.2 (UInt64.ofNat (w + 1)) (by rw [word _ (by omega)]; omega)
    have hg := gap w (by omega)
    exact F64NearestStep.upper_midpoint (v w) (v (w + 1)) A (by linarith [sp_pos w]) h
  have hBlo (hw1 : 1 ≤ w) : v (w - 1) + v w ≤ 2 * B := by
    have h := hB.2 (UInt64.ofNat (w - 1)) (by rw [word _ (by omega)]; omega)
    have hg := gap (w - 1) (by omega)
    rw [Nat.sub_add_cancel hw1] at hg
    have := F64NearestStep.lower_midpoint (v w) (v (w - 1)) B (by linarith [sp_pos (w - 1)]) h
    linarith
  have hw2 : 2 ≤ w := by
    by_contra hc
    rcases (show w = 0 ∨ w = 1 by omega) with h | h
    · subst h
      have h1 := hB.2 (UInt64.ofNat 1) (by rw [word _ (by norm_num), limit_eq]; norm_num)
      have hv1 : value (UInt64.ofNat 1) = 1 / 2 ^ 1074 := v_one
      have hv0 : value (UInt64.ofNat 0) = 0 := v_zero
      rw [hv0, hv1, zero_sub, abs_neg, abs_of_pos hB0] at h1
      rw [zero_add, v_zero, v_one] at hAup
      rcases le_or_gt B (1 / 2 ^ 1074) with hb | hb
      · rw [abs_of_nonneg (by linarith)] at h1
        linarith
      · rw [abs_of_neg (by linarith)] at h1
        linarith
    · subst h
      have hb := hBlo le_rfl
      have hg1 := gap 1 (by norm_num)
      rw [show (1 : ℕ) - 1 = 0 from rfl, v_zero, v_one] at hb
      rw [show (1 : ℕ) + 1 = 2 from rfl, v_one, sp_small 1 (by norm_num)] at hg1
      rw [show (1 : ℕ) + 1 = 2 from rfl, v_one] at hAup
      linarith
  obtain ⟨u, rfl⟩ : ∃ u, w = u + 2 := ⟨w - 2, by omega⟩
  have hBlo' := hBlo (by omega)
  rw [show u + 2 - 1 = u + 1 by omega] at hBlo'
  have g0 := gap u (by omega)
  have g1 := gap (u + 1) (by omega)
  have g2 := gap (u + 2) (by omega)
  have g3 := gap (u + 3) (by omega)
  rw [show u + 1 + 1 = u + 2 by omega] at g1
  rw [show u + 2 + 1 = u + 3 by omega] at g2 hAup
  rw [show u + 3 + 1 = u + 4 by omega] at g3
  have s01 := sp_mono (show u ≤ u + 1 by omega)
  have s12 := sp_mono (show u + 1 ≤ u + 2 by omega)
  have s23 := sp_mono (show u + 2 ≤ u + 3 by omega)
  have s2 := sp_two u
  have p1 := sp_pos (u + 1)
  have p0 := sp_pos u
  have hAB : A - B ≤ (sp (u + 1) + sp (u + 2)) / 2 := by linarith
  have hv1 := v_ge_sp (u + 1) (by omega) (by omega)
  have hv2 := v_ge_sp (u + 2) (by omega) (by omega)
  have p2 := sp_pos (u + 2)
  have hy0 : 0 < y := by linarith
  refine ⟨hy0, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have hrl := hr.1
    have h := hr.2 (UInt64.ofNat (r.toNat + 1)) (by rw [word _ (by omega)]; omega)
    have hgr := gap r.toNat (by omega)
    have hrv : value r = v r.toNat := by unfold v; rw [UInt64.ofNat_toNat]
    rw [hrv] at h
    have hm := F64NearestStep.upper_midpoint (v r.toNat) (v (r.toNat + 1)) y
      (by linarith [sp_pos r.toNat]) h
    have m1 := v_mono (show r.toNat ≤ u by omega) (by omega)
    have m2 := v_mono (show r.toNat + 1 ≤ u + 1 by omega) (by omega)
    linarith
  · by_contra hc
    push Not at hc
    have hrl := hr.1
    have h := hr.2 (UInt64.ofNat (r.toNat - 1)) (by rw [word _ (by omega)]; omega)
    have hgr := gap (r.toNat - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hgr
    have hrv : value r = v r.toNat := by unfold v; rw [UInt64.ofNat_toNat]
    rw [hrv] at h
    have hm := F64NearestStep.lower_midpoint (v r.toNat) (v (r.toNat - 1)) y
      (by linarith [sp_pos (r.toNat - 1)]) h
    have m1 := v_mono (show u + 3 ≤ r.toNat - 1 by omega) (by omega)
    have m2 := v_mono (show u + 4 ≤ r.toNat by omega) (by omega)
    linarith

#print axioms steps_pos

/-! ### Signed numbers and rounded words -/

/-- A word rounded to a positive number is a nearest nonnegative word of it. -/
theorem nearest_of_rounded (c : UInt64) (S : ℝ) (hc : Rounded c S) (hS : 0 < S) :
    c.toNat < limit ∧ Nearest S c := by
  obtain ⟨hcf, -, hpos, hnear⟩ := hc
  have hct : c.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hpos hS
  have hcl : c.toNat < limit := by
    rw [limit_eq]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    omega
  have hc0 : 0 ≤ value c := value_nonneg_of_lt c hct
  refine ⟨hcl, hcl, fun v hv => ?_⟩
  have h1 := hnear v
  rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [limit_eq] at hv; omega)), abs_of_nonneg hc0,
    abs_of_pos hS] at h1
  exact h1

/-- The magnitude of a word rounded to a negative number is a nearest nonnegative word of its
magnitude. -/
theorem nearest_of_rounded_neg (c : UInt64) (S : ℝ) (hc : Rounded c S) (hS : S < 0) :
    2 ^ 63 ≤ c.toNat ∧ (Wasm.IEEE64.abs c).toNat < limit ∧
      Nearest (-S) (Wasm.IEEE64.abs c) := by
  obtain ⟨hcf, hneg, -, hnear⟩ := hc
  have hct : 2 ^ 63 ≤ c.toNat := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hneg hS
  have hcl : (Wasm.IEEE64.abs c).toNat < limit := by
    rw [F64UpperWord.abs_toNat, limit_eq]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    have := c.toNat_lt
    omega
  refine ⟨hct, hcl, hcl, fun v hv => ?_⟩
  have h1 := hnear v
  rw [F64UpperWord.value_abs]
  rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [limit_eq] at hv; omega)), abs_of_neg hS] at h1
  exact h1

/-- A number with the same rounded word as zero lies within half the smallest spacing of zero. -/
theorem small_of_zero (c : UInt64) (S : ℝ) (hc : Rounded c S) (h0 : Rounded c 0) :
    |S| ≤ 1 / 2 ^ 1075 := by
  have hz := h0.2.2.2 0
  simp only [F64Magnitude.value_zero, abs_zero, sub_zero, abs_abs] at hz
  have hc0 : |value c| = 0 := le_antisymm hz (abs_nonneg _)
  have h1 := hc.2.2.2 (UInt64.ofNat 1)
  have hv1 : value (UInt64.ofNat 1) = 1 / 2 ^ 1074 := v_one
  rw [hc0, hv1, zero_sub, abs_neg, abs_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 1074)]
    at h1
  rcases le_or_gt |S| (1 / 2 ^ 1074) with h | h
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 ^ 1074 - |S| by linarith)] at h1
    have : (1 : ℝ) / 2 ^ 1075 = 1 / 2 ^ 1074 / 2 := by norm_num
    linarith
  · rw [abs_of_neg (show 1 / 2 ^ 1074 - |S| < 0 by linarith)] at h1
    linarith

theorem hwl_of (w : ℕ) (T : ℝ) (hw : w < limit) (hN : Nearest T (UInt64.ofNat w))
    (hT : T < 2 ^ 1022) : w + 2 < limit := by
  by_contra hc
  rw [limit_eq] at hw hc
  have h := hN.2 (UInt64.ofNat (w - 1)) (by rw [word _ (by omega), limit_eq]; omega)
  have hg := gap (w - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hg
  have hm := F64NearestStep.lower_midpoint (v w) (v (w - 1)) T (by linarith [sp_pos (w - 1)]) h
  have hb := F64PositiveSpacing.boundary_value 2046 (by norm_num) (by norm_num)
  have hmono := v_mono (show 2046 * 2 ^ 52 ≤ w - 1 by omega) (by omega)
  have hmono' := v_mono (show w - 1 ≤ w by omega) (by omega)
  have hv : v (2046 * 2 ^ 52) = 2 ^ 1023 := by
    unfold v; rw [hb]; norm_num
  linarith

/-- **One step for the rounding test**: when two numbers `A > B` more than the smallest spacing apart
have the same rounded word `U`, every number within `3/5 (A - B)` of `[B, A]` has a reference
within one step of `U`. -/
theorem within_of_test (U : UInt64) (A B y : ℝ) (hA : Rounded U A) (hB : Rounded U B)
    (hgap : 1 / 2 ^ 1074 < A - B) (hy1 : B - 3 / 5 * (A - B) ≤ y)
    (hy2 : y ≤ A + 3 / 5 * (A - B)) (hAt : |A| < 2 ^ 1022) (hBt : |B| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 y U := by
  rw [abs_lt] at hAt hBt
  have hthr : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
  have hc : (2 : ℝ) ^ 1022 + 3 / 5 * (2 * 2 ^ 1022) < 2 ^ 1024 - 2 ^ 970 := by norm_num
  rcases lt_or_ge 0 B with hB0 | hB0
  · have hA0 : 0 < A := by linarith
    obtain ⟨hcl, hNA⟩ := nearest_of_rounded U A hA hA0
    obtain ⟨-, hNB⟩ := nearest_of_rounded U B hB hB0
    have hU : UInt64.ofNat U.toNat = U := UInt64.ofNat_toNat
    rw [← hU] at hNA hNB
    have hwl := hwl_of U.toNat A hcl hNA hAt.2
    have hr := (F64NearestEven.roundNearestEven_spec y).1
    obtain ⟨hy0, h1, h2⟩ := steps_pos U.toNat A B y hwl hNA hNB hB0 hgap hy1 hy2 _ hr
    have href := F64PositiveRounding.reference_finite y (by rw [hthr]; linarith)
    exact F64SignedRounding.within_of_nonneg 1 y hy0.le U (by rw [limit_eq] at hcl; omega)
      (by rw [href]; omega) (by rw [href]; omega)
  · rcases lt_or_ge A 0 with hA0 | hA0
    · have hBn : B < 0 := by linarith
      obtain ⟨hct, hcl, hNA⟩ := nearest_of_rounded_neg U A hA hA0
      obtain ⟨-, -, hNB⟩ := nearest_of_rounded_neg U B hB hBn
      have hW : UInt64.ofNat (Wasm.IEEE64.abs U).toNat = Wasm.IEEE64.abs U :=
        UInt64.ofNat_toNat
      rw [← hW] at hNA hNB
      have hwl := hwl_of _ (-B) hcl hNB (by linarith)
      have hr := (F64NearestEven.roundNearestEven_spec (-y)).1
      obtain ⟨hy0, h1, h2⟩ := steps_pos _ (-B) (-A) (-y) hwl hNB hNA (by linarith)
        (by linarith) (by linarith) (by linarith) _ hr
      have href := F64PositiveRounding.reference_finite (-y) (by rw [hthr]; linarith)
      have hctn := F64UpperWord.abs_toNat U
      have hneq : Wasm.IEEE64.negate (Wasm.IEEE64.abs U) = U := by
        apply UInt64.toNat_inj.mp
        rw [F64SignedRounding.negate_toNat]
        have hsa : Wasm.IEEE64.sign (Wasm.IEEE64.abs U) = false := by
          simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, hctn]
          omega
        rw [hsa, ite_eq_right (by simp), hctn]
        have := U.toNat_lt
        omega
      rw [← hneq]
      exact F64SignedRounding.within_of_neg 1 y (by linarith) _ (by rw [limit_eq] at hcl; omega)
        (by rw [href]; omega) (by rw [href]; omega)
    · exfalso
      rcases lt_or_eq_of_le hB0 with hBn | hBz
      · rcases lt_or_eq_of_le hA0 with hAp | hAz
        · have h1 := hA.2.2.1 hAp
          have h2 := hB.2.1 hBn
          rw [h1] at h2
          exact Bool.false_ne_true h2
        · rw [← hAz] at hA
          have := small_of_zero U B hB hA
          rw [abs_of_neg hBn] at this
          rw [← hAz] at hgap
          have : (1 : ℝ) / 2 ^ 1075 < 1 / 2 ^ 1074 := by norm_num
          linarith
      · rw [hBz] at hB
        have := small_of_zero U A hA hB
        rw [abs_of_nonneg hA0] at this
        rw [hBz] at hgap
        have : (1 : ℝ) / 2 ^ 1075 < 1 / 2 ^ 1074 := by norm_num
        linarith

/-- A finite word with the value of a word rounded to a nonzero number is rounded to it too. -/
theorem rounded_congr (c d : UInt64) (S : ℝ) (hc : Rounded c S) (hd : Finite d)
    (hv : value d = value c) (hc0 : value c ≠ 0) : Rounded d S := by
  obtain ⟨-, hneg, hpos, hnear⟩ := hc
  refine ⟨hd, fun hS => ?_, fun hS => ?_, fun w => ?_⟩
  · have hs := hneg hS
    have hcn : value c < 0 := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · exact h
      · rw [F64Exact.sign_of_pos c h] at hs; exact absurd hs Bool.false_ne_true
    by_contra hds
    have := F64TwoSum.value_nonneg_of_sign d (by simpa using hds)
    linarith
  · have hs := hpos hS
    have hcp : 0 < value c := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · have := F64TwoSum.value_nonneg_of_sign c hs; linarith
      · exact h
    exact F64Exact.sign_of_pos d (by rw [hv]; exact hcp)
  · rw [hv]; exact hnear w

/-- **The rounding test of the code**: when `fh + (fl + eps)` and `fh + (fl - eps)` agree, the
first is within one step of every number within `2 eps` of `fh + fl`. -/
theorem round_test (fh fl eps : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (he : Finite eps.toBits) (he0 : 1 / 2 ^ 1000 ≤ value eps.toBits)
    (hfle : |value fl.toBits| ≤ 2 ^ 48 * value eps.toBits)
    (hbig : |value fh.toBits| + 2 ^ 49 * value eps.toBits ≤ 2 ^ 1020)
    (htest : ¬ (fh + (fl + eps) != fh + (fl - eps)) = true) (y : ℝ)
    (hy : |y - (value fh.toBits + value fl.toBits)| ≤ 2 * value eps.toBits) :
    F64SignedRounding.WithinSteps 1 y (fh + (fl + eps)).toBits := by
  set h := value fh.toBits with hh
  set l := value fl.toBits with hl
  set e := value eps.toBits with he'
  have he0' : 0 < e := lt_of_lt_of_le (by positivity) he0
  have hle : |l + e| ≤ (2 ^ 48 + 1) * e := by
    have := abs_add_le l e; rw [abs_of_pos he0'] at this; linarith
  have hlm : |l - e| ≤ (2 ^ 48 + 1) * e := by
    have := abs_sub l e; rw [abs_of_pos he0'] at this; linarith
  have he1 : e ≤ 2 ^ 1020 / 2 ^ 49 := by
    rw [le_div_iff₀ (by positivity)]; linarith [abs_nonneg h]
  have ha := fapprox_add (approx_self _ hfl) (approx_self _ he) |l + e|
    (by rw [add_zero, add_zero]) (by nlinarith)
  have hb := fapprox_sub (approx_self _ hfl) (approx_self _ he) |l - e|
    (by rw [add_zero, add_zero]) (by nlinarith)
  set a := fl + eps with hadef
  set b := fl - eps with hbdef
  have hda : |value a.toBits - (l + e)| ≤ e / 31 := by
    have h1 := ha.2
    simp only [zero_add] at h1
    have : |l + e| / 2 ^ 53 ≤ e / 31 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hdb : |value b.toBits - (l - e)| ≤ e / 31 := by
    have h1 := hb.2
    simp only [zero_add] at h1
    have : |l - e| / 2 ^ 53 ≤ e / 31 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  obtain ⟨hda1, hda2⟩ := abs_le.mp hda
  obtain ⟨hdb1, hdb2⟩ := abs_le.mp hdb
  set A := h + value a.toBits with hA
  set B := h + value b.toBits with hB
  have hAB : 19 / 10 * e ≤ A - B := by linarith
  have hAt : |A| < 2 ^ 1022 := by
    have := abs_add_le h (value a.toBits)
    have h3 : |value a.toBits| ≤ (2 ^ 48 + 1) * e + e / 31 := by
      have := abs_sub_abs_le_abs_sub (value a.toBits) (l + e); linarith
    have : (2 ^ 48 + 1) * e + e / 31 ≤ 2 ^ 49 * e := by nlinarith
    linarith [(by norm_num : (2 : ℝ) ^ 1020 < 2 ^ 1022)]
  have hBt : |B| < 2 ^ 1022 := by
    have := abs_add_le h (value b.toBits)
    have h3 : |value b.toBits| ≤ (2 ^ 48 + 1) * e + e / 31 := by
      have := abs_sub_abs_le_abs_sub (value b.toBits) (l - e); linarith
    have : (2 ^ 48 + 1) * e + e / 31 ≤ 2 ^ 49 * e := by nlinarith
    linarith [(by norm_num : (2 : ℝ) ^ 1020 < 2 ^ 1022)]
  have hu := fapprox_add (approx_self _ hfh) (approx_self _ ha.1) |A| (by rw [add_zero, add_zero])
    (by linarith)
  have hd := fapprox_add (approx_self _ hfh) (approx_self _ hb.1) |B| (by rw [add_zero, add_zero])
    (by linarith)
  set ub := fh + a with hub
  set lb := fh + b with hlb
  have hu2 := hu.2
  have hd2 := hd.2
  simp only [zero_add] at hu2 hd2
  have hbeq : (ub == lb) = true := by
    cases hcmp : (ub == lb)
    · exfalso; apply htest; simp only [bne, hcmp, Bool.not_false]
    · rfl
  have hval := (F64UpperWord.float_beq_iff ub lb hu.1 hd.1).mp hbeq
  have he1074 : (1 : ℝ) / 2 ^ 1074 < 19 / 10 * e := by
    have : (1 : ℝ) / 2 ^ 1074 < 19 / 10 * (1 / 2 ^ 1000) := by norm_num
    linarith
  have hA0 : A ≠ 0 := by
    intro h0
    have hu0 : value ub.toBits = 0 := by
      have h1 : |value ub.toBits - A| ≤ |A| / 2 ^ 53 := hu2
      rw [h0, abs_zero, zero_div, sub_zero] at h1
      exact abs_nonpos_iff.mp h1
    have h2 : |value lb.toBits - B| ≤ |B| / 2 ^ 53 := hd2
    rw [← hval, hu0, zero_sub, abs_neg] at h2
    have : |B| ≤ 0 := by linarith [abs_nonneg B]
    have := abs_nonpos_iff.mp this
    linarith
  have hB0 : B ≠ 0 := by
    intro h0
    have hd0 : value lb.toBits = 0 := by
      have h1 : |value lb.toBits - B| ≤ |B| / 2 ^ 53 := hd2
      rw [h0, abs_zero, zero_div, sub_zero] at h1
      exact abs_nonpos_iff.mp h1
    have h2 : |value ub.toBits - A| ≤ |A| / 2 ^ 53 := hu2
    rw [hval, hd0, zero_sub, abs_neg] at h2
    have : |A| ≤ 0 := by linarith [abs_nonneg A]
    have := abs_nonpos_iff.mp this
    linarith
  have hRA := F64RoundNearest.add_rounded fh.toBits a.toBits hfh ha.1 hA0 (by linarith)
  have hRB := F64RoundNearest.add_rounded fh.toBits b.toBits hfh hb.1 hB0 (by linarith)
  rw [← F64Bits.toBits_add] at hRA hRB
  have hlb0 : value lb.toBits ≠ 0 := by
    intro h0
    have h2 : |value lb.toBits - B| ≤ |B| / 2 ^ 53 := hd2
    rw [h0, zero_sub, abs_neg] at h2
    have : |B| ≤ 0 := by linarith [abs_nonneg B]
    exact hB0 (abs_nonpos_iff.mp this)
  have hRB' := rounded_congr lb.toBits ub.toBits B hRB hu.1 hval hlb0
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  exact within_of_test ub.toBits A B y hRA hRB' (by linarith) (by linarith) (by linarith) hAt hBt

#print axioms within_of_test
#print axioms round_test

end Verified.Examples.LgammaRoundTest
