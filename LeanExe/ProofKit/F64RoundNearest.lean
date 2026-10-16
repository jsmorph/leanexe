import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64NearestSum
import LeanExe.ProofKit.F64PackingFinite
import LeanExe.ProofKit.F64Approx
import LeanExe.ProofKit.F64SignedRounding
import LeanExe.ProofKit.F64UpperWord
import LeanExe.ProofKit.F64Exact
import Mathlib.Data.Int.Log

/-!
A sum or difference of finite words rounds to a nearest word of its exact value: no word has a
magnitude closer to the exact magnitude.  Nearest words of two numbers that lie at or above the
start of binade `a` and closer together than one spacing of that binade are at most one step
apart, so `within_one_of_rounded` gives one step for a rounded sum whose exact value is within one
spacing of `y`, without charging the final rounding.  `within_one_of_rounded_rel` states the same
for an exact value within the fraction `1/(2 ^ 53 + 1)` of `y`.
-/

namespace LeanExe.ProofKit.F64RoundNearest
open CodeLib.IEEE64 F64NearestNonnegative F64Approx

set_option exponentiation.threshold 4096

/-- `c` is finite, carries the sign of a nonzero `S`, and no word has a magnitude closer to
`|S|`. -/
def Rounded (c : UInt64) (S : ℝ) : Prop :=
  Finite c ∧ (S < 0 → Wasm.IEEE64.sign c = true) ∧ (0 < S → Wasm.IEEE64.sign c = false) ∧
    ∀ v : UInt64, abs (|value c| - |S|) ≤ abs (|value v| - |S|)

theorem abs_value (v : UInt64) :
    |value v| = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
  rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← natAbs_scaledValue,
    ← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

theorem magnitude_below (v : UInt64) (g : ℕ) (hg : 1 ≤ g)
    (h : Wasm.IEEE64.scaledMagnitude v < 2 ^ (52 + g)) :
    Wasm.IEEE64.scaledMagnitude v + 2 ^ (g - 1) ≤ 2 ^ (52 + g) := by
  have h2 : 2 ^ (52 + g) = 2 ^ (g - 1) * 2 ^ 53 := by
    rw [← pow_add]
    congr 1
    omega
  have hp : 0 < 2 ^ (g - 1) := by positivity
  by_cases hl : 2 ^ (52 + (g - 1)) ≤ Wasm.IEEE64.scaledMagnitude v
  · obtain ⟨q, hq⟩ := F64NearestSum.magnitude_dvd v (g - 1) hl
    rw [hq, h2] at h ⊢
    have hq53 : q < 2 ^ 53 := lt_of_mul_lt_mul_left h (Nat.zero_le _)
    have : q + 1 ≤ 2 ^ 53 := hq53
    calc 2 ^ (g - 1) * q + 2 ^ (g - 1) = 2 ^ (g - 1) * (q + 1) := by ring
      _ ≤ 2 ^ (g - 1) * 2 ^ 53 := Nat.mul_le_mul_left _ this
  · have h3 : 2 ^ (52 + (g - 1)) = 2 ^ (g - 1) * 2 ^ 52 := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : 2 ^ (g - 1) * 2 ^ 52 + 2 ^ (g - 1) ≤ 2 ^ (g - 1) * 2 ^ 53 := by
      have : 2 ^ 52 + 1 ≤ 2 ^ 53 := by norm_num
      calc 2 ^ (g - 1) * 2 ^ 52 + 2 ^ (g - 1) = 2 ^ (g - 1) * (2 ^ 52 + 1) := by ring
        _ ≤ 2 ^ (g - 1) * 2 ^ 53 := Nat.mul_le_mul_left _ this
    omega

theorem add_rounded (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h0 : value a + value b ≠ 0) (hmax : |value a + value b| < 2 ^ 1023) :
    Rounded (Wasm.IEEE64.add a b) (value a + value b) := by
  set S := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b with hSdef
  have hSv : value a + value b = (S : ℝ) / 2 ^ 1074 := by
    simp only [value, hSdef]
    push_cast
    ring
  have hS0 : S ≠ 0 := by
    intro h
    apply h0
    rw [hSv, h]
    simp
  have hcast : |(S : ℝ)| = (S.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hn : S.natAbs < 2 ^ 2097 := by
    rw [hSv, abs_div, abs_of_pos h2, div_lt_iff₀ h2, hcast, ← pow_add] at hmax
    exact_mod_cast hmax
  have heq : Wasm.IEEE64.add a b =
      Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs := by
    have hne : (S == 0) = false := by simpa using hS0
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hSdef, hne]
  obtain ⟨hf, hmag, hsign⟩ := F64Packing.pack_spec (decide (S < 0)) S.natAbs hn
  rw [heq]
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro hneg
    rw [hsign]
    rw [hSv] at hneg
    have : (S : ℝ) < 0 := by
      by_contra hc
      push Not at hc
      have := div_nonneg hc h2.le
      linarith
    simpa using (by exact_mod_cast this : S < 0)
  · intro hpos
    rw [hsign]
    rw [hSv] at hpos
    have : (0 : ℝ) < S := by
      by_contra hc
      push Not at hc
      have := div_nonpos_of_nonpos_of_nonneg hc h2.le
      linarith
    simpa using (by exact_mod_cast this.le : 0 ≤ S)
  · intro v
    rw [abs_value, abs_value v, hmag, hSv, abs_div, abs_of_pos h2, hcast,
      ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos h2]
    exact div_le_div_of_nonneg_right (F64NearestSum.rounded_nearest _ v) h2.le

theorem sub_rounded (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h0 : value a - value b ≠ 0) (hmax : |value a - value b| < 2 ^ 1023) :
    Rounded (Wasm.IEEE64.sub a b) (value a - value b) := by
  have hn := F64Magnitude.negate_value b hb
  have h := add_rounded a (Wasm.IEEE64.negate b) ha hn.1 (by rw [hn.2, ← sub_eq_add_neg]; exact h0)
    (by rw [hn.2, ← sub_eq_add_neg]; exact hmax)
  rw [hn.2, ← sub_eq_add_neg] at h
  exact h

theorem value_nonneg_of_lt (v : UInt64) (h : v.toNat < 2 ^ 63) : 0 ≤ value v := by
  have hs : Wasm.IEEE64.sign v = false := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using h
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false]
  positivity

/-- A nearest word of a number at or above the start of binade `a` lies in binade `a` or above. -/
theorem nearest_above (t : ℝ) (w : UInt64) (hw : Nearest t w) (a : ℕ) (ha : a < 2047)
    (ht : value (UInt64.ofNat (a * 2 ^ 52)) ≤ t) : a * 2 ^ 52 ≤ w.toNat := by
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hB : (UInt64.ofNat (a * 2 ^ 52)).toNat = a * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  by_contra hc
  push Not at hc
  have hlt := F64PositiveOrder.value_strict (left := w) (right := UInt64.ofNat (a * 2 ^ 52))
    (by rw [hB]; omega) (by rw [hB]; exact hc)
  have hd := hw.2 (UInt64.ofNat (a * 2 ^ 52)) (by rw [hB, hlim]; omega)
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hd
  linarith

/-- Nearest words of two numbers at or above the start of binade `a`, closer than one spacing of
that binade, are at most one step apart. -/
theorem steps_of_nearest (S y : ℝ) (w r : UInt64) (hw : Nearest S w) (hr : Nearest y r)
    (a : ℕ) (ha : a < 2047) (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ S)
    (hy : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y)
    (h : |S - y| < (2 : ℝ) ^ (a - 1) / 2 ^ 1074) :
    w.toNat ≤ r.toNat + 1 ∧ r.toNat ≤ w.toNat + 1 := by
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hwa := nearest_above S w hw a ha hS
  have hra := nearest_above y r hr a ha hy
  have hw1 := hw.1
  have hr1 := hr.1
  have word (n : ℕ) (hn : n < 2 ^ 63) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have habs := abs_lt.mp h
  have habs_l := habs.1
  have habs_r := habs.2
  constructor
  · by_contra hc
    push Not at hc
    have g1 := F64FullStep.gap_lower r.toNat a hra (by rw [hlim] at hw1; omega)
    have g2 := F64FullStep.gap_lower (r.toNat + 1) a (by omega) (by rw [hlim] at hw1; omega)
    simp only [UInt64.ofNat_toNat] at g1
    have hle : value (UInt64.ofNat (r.toNat + 1 + 1)) ≤ value w :=
      (F64PositiveOrder.value_le_iff (by rw [word _ (by rw [hlim] at hw1; omega)]; omega)
        (by rw [hlim] at hw1; omega)).mpr (by rw [word _ (by rw [hlim] at hw1; omega)]; omega)
    have hpos : (0 : ℝ) < 2 ^ (a - 1) / 2 ^ 1074 := by positivity
    have hpw : value (UInt64.ofNat (r.toNat + 1)) < value w := by linarith
    have hm1 := F64NearestStep.lower_midpoint (value w) (value (UInt64.ofNat (r.toNat + 1))) S
      hpw (hw.2 _ (by rw [word _ (by rw [hlim] at hw1; omega), hlim]; omega))
    have hm2 := F64NearestStep.upper_midpoint (value r) (value (UInt64.ofNat (r.toNat + 1))) y
      (by linarith) (hr.2 _ (by rw [word _ (by rw [hlim] at hw1; omega), hlim]; omega))
    linarith
  · by_contra hc
    push Not at hc
    have g1 := F64FullStep.gap_lower w.toNat a hwa (by rw [hlim] at hr1; omega)
    have g2 := F64FullStep.gap_lower (w.toNat + 1) a (by omega) (by rw [hlim] at hr1; omega)
    simp only [UInt64.ofNat_toNat] at g1
    have hle : value (UInt64.ofNat (w.toNat + 1 + 1)) ≤ value r :=
      (F64PositiveOrder.value_le_iff (by rw [word _ (by rw [hlim] at hr1; omega)]; omega)
        (by rw [hlim] at hr1; omega)).mpr (by rw [word _ (by rw [hlim] at hr1; omega)]; omega)
    have hpos : (0 : ℝ) < 2 ^ (a - 1) / 2 ^ 1074 := by positivity
    have hpr : value (UInt64.ofNat (w.toNat + 1)) < value r := by linarith
    have hm1 := F64NearestStep.lower_midpoint (value r) (value (UInt64.ofNat (w.toNat + 1))) y
      hpr (hr.2 _ (by rw [word _ (by rw [hlim] at hr1; omega), hlim]; omega))
    have hm2 := F64NearestStep.upper_midpoint (value w) (value (UInt64.ofNat (w.toNat + 1))) S
      (by linarith) (hw.2 _ (by rw [word _ (by rw [hlim] at hr1; omega), hlim]; omega))
    linarith

/-- A rounded word whose exact value lies within one spacing of binade `a` from `y`, both at or
above the start of that binade in magnitude, is within one step of the reference of `y`. -/
theorem within_one_of_rounded (c : UInt64) (S y : ℝ) (hc : Rounded c S) (a : ℕ) (ha1 : 1 ≤ a)
    (ha : a < 2047) (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ |S|)
    (hy : value (UInt64.ofNat (a * 2 ^ 52)) ≤ |y|)
    (h : |S - y| < (2 : ℝ) ^ (a - 1) / 2 ^ 1074) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 1 y c := by
  obtain ⟨hcf, hneg, hpos, hnear⟩ := hc
  have hB := F64PositiveSpacing.boundary_value a ha1 (by omega)
  have hBh : (2 : ℝ) ^ (a - 1) / 2 ^ 1074 < value (UInt64.ofNat (a * 2 ^ 52)) := by
    rw [hB]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := lt_of_le_of_lt (by positivity) hBh
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hcl : (Wasm.IEEE64.abs c).toNat < limit := by
    rw [F64UpperWord.abs_toNat, hlim]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    have := c.toNat_lt
    omega
  have hN : Nearest |S| (Wasm.IEEE64.abs c) := by
    refine ⟨hcl, fun v hv => ?_⟩
    have h1 := hnear v
    rw [F64UpperWord.value_abs]
    rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [hlim] at hv; omega))] at h1
    exact h1
  have hyo : |y| < F64PositiveRounding.overflowThreshold := by
    have : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
    rw [this]
    have : (2 : ℝ) ^ 1023 ≤ 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  have hr := F64PositiveRounding.reference_finite |y| hyo
  have hrN : Nearest |y| (F64PositiveRounding.roundNearestEven |y|) := by
    rw [hr]
    exact (F64NearestEven.roundNearestEven_spec |y|).1
  have hhS : abs (|S| - |y|) < (2 : ℝ) ^ (a - 1) / 2 ^ 1074 :=
    lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub S y) h
  have hst := steps_of_nearest |S| |y| _ _ hN hrN a ha hS hy hhS
  have hrle := F64SignedRounding.positive_reference_le |y|
  have hctn := F64UpperWord.abs_toNat c
  rcases lt_or_gt_of_ne (show y ≠ 0 by intro h0; rw [h0, abs_zero] at hy; linarith) with hy0 | hy0
  · -- negative: `S` is negative too
    have hS0 : S < 0 := by
      by_contra hc
      push Not at hc
      rw [abs_of_nonneg hc] at hS
      rw [abs_of_neg hy0] at hy
      obtain ⟨hab_l, hab_r⟩ := abs_lt.mp h
      set B := value (UInt64.ofNat (a * 2 ^ 52))
      set hh := (2 : ℝ) ^ (a - 1) / 2 ^ 1074
      linarith
    have hsc := hneg hS0
    have hct : 2 ^ 63 ≤ c.toNat := by
      simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hsc
    have hneq : Wasm.IEEE64.negate (Wasm.IEEE64.abs c) = c := by
      apply UInt64.toNat_inj.mp
      rw [F64SignedRounding.negate_toNat]
      have hsa : Wasm.IEEE64.sign (Wasm.IEEE64.abs c) = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, hctn]
        omega
      rw [hsa, if_neg (by simp), hctn]
      have := c.toNat_lt
      omega
    rw [← hneq]
    rw [abs_of_neg hy0] at hst hrle
    exact F64SignedRounding.within_of_neg 1 y hy0 _ (by rw [hlim] at hcl; omega) hst.1 hst.2
  · have hS0 : 0 < S := by
      by_contra hc
      push Not at hc
      rw [abs_of_nonpos hc] at hS
      rw [abs_of_pos hy0] at hy
      obtain ⟨hab_l, hab_r⟩ := abs_lt.mp h
      set B := value (UInt64.ofNat (a * 2 ^ 52))
      set hh := (2 : ℝ) ^ (a - 1) / 2 ^ 1074
      linarith
    have hsc := hpos hS0
    have hct : c.toNat < 2 ^ 63 := by
      simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hsc
    have heq : Wasm.IEEE64.abs c = c := by
      apply UInt64.toNat_inj.mp
      rw [hctn]
      omega
    rw [heq] at hst hcl
    rw [abs_of_pos hy0] at hst
    exact F64SignedRounding.within_of_nonneg 1 y hy0.le c (by rw [hlim] at hcl; omega)
      hst.1 hst.2

/-- The binade of a number between `2 ^ -1021` and `2 ^ 1022`. -/
theorem binade_of_real (t : ℝ) (ht : 1 / 2 ^ 1021 ≤ t) (ht2 : t < 2 ^ 1022) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ 2044 ∧ value (UInt64.ofNat (n * 2 ^ 52)) ≤ t ∧
      t < 2 * value (UInt64.ofNat (n * 2 ^ 52)) := by
  have htp : 0 < t := lt_of_lt_of_le (by positivity) ht
  set L := Int.log 2 t with hL
  have hlo : (2 : ℝ) ^ L ≤ t := by simpa using Int.zpow_log_le_self (b := 2) (by norm_num) htp
  have hhi : t < (2 : ℝ) ^ (L + 1) := by
    simpa using Int.lt_zpow_succ_log_self (b := 2) (by norm_num) t
  have hL1 : -1021 ≤ L := by
    by_contra hc
    push Not at hc
    have h3 : (2 : ℝ) ^ (L + 1) ≤ 2 ^ (-1021 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [show (2 : ℝ) ^ (-1021 : ℤ) = 1 / 2 ^ 1021 by norm_num] at h3
    exact absurd (lt_of_lt_of_le hhi h3) (not_lt.mpr ht)
  have hL2 : L ≤ 1021 := by
    by_contra hc
    push Not at hc
    have : (2 : ℝ) ^ (1022 : ℤ) ≤ 2 ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (1022 : ℤ) = 2 ^ 1022 := by norm_num
    linarith
  refine ⟨(L + 1023).toNat, by omega, by omega, ?_⟩
  have hB := F64PositiveSpacing.boundary_value (L + 1023).toNat (by omega) (by omega)
  have hBz : value (UInt64.ofNat ((L + 1023).toNat * 2 ^ 52)) = (2 : ℝ) ^ L := by
    rw [hB, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num)]
    congr 1
    push_cast
    omega
  rw [hBz]
  refine ⟨hlo, ?_⟩
  rw [zpow_add_one₀ (by norm_num)] at hhi
  linarith

/-- `within_one_of_rounded` for an exact value within the fraction `1/(2 ^ 53 + 1)` of `y`. -/
theorem within_one_of_rounded_rel (c : UInt64) (S y : ℝ) (hc : Rounded c S) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (2 ^ 53 + 1)) (h : |S - y| ≤ ρ * |y|)
    (hy : 1 / 2 ^ 1021 ≤ |y|) (hyt : |y| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 y c := by
  obtain ⟨n, hn2, hn, hBy, hyB⟩ := binade_of_real |y| hy hyt
  have hB := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  have hBm := F64PositiveSpacing.boundary_value (n - 1) (by omega) (by omega)
  set h1 := (2 : ℝ) ^ (n - 1 - 1) / 2 ^ 1074 with hh1
  have hh1p : 0 < h1 := by positivity
  have hBn : value (UInt64.ofNat (n * 2 ^ 52)) = 2 ^ 53 * h1 := by
    rw [hB, hh1, show n + 51 = 53 + (n - 1 - 1) by omega, pow_add]
    ring
  have hBn1 : value (UInt64.ofNat ((n - 1) * 2 ^ 52)) = 2 ^ 52 * h1 := by
    rw [hBm, hh1, show n - 1 + 51 = 52 + (n - 1 - 1) by omega, pow_add]
    ring
  have hhn : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 = 2 * h1 := by
    rw [hh1, ← mul_div_assoc, ← pow_succ', show n - 1 - 1 + 1 = n - 1 by omega]
  have hρ2 : ρ * (2 ^ 53 + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hρ
    linarith
  have hρ53 : ρ * 2 ^ 53 < 1 := by
    rcases eq_or_lt_of_le hρ0 with h0 | h0
    · rw [← h0]
      norm_num
    · linarith
  have htri : |y| - |S - y| ≤ |S| := by
    have := abs_sub_abs_le_abs_sub y S
    rw [abs_sub_comm] at this
    linarith
  have hρy : 0 ≤ ρ * |y| := by positivity
  have hyt' : |y| < 2 ^ 1023 := hyt.trans (by norm_num)
  by_cases hS : value (UInt64.ofNat (n * 2 ^ 52)) ≤ |S|
  · refine within_one_of_rounded c S y hc n (by omega) (by omega) hS hBy ?_ hyt'
    rw [hhn]
    have h2 : ρ * |y| ≤ ρ * (2 ^ 54 * h1) := by
      apply mul_le_mul_of_nonneg_left _ hρ0
      rw [hBn] at hyB
      linarith
    nlinarith
  · push Not at hS
    refine within_one_of_rounded c S y hc (n - 1) (by omega) (by omega) ?_ ?_ ?_ hyt'
    · rw [hBn1]
      rw [hBn] at hBy
      have : ρ * |y| ≤ 1 / 2 * |y| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have : (1 : ℝ) / (2 ^ 53 + 1) ≤ 1 / 2 := by norm_num
        linarith
      nlinarith
    · rw [hBn1]
      rw [hBn] at hBy
      nlinarith
    · rw [show n - 1 - 1 = n - 1 - 1 from rfl, ← hh1]
      rw [hBn] at hS
      have h3 : ρ * |y| * 2 ^ 53 ≤ |y| - ρ * |y| := by nlinarith
      nlinarith

theorem fapprox_sum_close {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (y : ℝ) :
    |value a.toBits + value b.toBits - y| ≤ ea + eb + |va + vb - y| := by
  have h := abs_add_le (value a.toBits - va + (value b.toBits - vb)) (va + vb - y)
  rw [show value a.toBits - va + (value b.toBits - vb) + (va + vb - y) =
    value a.toBits + value b.toBits - y by ring] at h
  have := abs_add_le (value a.toBits - va) (value b.toBits - vb)
  linarith [ha.2, hb.2]

theorem fapprox_diff_close {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (y : ℝ) :
    |value a.toBits - value b.toBits - y| ≤ ea + eb + |va - vb - y| := by
  have h := abs_add_le (value a.toBits - va - (value b.toBits - vb)) (va - vb - y)
  rw [show value a.toBits - va - (value b.toBits - vb) + (va - vb - y) =
    value a.toBits - value b.toBits - y by ring] at h
  have := abs_sub (value a.toBits - va) (value b.toBits - vb)
  linarith [ha.2, hb.2]

/-- A rounded float sum whose exact value lies within `E` of `y`, below one spacing of binade
`n`, with `|y|` at least `E` above the start of that binade. -/
theorem add_within {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea) (hb : FApprox b vb eb)
    (y E : ℝ) (hE : ea + eb + |va + vb - y| ≤ E) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2047)
    (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ |y|) (hEh : E < (2 : ℝ) ^ (n - 1) / 2 ^ 1074)
    (hyt : |y| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 y (a + b).toBits := by
  have hc := fapprox_sum_close ha hb y
  have hB := F64PositiveSpacing.boundary_value n hn1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (n * 2 ^ 52)) := by rw [hB]; positivity
  have htri : |y| - |value a.toBits + value b.toBits - y| ≤ |value a.toBits + value b.toBits| := by
    have := abs_sub_abs_le_abs_sub y (value a.toBits + value b.toBits)
    rw [abs_sub_comm y] at this
    linarith
  have htri2 : |value a.toBits + value b.toBits| ≤ |y| + |value a.toBits + value b.toBits - y| := by
    have := abs_sub_abs_le_abs_sub (value a.toBits + value b.toBits) y
    linarith
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hc.trans hE)
  rw [F64Bits.toBits_add]
  refine within_one_of_rounded _ _ y (add_rounded _ _ ha.1 hb.1 ?_ ?_) n hn1 hn ?_ ?_ ?_
    (hyt.trans (by norm_num))
  · intro h0
    have := hc.trans hE
    rw [h0, zero_sub, abs_neg] at this
    linarith
  · have : (E : ℝ) < 2 ^ 1022 := by
      have : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 ≤ 2 ^ 2045 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      have h2 : (2 : ℝ) ^ 2045 / 2 ^ 1074 = 2 ^ 971 := by norm_num
      have h3 : (2 : ℝ) ^ 971 ≤ 2 ^ 1022 := by norm_num
      linarith
    have h4 : (2 : ℝ) ^ 1022 + 2 ^ 1022 = 2 ^ 1023 := by norm_num
    linarith
  · linarith
  · linarith
  · linarith

theorem sub_within {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea) (hb : FApprox b vb eb)
    (y E : ℝ) (hE : ea + eb + |va - vb - y| ≤ E) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2047)
    (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ |y|) (hEh : E < (2 : ℝ) ^ (n - 1) / 2 ^ 1074)
    (hyt : |y| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 y (a - b).toBits := by
  have hc := fapprox_diff_close ha hb y
  have hB := F64PositiveSpacing.boundary_value n hn1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (n * 2 ^ 52)) := by rw [hB]; positivity
  have htri : |y| - |value a.toBits - value b.toBits - y| ≤ |value a.toBits - value b.toBits| := by
    have := abs_sub_abs_le_abs_sub y (value a.toBits - value b.toBits)
    rw [abs_sub_comm y] at this
    linarith
  have htri2 : |value a.toBits - value b.toBits| ≤ |y| + |value a.toBits - value b.toBits - y| := by
    have := abs_sub_abs_le_abs_sub (value a.toBits - value b.toBits) y
    linarith
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hc.trans hE)
  rw [F64Bits.toBits_sub]
  refine within_one_of_rounded _ _ y (sub_rounded _ _ ha.1 hb.1 ?_ ?_) n hn1 hn ?_ ?_ ?_
    (hyt.trans (by norm_num))
  · intro h0
    have := hc.trans hE
    rw [h0, zero_sub, abs_neg] at this
    linarith
  · have : (E : ℝ) < 2 ^ 1022 := by
      have : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 ≤ 2 ^ 2045 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      have h2 : (2 : ℝ) ^ 2045 / 2 ^ 1074 = 2 ^ 971 := by norm_num
      have h3 : (2 : ℝ) ^ 971 ≤ 2 ^ 1022 := by norm_num
      linarith
    have h4 : (2 : ℝ) ^ 1022 + 2 ^ 1022 = 2 ^ 1023 := by norm_num
    linarith
  · linarith
  · linarith
  · linarith

/-- A rounded float difference whose exact value lies within the fraction `ρ` of `y`. -/
theorem sub_within_rel {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (y ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (2 ^ 53 + 1))
    (hE : ea + eb + |va - vb - y| ≤ ρ * |y|) (hy : 1 / 2 ^ 1021 ≤ |y|) (hyt : |y| < 2 ^ 1021) :
    F64SignedRounding.WithinSteps 1 y (a - b).toBits := by
  have hc := fapprox_diff_close ha hb y
  have htri : |y| - |value a.toBits - value b.toBits - y| ≤ |value a.toBits - value b.toBits| := by
    have := abs_sub_abs_le_abs_sub y (value a.toBits - value b.toBits)
    rw [abs_sub_comm y] at this
    linarith
  have htri2 : |value a.toBits - value b.toBits| ≤ |y| + |value a.toBits - value b.toBits - y| := by
    have := abs_sub_abs_le_abs_sub (value a.toBits - value b.toBits) y
    linarith
  have hρ1 : ρ ≤ 1 / 2 := hρ.trans (by norm_num)
  have hy0 : 0 < |y| := lt_of_lt_of_le (by positivity) hy
  rw [F64Bits.toBits_sub]
  refine within_one_of_rounded_rel _ _ y (sub_rounded _ _ ha.1 hb.1 ?_ ?_) ρ hρ0 hρ
    (hc.trans hE) hy (hyt.trans (by norm_num))
  · intro h0
    have := hc.trans hE
    rw [h0, zero_sub, abs_neg] at this
    nlinarith [mul_le_mul_of_nonneg_right hρ1 (abs_nonneg y)]
  · have : ρ * |y| ≤ |y| := by nlinarith
    have h4 : (2 : ℝ) ^ 1021 + 2 ^ 1021 < 2 ^ 1023 := by norm_num
    linarith

/-- A rounded float sum whose exact value lies within the fraction `ρ` of `y`. -/
theorem add_within_rel {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (y ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (2 ^ 53 + 1))
    (hE : ea + eb + |va + vb - y| ≤ ρ * |y|) (hy : 1 / 2 ^ 1021 ≤ |y|) (hyt : |y| < 2 ^ 1021) :
    F64SignedRounding.WithinSteps 1 y (a + b).toBits := by
  have hc := fapprox_sum_close ha hb y
  have htri2 : |value a.toBits + value b.toBits| ≤ |y| + |value a.toBits + value b.toBits - y| := by
    have := abs_sub_abs_le_abs_sub (value a.toBits + value b.toBits) y
    linarith
  have hρ1 : ρ ≤ 1 / 2 := hρ.trans (by norm_num)
  have hy0 : 0 < |y| := lt_of_lt_of_le (by positivity) hy
  rw [F64Bits.toBits_add]
  refine within_one_of_rounded_rel _ _ y (add_rounded _ _ ha.1 hb.1 ?_ ?_) ρ hρ0 hρ
    (hc.trans hE) hy (hyt.trans (by norm_num))
  · intro h0
    have := hc.trans hE
    rw [h0, zero_sub, abs_neg] at this
    nlinarith [mul_le_mul_of_nonneg_right hρ1 (abs_nonneg y)]
  · have : ρ * |y| ≤ |y| := by nlinarith
    have h4 : (2 : ℝ) ^ 1021 + 2 ^ 1021 < 2 ^ 1023 := by norm_num
    linarith

/-- A rounded word of a number at or above the start of binade `a` lies at or above it too. -/
theorem rounded_ge (c : UInt64) (S : ℝ) (hc : Rounded c S) (a : ℕ) (ha1 : 1 ≤ a) (ha : a < 2047)
    (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ S) : value (UInt64.ofNat (a * 2 ^ 52)) ≤ value c := by
  obtain ⟨hcf, -, hpos, hnear⟩ := hc
  have hB := F64PositiveSpacing.boundary_value a ha1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by rw [hB]; positivity
  have hS0 : 0 < S := lt_of_lt_of_le hB0 hS
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hct : c.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hpos hS0
  have hcl : c.toNat < limit := by
    rw [hlim]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    omega
  have hc0 : 0 ≤ value c := value_nonneg_of_lt c hct
  have hN : Nearest S c := by
    refine ⟨hcl, fun v hv => ?_⟩
    have h1 := hnear v
    rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [hlim] at hv; omega)), abs_of_nonneg hc0,
      abs_of_pos hS0] at h1
    exact h1
  have hab := nearest_above S c hN a ha hS
  have hBt : (UInt64.ofNat (a * 2 ^ 52)).toNat = a * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  exact (F64PositiveOrder.value_le_iff (by rw [hBt]; omega) hct).mpr (by rw [hBt]; exact hab)

#print axioms add_rounded
#print axioms sub_rounded
#print axioms within_one_of_rounded
#print axioms within_one_of_rounded_rel
#print axioms add_within
#print axioms sub_within
#print axioms sub_within_rel
#print axioms rounded_ge
#print axioms add_within_rel

end LeanExe.ProofKit.F64RoundNearest
