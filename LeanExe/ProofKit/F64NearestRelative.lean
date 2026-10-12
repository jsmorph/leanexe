import LeanExe.ProofKit.F64NearestSteps

/-!
Step counts from relative distances.  `steps_rel` is the one-step criterion of
`F64NearestSteps.steps_relative` with the binade of `y` found from `Nat.log2`.  `steps_rel_k`
chains it: if `abs(s - y) ≤ k (1 - 2 ^ -50) u min(y, s)`, the points `y + j (s - y) / k` split the
distance into `k` parts of one step each.  `within_rel_k` turns the count into `WithinSteps k`, and
`within_rel_of` accepts the simpler bound `abs(s - y) ≤ (k - 1/16) u y`.
-/

namespace LeanExe.ProofKit.F64NearestRelative
open CodeLib.IEEE64 F64NearestNonnegative

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem binade_index (L : Nat) (h1 : 52 ≤ L) (h2 : L < 2098) :
    1 ≤ L - 51 ∧ L - 51 ≤ 2046 ∧ L - 51 + 51 = L ∧ L - 51 + 52 = L + 1 := by
  omega

/-- The binade of a normal `y` below the overflow threshold. -/
theorem binade_of (y : ℝ) (hy : 1 / 2 ^ 1022 ≤ y)
    (hyt : y < F64PositiveRounding.overflowThreshold) :
    ∃ e : Nat, 1 ≤ e ∧ e ≤ 2046 ∧ (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ y ∧
      y < (2 : ℝ) ^ (e + 52) / 2 ^ 1074 := by
  have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hyp : (0 : ℝ) ≤ y := le_trans (by positivity) hy
  have hy0 : 0 ≤ y * 2 ^ 1074 := by positivity
  have hn1 : (⌊y * 2 ^ 1074⌋₊ : ℝ) ≤ y * 2 ^ 1074 := Nat.floor_le hy0
  have hn2 : y * 2 ^ 1074 < ⌊y * 2 ^ 1074⌋₊ + 1 := Nat.lt_floor_add_one _
  set n := ⌊y * 2 ^ 1074⌋₊
  have hn52 : 2 ^ 52 ≤ n := by
    apply Nat.le_floor
    have := mul_le_mul_of_nonneg_right hy h74.le
    have h : (1 : ℝ) / 2 ^ 1022 * 2 ^ 1074 = 2 ^ 52 := by norm_num
    push_cast
    linarith
  have hth : F64PositiveRounding.overflowThreshold < 2 ^ 1024 := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  have hyb : y * 2 ^ 1074 < 2 ^ 2098 := by
    have := mul_lt_mul_of_pos_right (hyt.trans hth) h74
    have h : (2 : ℝ) ^ 1024 * 2 ^ 1074 = 2 ^ 2098 := by norm_num
    linarith
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.two_pow_pos 52) hn52)
  have hL52 : 52 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn52
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  set L := Nat.log2 n
  have hL1' : (2 : ℝ) ^ L ≤ n := by exact_mod_cast hL1
  have hL2' : (n : ℝ) + 1 ≤ 2 ^ (L + 1) := by exact_mod_cast hL2
  have hL : L < 2098 := by
    by_contra h
    have : (2 : ℝ) ^ 2098 ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (not_lt.mp h)
    linarith
  obtain ⟨he1, he2, he3, he4⟩ := binade_index L hL52 hL
  refine ⟨L - 51, he1, he2, ?_, ?_⟩
  · rw [he3, div_le_iff₀ h74]
    linarith
  · rw [he4, lt_div_iff₀ h74]
    linarith

/-- One step between nearest words of `y` and `s` at relative distance below `(1 - 2 ^ -50) u`. -/
theorem steps_rel (y s : ℝ) (c w : UInt64) (hy : 1 / 2 ^ 1022 ≤ y)
    (hyt : y < F64PositiveRounding.overflowThreshold) (hc : Nearest s c) (hw : Nearest y w)
    (hr : |s - y| ≤ (1 - 1 / 2 ^ 50) * u * y) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  obtain ⟨e, he1, he2, hlo, hhi⟩ := binade_of y hy hyt
  exact F64NearestSteps.steps_relative y s c w e he1 he2 hlo hhi hc hw hr

/-- `k` steps between nearest words of `y` and `s` at distance below `k (1 - 2 ^ -50) u
min(y, s)`. -/
theorem steps_rel_k (k : Nat) (hk : 1 ≤ k) : ∀ (y s : ℝ) (c w : UInt64),
    1 / 2 ^ 1022 ≤ min y s → max y s < F64PositiveRounding.overflowThreshold →
    Nearest s c → Nearest y w →
    |s - y| ≤ k * ((1 - 1 / 2 ^ 50) * u) * min y s →
    c.toNat ≤ w.toNat + k ∧ w.toNat ≤ c.toNat + k := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro y s c w hmin hmax hc hw hr
    have hy : 1 / 2 ^ 1022 ≤ y := hmin.trans (min_le_left _ _)
    have hyt : y < F64PositiveRounding.overflowThreshold := (le_max_left _ _).trans_lt hmax
    refine steps_rel y s c w hy hyt hc hw (hr.trans ?_)
    have hd : (0 : ℝ) ≤ (1 - 1 / 2 ^ 50) * u := by
      have : (0 : ℝ) ≤ u := by norm_num [unitRoundoff64]
      have : (0 : ℝ) ≤ 1 - 1 / 2 ^ 50 := by norm_num
      positivity
    push_cast
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hd
  | succ k hk ih =>
    intro y s c w hmin hmax hc hw hr
    set δ := (1 - 1 / 2 ^ 50) * u with hδ
    have hδ0 : 0 ≤ δ := by
      have : (0 : ℝ) ≤ u := by norm_num [unitRoundoff64]
      have : (0 : ℝ) ≤ 1 - 1 / 2 ^ 50 := by norm_num
      positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    set y1 := y + (s - y) / ((k : ℝ) + 1) with hy1
    obtain ⟨w1, hw1⟩ := exists_nearest y1
    have hfrac : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) ∧ 1 / ((k : ℝ) + 1) ≤ 1 := by
      constructor
      · positivity
      · rw [div_le_one hk1]; have : (0 : ℝ) ≤ k := by positivity
        linarith
    -- `y1` lies between `y` and `s`.
    have hbet : min y s ≤ min y1 s ∧ max y1 s ≤ max y s := by
      have hy1' : y1 = y + (s - y) * (1 / ((k : ℝ) + 1)) := by rw [hy1]; ring
      rcases le_total y s with h | h
      · have h1 : y ≤ y1 := by rw [hy1']; nlinarith [hfrac.1]
        have h2 : y1 ≤ s := by rw [hy1']; nlinarith [hfrac.2]
        rw [min_eq_left h, min_eq_left h2, max_eq_right h, max_eq_right h2]
        exact ⟨h1, le_rfl⟩
      · have h1 : y1 ≤ y := by rw [hy1']; nlinarith [hfrac.1]
        have h2 : s ≤ y1 := by rw [hy1']; nlinarith [hfrac.2]
        rw [min_eq_right h, min_eq_right h2, max_eq_left h, max_eq_left h2]
        exact ⟨le_rfl, h1⟩
    have hy : 1 / 2 ^ 1022 ≤ y := hmin.trans (min_le_left _ _)
    have hyt : y < F64PositiveRounding.overflowThreshold := (le_max_left _ _).trans_lt hmax
    have hm0 : (0 : ℝ) ≤ min y s := le_trans (by positivity) hmin
    -- From `y` to `y1`: one step.
    have h1 : w1.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ w1.toNat + 1 := by
      refine steps_rel y y1 w1 w hy hyt hw1 hw ?_
      have hd : y1 - y = (s - y) / ((k : ℝ) + 1) := by rw [hy1]; ring
      rw [hd, abs_div, abs_of_pos hk1, div_le_iff₀ hk1]
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [this] at hr
      calc |s - y| ≤ ((k : ℝ) + 1) * δ * min y s := hr
        _ ≤ ((k : ℝ) + 1) * δ * y := by
          apply mul_le_mul_of_nonneg_left (min_le_left _ _)
          positivity
        _ = (1 - 1 / 2 ^ 50) * u * y * ((k : ℝ) + 1) := by rw [hδ]; ring
    -- From `y1` to `s`: `k` steps.
    have h2 := ih y1 s c w1 (hmin.trans hbet.1) (hbet.2.trans_lt hmax) hc hw1 (by
      have hd : s - y1 = (s - y) * ((k : ℝ) / ((k : ℝ) + 1)) := by
        rw [hy1]; field_simp; ring
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [this] at hr
      rw [hd, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) / ((k : ℝ) + 1))]
      calc |s - y| * ((k : ℝ) / ((k : ℝ) + 1)) ≤
            ((k : ℝ) + 1) * δ * min y s * ((k : ℝ) / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
        _ = (k : ℝ) * δ * min y s := by field_simp
        _ ≤ (k : ℝ) * δ * min y1 s := by
          apply mul_le_mul_of_nonneg_left hbet.1
          positivity)
    constructor <;> omega

/-- `WithinSteps k` from a relative distance below `k (1 - 2 ^ -50) u min(y, s)`. -/
theorem within_rel_k (k : Nat) (hk : 1 ≤ k) (y s : ℝ) (c : UInt64)
    (hmin : 1 / 2 ^ 1022 ≤ min y s) (hmax : max y s < F64PositiveRounding.overflowThreshold)
    (hc : Nearest s c) (hr : |s - y| ≤ k * ((1 - 1 / 2 ^ 50) * u) * min y s) :
    F64SignedRounding.WithinSteps k y c := by
  have hy : 1 / 2 ^ 1022 ≤ y := hmin.trans (min_le_left _ _)
  have hyt : y < F64PositiveRounding.overflowThreshold := (le_max_left _ _).trans_lt hmax
  have hy0 : (0 : ℝ) ≤ y := le_trans (by positivity) hy
  have hw := (F64NearestEven.roundNearestEven_spec y).1
  have hs := steps_rel_k k hk y s c _ hmin hmax hc hw hr
  rw [← F64PositiveRounding.reference_finite y hyt] at hs
  exact F64SignedRounding.within_of_nonneg k y hy0 c
    (by have := hc.1; unfold limit at this; omega) hs.1 hs.2

/-- `WithinSteps k` from `abs(s - y) ≤ (k - 1/16) u y`, for `y` in `[2 ^ -1021, 2 ^ 1022)` and
`k ≤ 64`. -/
theorem within_rel_of (k : Nat) (hk : 1 ≤ k) (hk64 : k ≤ 64) (y s : ℝ) (c : UInt64)
    (hy : 1 / 2 ^ 1021 ≤ y) (hyt : y < 2 ^ 1022) (hc : Nearest s c)
    (hr : |s - y| ≤ ((k : ℝ) - 1 / 16) * u * y) :
    F64SignedRounding.WithinSteps k y c := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk64r : (k : ℝ) ≤ 64 := by exact_mod_cast hk64
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have huy : ((k : ℝ) - 1 / 16) * u * y ≤ 64 * (1 / 2 ^ 53) * y := by
    rw [hu]
    apply mul_le_mul_of_nonneg_right _ hy0.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hsb := abs_le.mp hr
  have hsl : y * (1 - 64 / 2 ^ 53) ≤ s := by
    have : 64 * (1 / 2 ^ 53) * y = y * (64 / 2 ^ 53) := by ring
    linarith
  have hsu : s ≤ y * (1 + 64 / 2 ^ 53) := by
    have : 64 * (1 / 2 ^ 53) * y = y * (64 / 2 ^ 53) := by ring
    linarith
  have hmin : y * (1 - 64 / 2 ^ 53) ≤ min y s := by
    apply le_min _ hsl
    have : (0 : ℝ) ≤ y * (64 / 2 ^ 53) := by positivity
    linarith
  refine within_rel_k k hk y s c ?_ ?_ hc ?_
  · have h1 : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 1021 * (1 - 64 / 2 ^ 53) := by norm_num
    have h2 : 1 / 2 ^ 1021 * (1 - 64 / 2 ^ 53) ≤ y * (1 - 64 / 2 ^ 53) :=
      mul_le_mul_of_nonneg_right hy (by norm_num)
    linarith
  · have h1 : y * (1 + 64 / 2 ^ 53) < 2 ^ 1022 * (1 + 64 / 2 ^ 53) :=
      mul_lt_mul_of_pos_right hyt (by norm_num)
    have h2 : (2 : ℝ) ^ 1022 * (1 + 64 / 2 ^ 53) < F64PositiveRounding.overflowThreshold := by
      unfold F64PositiveRounding.overflowThreshold; norm_num
    have h3 : y ≤ y * (1 + 64 / 2 ^ 53) := by
      have : (0 : ℝ) ≤ y * (64 / 2 ^ 53) := by positivity
      linarith
    exact max_lt (by linarith) (by linarith)
  · have h1 : ((k : ℝ) - 1 / 16) * u * y ≤
        (k : ℝ) * ((1 - 1 / 2 ^ 50) * u) * (y * (1 - 64 / 2 ^ 53)) := by
      rw [hu]
      have : ((k : ℝ) - 1 / 16) ≤ (k : ℝ) * (1 - 1 / 2 ^ 50) * (1 - 64 / 2 ^ 53) := by
        nlinarith
      have hyu : (0 : ℝ) ≤ 1 / 2 ^ 53 * y := by positivity
      calc ((k : ℝ) - 1 / 16) * (1 / 2 ^ 53) * y = ((k : ℝ) - 1 / 16) * (1 / 2 ^ 53 * y) := by ring
        _ ≤ (k : ℝ) * (1 - 1 / 2 ^ 50) * (1 - 64 / 2 ^ 53) * (1 / 2 ^ 53 * y) :=
          mul_le_mul_of_nonneg_right this hyu
        _ = _ := by ring
    have h2 : (k : ℝ) * ((1 - 1 / 2 ^ 50) * u) * (y * (1 - 64 / 2 ^ 53)) ≤
        (k : ℝ) * ((1 - 1 / 2 ^ 50) * u) * min y s := by
      apply mul_le_mul_of_nonneg_left hmin
      have : (0 : ℝ) ≤ (1 - 1 / 2 ^ 50) * u := by rw [hu]; norm_num
      positivity
    linarith

#print axioms steps_rel
#print axioms steps_rel_k
#print axioms within_rel_k
#print axioms within_rel_of

end LeanExe.ProofKit.F64NearestRelative
