import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64RelativeSteps
import Mathlib.Data.Int.Log

/-!
A rounded sum is a nearest binary64 value of the exact sum.  `roundShift n s` rounds `n / 2 ^ s` to
an integer at least as close as any other (`roundShift_nearest`), and every finite magnitude at or
above `2 ^ (52 + s)` is a multiple of `2 ^ s`, so `roundedMagnitude n` is at least as close to `n` as
the magnitude of any finite word (`roundedMagnitude_nearest`).  `add_nearest` states it for a
positive sum in the form of `F64NearestNonnegative.Nearest`.  `steps_of_nearest` then counts the
steps between two nearest words from the distance of the numbers they round: the rounding of a
number within `m` spacings of `y` lies within `m` steps of a nearest word of `y`.
-/

namespace LeanExe.ProofKit.F64AddNearest
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep

set_option exponentiation.threshold 4096

/-- `roundShift n s · 2 ^ s` is a multiple of `2 ^ s` nearest to `n`, for `s ≥ 1`. -/
theorem roundShift_nearest (n s m : Nat) (hs : 1 ≤ s) :
    |(Wasm.IEEE32.roundShift n s : Int) * 2 ^ s - n| ≤ |(m : Int) * 2 ^ s - n| := by
  have hU2 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have heven : 2 ^ s / 2 * 2 = 2 ^ s := Nat.div_mul_cancel (dvd_pow_self 2 (by omega))
  have hR : (Wasm.IEEE32.roundShift n s = n / 2 ^ s ∧ 2 * (n % 2 ^ s) ≤ 2 ^ s) ∨
      (Wasm.IEEE32.roundShift n s = n / 2 ^ s + 1 ∧ 2 ^ s ≤ 2 * (n % 2 ^ s)) := by
    unfold Wasm.IEEE32.roundShift
    simp only []
    split_ifs with h1 h2 h3
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, q = n / 2 ^ s := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n % 2 ^ s := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = 2 ^ s := ⟨_, rfl⟩
  rw [← hq, ← hr, ← hUd] at hR
  rw [← hUd] at heven hU2
  have hn : n = q * U + r := by rw [hq, hr, hUd, mul_comm]; exact (Nat.div_add_mod n _).symm
  have hrU : r < U := by rw [hr, hUd]; exact Nat.mod_lt _ (by positivity)
  have hUi : ((2 : Int) ^ s) = (U : Int) := by rw [hUd]; push_cast; rfl
  rw [hUi]
  have hni : (n : Int) = (q : Int) * U + r := by exact_mod_cast hn
  have hm : (r : Int) ≤ |(m : Int) * U - n| ∨ ((U : Int) - r) ≤ |(m : Int) * U - n| := by
    rcases le_or_gt m q with h | h
    · left
      have h1 : (m : Int) * U ≤ q * U := by exact_mod_cast Nat.mul_le_mul_right U h
      rw [abs_sub_comm, abs_of_nonneg (by rw [hni]; nlinarith)]
      rw [hni]
      linarith
    · right
      have h1 : ((q : Int) + 1) * U ≤ m * U := by
        have := Nat.mul_le_mul_right U h
        push_cast at this ⊢
        exact_mod_cast this
      rw [abs_of_nonneg (by rw [hni]; nlinarith)]
      rw [hni]
      linarith
  have hr0 : (0 : Int) ≤ r := by positivity
  have hrUi : (r : Int) < U := by exact_mod_cast hrU
  have hl0 : |(q : Int) * U - n| = r := by
    rw [hni, show (q : Int) * U - (q * U + r) = -r by ring, abs_neg, abs_of_nonneg hr0]
  have hl1 : |((q : Int) + 1) * U - n| = U - r := by
    rw [hni, show ((q : Int) + 1) * U - (q * U + r) = U - r by ring, abs_of_nonneg (by linarith)]
  rcases hR with ⟨hR, h2⟩ | ⟨hR, h2⟩
  · rw [hR, hl0]
    have h2' : 2 * (r : Int) ≤ U := by exact_mod_cast h2
    rcases hm with h | h <;> linarith
  · rw [hR]
    push_cast
    rw [hl1]
    have h2' : (U : Int) ≤ 2 * r := by exact_mod_cast h2
    rcases hm with h | h <;> linarith

/-- `roundedMagnitude n` is at least as close to `n` as the magnitude of any finite word. -/
theorem roundedMagnitude_nearest (n : Nat) (hmax : n < 2 ^ 2097) (v : UInt64) (hv : Finite v) :
    |(roundedMagnitude n : Int) - n| ≤ |(Wasm.IEEE64.scaledMagnitude v : Int) - n| := by
  by_cases hsmall : n < 2 ^ 53
  · rw [show roundedMagnitude n = n by rw [roundedMagnitude, if_pos hsmall]]
    simp
  have hmin : 2 ^ 53 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hpar := F64PackRelative.rounding_parameters hmin hmax
  simp only at hpar
  obtain ⟨hs0, _, hq1, hq2⟩ := hpar
  set s := Nat.log2 n - 52 with hs
  have hlog1 : 2 ^ (52 + s) ≤ n := by
    have h := Nat.log2_self_le hn0
    rw [show 52 + s = Nat.log2 n by omega]
    exact h
  have hlog2 : n < 2 ^ (53 + s) := by
    have h := Nat.lt_log2_self (n := n)
    rw [show 53 + s = Nat.log2 n + 1 by omega]
    exact h
  have hround : (roundedMagnitude n : Int) = (Wasm.IEEE32.roundShift n s : Int) * 2 ^ s := by
    simp only [roundedMagnitude, show ¬ n < 2 ^ 53 from hsmall, ite_false, ← hs]
    split_ifs with h
    · have h' : Wasm.IEEE32.roundShift n s = 2 ^ 53 := by simpa using h
      rw [h']
      push_cast
      ring
    · push_cast
      ring
  rw [hround]
  -- the magnitude of `v`
  have he : Wasm.IEEE64.exponent v < 2047 := by
    have h := hv
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent v < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  set W := Wasm.IEEE64.scaledMagnitude v with hW
  rcases Nat.lt_or_ge W (2 ^ (52 + s)) with hlow | hhigh
  · -- below the binade of `n`: the binade's start is closer
    have h := roundShift_nearest n s (2 ^ 52) hs0
    have h52 : ((2 ^ 52 : Nat) : Int) * 2 ^ s = 2 ^ (52 + s) := by
      rw [pow_add]
      norm_num
    have hli' : (2 : Int) ^ (52 + s) ≤ n := by exact_mod_cast hlog1
    have hb : |((2 ^ 52 : Nat) : Int) * 2 ^ s - n| = n - 2 ^ (52 + s) := by
      rw [h52, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hb] at h
    have hWi : (W : Int) < 2 ^ (52 + s) := by exact_mod_cast hlow
    have hli : (2 : Int) ^ (52 + s) ≤ n := by exact_mod_cast hlog1
    rw [abs_sub_comm (W : Int) (n : Int), abs_of_nonneg (show (0 : Int) ≤ (n : Int) - W by linarith)]
    push_cast at h
    linarith
  · -- in or above the binade of `n`: a multiple of `2 ^ s`
    have hep : 0 < Wasm.IEEE64.exponent v := by
      by_contra h0
      have h0' : Wasm.IEEE64.exponent v = 0 := by omega
      have : W = Wasm.IEEE64.fraction v := by simp [hW, Wasm.IEEE64.scaledMagnitude, h0']
      have : 2 ^ 52 ≤ 2 ^ (52 + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hWdef : W = (2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1) := by
      simp [hW, Wasm.IEEE64.scaledMagnitude, Nat.pos_iff_ne_zero.mp hep]
    have hes : s ≤ Wasm.IEEE64.exponent v - 1 := by
      by_contra hlt
      have hlt' : Wasm.IEEE64.exponent v - 1 + 1 ≤ s := by omega
      have h1 : W < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) := by
        rw [hWdef]
        apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
        omega
      have h2 : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) ≤ 2 ^ (52 + s) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hmul : W = ((2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1 - s)) *
        2 ^ s := by
      rw [hWdef, mul_assoc, ← pow_add, Nat.sub_add_cancel hes]
    have h := roundShift_nearest n s
      ((2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1 - s)) hs0
    rw [hmul]
    push_cast at h ⊢
    exact h

/-- A positive rounded sum is a nearest nonnegative binary64 value of the exact sum. -/
theorem add_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hpos : 0 < value a + value b) (hbound : value a + value b < (2 : ℝ) ^ 1023) :
    Nearest (value a + value b) (Wasm.IEEE64.add a b) := by
  have hz : 0 < Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
    have h : value a + value b = ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : Int) : ℝ) /
        (2 : ℝ) ^ 1074 := by simp only [value, Int.cast_add, add_div]
    rw [h] at hpos
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp hpos
    exact_mod_cast this
  set n := (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs with hn
  have hni : (n : Int) = Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b :=
    Int.natAbs_of_nonneg hz.le
  have hfin := F64AddBounds.add_real_relative a b ha hb
    (by rw [abs_of_pos hpos]; exact hbound)
  have hmax : n < 2 ^ 2097 := by
    have h1 : ((n : Int) : ℝ) / 2 ^ 1074 < 2 ^ 1023 := by
      rw [hni]; push_cast; simp only [value] at hbound; rw [add_div]; exact hbound
    have h2 : ((n : Int) : ℝ) < 2 ^ 1023 * 2 ^ 1074 := by
      rwa [div_lt_iff₀ (by positivity)] at h1
    have h3 : (n : ℝ) < 2 ^ 2097 := by
      have : (2 : ℝ) ^ 1023 * 2 ^ 1074 = 2 ^ 2097 := by norm_num
      push_cast at h2
      linarith
    exact_mod_cast h3
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude false n := by
    have hne : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0 := hz.ne'
    have hnn : ¬ Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0 := not_lt.mpr hz.le
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, hne, hnn, n]
  obtain ⟨hcf, hcm, hsign⟩ := F64PackRelative.pack_spec false n hmax
  rw [heq]
  set c := Wasm.IEEE64.roundScaledMagnitude false n
  have hcval : value c = (roundedMagnitude n : ℝ) / 2 ^ 1074 := by
    simp only [value, Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false, hcm]
    push_cast
    rfl
  have hyval : value a + value b = (n : ℝ) / 2 ^ 1074 := by
    have : ((n : Int) : ℝ) = (n : ℝ) := by push_cast; rfl
    simp only [value, ← add_div]
    rw [← this, hni]
    push_cast
    rfl
  refine ⟨F64Magnitude.lt_limit_of_finite c hcf hsign, ?_⟩
  intro v hv
  have hvs : Wasm.IEEE64.sign v = false := (nearest_finite (value v) v ⟨hv, fun _ _ => by simp⟩).2
  have hvf : Finite v := (nearest_finite (value v) v ⟨hv, fun _ _ => by simp⟩).1
  have hvval : value v = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
    simp only [value, Wasm.IEEE64.scaledValue, hvs, Bool.false_eq_true, ite_false]
    push_cast
    rfl
  rw [hcval, hyval, hvval, ← sub_div, ← sub_div, abs_div, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := roundedMagnitude_nearest n hmax v hvf
  exact_mod_cast h

/-- Two nearest words of numbers within `m` spacings lie within `m` steps of each other. -/
theorem steps_of_nearest (m : Nat) (hm : 1 ≤ m) (c w : UInt64) (v y d : ℝ) (L U : Nat)
    (hU : U ≤ limit) (hc : Nearest v c) (hw : Nearest y w)
    (hcr : L ≤ c.toNat ∧ c.toNat ≤ U) (hwr : L ≤ w.toNat ∧ w.toNat ≤ U)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (hvy : |v - y| < m * d) :
    c.toNat ≤ w.toNat + m ∧ w.toNat ≤ c.toNat + m := by
  have hlim : limit < 2 ^ 63 := by decide
  have word_nat (n : Nat) (hn : n ≤ U) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (lt_of_le_of_lt (hn.trans hU) hlim) (by norm_num))
  have hgs := F64RelativeSteps.gap_sum L U d hU hspacing
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- one direction, for any two nearest words in the range
  have key : ∀ (c w : UInt64) (v y : ℝ), Nearest v c → Nearest y w →
      L ≤ c.toNat ∧ c.toNat ≤ U → L ≤ w.toNat ∧ w.toNat ≤ U →
      v - y < m * d → c.toNat ≤ w.toNat + m := by
    intro c w v y hc hw hcr hwr hvy
    by_contra h
    have hc63 : c.toNat < 2 ^ 63 := lt_of_le_of_lt (hcr.2.trans hU) hlim
    have hw1 : w.toNat + 1 ≤ U := by omega
    have hcm1 : L ≤ c.toNat - 1 := by omega
    -- `w` nearest `y`: `y` is at most the midpoint above `w`
    have hg1 := hgs 1 w.toNat hwr.1 hw1
    simp only [UInt64.ofNat_toNat, Nat.cast_one, one_mul] at hg1
    have hwv : value w < value (UInt64.ofNat (w.toNat + 1)) := by
      have := value_strict (left := w) (right := UInt64.ofNat (w.toNat + 1))
        (by rw [word_nat _ hw1]; omega) (by rw [word_nat _ hw1]; omega)
      exact this
    have hmid1 := upper_midpoint _ _ y hwv (hw.2 _ (by rw [word_nat _ hw1]; omega))
    -- `c` nearest `v`: `v` is at least the midpoint below `c`
    have hcm1U : c.toNat - 1 ≤ U := by omega
    have hcv : value (UInt64.ofNat (c.toNat - 1)) < value c := by
      exact value_strict (by exact hc63) (by rw [word_nat _ hcm1U]; omega)
    have hmid2 := lower_midpoint _ _ v hcv (hc.2 _ (by rw [word_nat _ hcm1U]; omega))
    -- the gaps
    have hga := hgs m (w.toNat + 1) (by omega) (by omega)
    have hgb := hgs m w.toNat hwr.1 (by omega)
    have hle1 : value (UInt64.ofNat (w.toNat + 1 + m)) ≤ value c := by
      apply (value_le_iff (by rw [word_nat _ (by omega)]; omega) hc63).mpr
      rw [word_nat _ (by omega)]
      omega
    have hle2 : value (UInt64.ofNat (w.toNat + m)) ≤ value (UInt64.ofNat (c.toNat - 1)) := by
      apply (value_le_iff (by rw [word_nat _ (by omega)]; omega)
        (by rw [word_nat _ hcm1U]; omega)).mpr
      rw [word_nat _ (by omega), word_nat _ hcm1U]
      omega
    simp only [UInt64.ofNat_toNat] at hgb
    linarith
  constructor
  · exact key c w v y hc hw hcr hwr (by have := le_abs_self (v - y); linarith)
  · exact key w c y v hw hc hwr hcr (by have := neg_abs_le (v - y); linarith)

#print axioms roundShift_nearest
#print axioms roundedMagnitude_nearest
#print axioms add_nearest
#print axioms steps_of_nearest

/-- A nearest word lies at or above every word below the number it rounds. -/
theorem nearest_ge (v : ℝ) (c : UInt64) (L : Nat) (hL : L < limit) (hc : Nearest v c)
    (hv : value (UInt64.ofNat L) ≤ v) : L ≤ c.toNat := by
  have hlim : limit < 2 ^ 63 := by decide
  have hLw : (UInt64.ofNat L).toNat = L :=
    UInt64.toNat_ofNat_of_lt' (hL.trans (by decide : limit < 2 ^ 64))
  by_contra hn
  have hlt := value_strict (by rw [hLw]; exact hL.trans hlim)
    (show c.toNat < (UInt64.ofNat L).toNat by rw [hLw]; omega)
  have hd := hc.2 (UInt64.ofNat L) (by rw [hLw]; exact hL)
  rw [abs_of_nonpos (by linarith : value c - v ≤ 0),
    abs_of_nonpos (by linarith : value (UInt64.ofNat L) - v ≤ 0)] at hd
  linarith

/-- A word nearest to a positive `v` lies within `m` steps of the reference of a positive `y` when
`|v - y|` is below `m` spacings of a binade at or below both. -/
theorem within_of_nearest (m : Nat) (hm : 1 ≤ m) (y v : ℝ) (c : UInt64) (e : Nat) (he1 : 1 ≤ e)
    (he : e < 2047)
    (hy : value (UInt64.ofNat (e * 2 ^ 52)) ≤ y) (hv : value (UInt64.ofNat (e * 2 ^ 52)) ≤ v)
    (hyt : y < F64PositiveRounding.overflowThreshold) (hc : Nearest v c)
    (hvy : |v - y| < m * ((2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074)) :
    F64SignedRounding.WithinSteps m y c := by
  have hl : limit = 2047 * 2 ^ 52 := rfl
  have hL : e * 2 ^ 52 < limit := by rw [hl]; omega
  have hw := (F64NearestEven.roundNearestEven_spec y).1
  have hcL := nearest_ge v c _ hL hc hv
  have hwL := nearest_ge y _ _ hL hw hy
  have hspacing : ∀ n : Nat, e * 2 ^ 52 ≤ n → n < limit →
      (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n) :=
    fun n hn1 hn2 => F64FullStep.gap_lower n e hn1 (by rw [hl] at hn2; omega)
  have hst := steps_of_nearest m hm c _ v y _ (e * 2 ^ 52) limit le_rfl hc hw
    ⟨hcL, hc.1.le⟩ ⟨hwL, hw.1.le⟩ hspacing hvy
  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ value (UInt64.ofNat (e * 2 ^ 52)) := by
      rw [F64PositiveSpacing.boundary_value e he1 (by omega)]
      positivity
    linarith
  have href := F64PositiveRounding.reference_finite y hyt
  exact F64SignedRounding.within_of_nonneg m y hy0 c hc.1.le (by rw [href]; exact hst.1)
    (by rw [href]; exact hst.2)

/-- A word nearest to `v` lies within `m` steps of the reference of a positive `y` when `v` lies
within `(63/64) m` units of roundoff of `y`, relative to `y`.  The binade of `(1 - 2^-46) y` lies at
or below both numbers, and its spacing exceeds `(63/64) 2^-53 y`. -/
theorem within_nearest_relative (m : Nat) (hm : 1 ≤ m) (hm64 : m ≤ 64) (y v : ℝ) (c : UInt64)
    (hc : Nearest v c) (hy : 1 / (2 : ℝ) ^ 1021 ≤ y) (hyt : y < (2 : ℝ) ^ 1000)
    (hvy : |v - y| ≤ m * (63 / 64) * unitRoundoff64 * y) :
    F64SignedRounding.WithinSteps m y c := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmr64 : (m : ℝ) ≤ 64 := by exact_mod_cast hm64
  set t : ℝ := (1 - 1 / 2 ^ 46) * y with ht
  have hc46 : (0 : ℝ) < 1 - 1 / 2 ^ 46 := by norm_num
  have ht0 : 0 < t := mul_pos hc46 hy0
  have hty : t ≤ y := by
    rw [ht]
    have : (0 : ℝ) ≤ 1 / 2 ^ 46 * y := by positivity
    linarith
  set k : Int := Int.log 2 t with hk
  have hk1 : (2 : ℝ) ^ k ≤ t := by
    have h := Int.zpow_log_le_self (b := 2) (by norm_num) ht0
    simpa using h
  have hk2 : t < (2 : ℝ) ^ (k + 1) := by
    have h := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) t
    simpa using h
  have hklo : -1022 ≤ k := by
    by_contra h
    have h1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (-1022 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (-1022 : Int) = 1 / 2 ^ 1022 := by norm_num
    have h3 : (1 - 1 / 2 ^ 46) * (1 / (2 : ℝ) ^ 1021) ≤ t :=
      mul_le_mul_of_nonneg_left hy hc46.le
    have h4 : 1 / (2 : ℝ) ^ 1022 < (1 - 1 / 2 ^ 46) * (1 / 2 ^ 1021) := by norm_num
    have h5 : t < 1 / (2 : ℝ) ^ 1022 := by
      calc t < (2 : ℝ) ^ (k + 1) := hk2
        _ ≤ (2 : ℝ) ^ (-1022 : Int) := h1
        _ = 1 / 2 ^ 1022 := h2
    linarith
  have hkhi : k < 1000 := by
    by_contra h
    have h1 : (2 : ℝ) ^ (1000 : Int) ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (1000 : Int) = 2 ^ 1000 := by norm_num
    have h3 : (2 : ℝ) ^ 1000 ≤ y := by
      calc (2 : ℝ) ^ 1000 = (2 : ℝ) ^ (1000 : Int) := h2.symm
        _ ≤ (2 : ℝ) ^ k := h1
        _ ≤ t := hk1
        _ ≤ y := hty
    linarith
  set e : Nat := (k + 1023).toNat with he
  have heq : (e : Int) = k + 1023 := by rw [he]; omega
  have he1 : 1 ≤ e := by omega
  have he2 : e < 2047 := by omega
  have hB : value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ k :=
    F64NearestBinade.boundary_power e k he1 (by omega) heq
  have hsp : (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 = (2 : ℝ) ^ k / 2 ^ 52 := by
    rw [F64NearestBinade.power_quotient]
    have h : (((e - 1 : Nat) : Int) - 1074) = k - 52 := by omega
    rw [h, zpow_sub₀ (by norm_num)]
    norm_num
  have hmu : m * (63 / 64) * unitRoundoff64 * y ≤ 1 / 2 ^ 46 * y := by
    rw [hu]
    have h1 : (m : ℝ) * (63 / 64) * (1 / 2 ^ 53) ≤ 64 * (63 / 64) * (1 / 2 ^ 53) := by gcongr
    have h2 : (64 : ℝ) * (63 / 64) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 46 := by norm_num
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hy0.le
  have hv1 := (abs_le.mp hvy).1
  have htv : t ≤ v := by rw [ht] at hk1 ⊢; linarith
  refine within_of_nearest m hm y v c e he1 he2 (by rw [hB]; linarith) (by rw [hB]; linarith)
    ?_ hc ?_
  · have h : (2 : ℝ) ^ 1000 < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
      norm_num
    linarith
  · rw [hsp]
    have h2k : t / 2 < (2 : ℝ) ^ k := by
      have h : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [zpow_add_one₀ (by norm_num)]; ring
      linarith
    have h5 : (63 / 64) * (1 / (2 : ℝ) ^ 53) * y ≤ t / 2 / 2 ^ 52 := by
      rw [ht]
      have h6 : (63 / 64 : ℝ) * (1 / 2 ^ 53) ≤ (1 - 1 / 2 ^ 46) / 2 / 2 ^ 52 := by norm_num
      have h7 := mul_le_mul_of_nonneg_right h6 hy0.le
      have h8 : (1 - 1 / (2 : ℝ) ^ 46) / 2 / 2 ^ 52 * y = (1 - 1 / 2 ^ 46) * y / 2 / 2 ^ 52 := by
        ring
      linarith
    have h4 : t / 2 / 2 ^ 52 < (2 : ℝ) ^ k / 2 ^ 52 := div_lt_div_of_pos_right h2k (by positivity)
    have h3 : (63 / 64) * (1 / (2 : ℝ) ^ 53) * y < (2 : ℝ) ^ k / 2 ^ 52 := by linarith
    have hlt : m * (63 / 64) * unitRoundoff64 * y < m * ((2 : ℝ) ^ k / 2 ^ 52) := by
      rw [hu]
      calc (m : ℝ) * (63 / 64) * (1 / 2 ^ 53) * y = m * ((63 / 64) * (1 / 2 ^ 53) * y) := by ring
        _ < m * ((2 : ℝ) ^ k / 2 ^ 52) := mul_lt_mul_of_pos_left h3 (by linarith)
    linarith

#print axioms within_of_nearest
#print axioms within_nearest_relative

end LeanExe.ProofKit.F64AddNearest
