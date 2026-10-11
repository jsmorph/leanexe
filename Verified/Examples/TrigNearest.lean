import Verified.Examples.TrigFloatTools
import LeanExe.ProofKit.F64PackingModel
import LeanExe.ProofKit.F64Magnitude

/-!
Rounded sums and differences are nearest: no finite word lies closer to the exact result.  The
rounding of a magnitude `n` with more than 53 bits keeps the nearest multiple of `2 ^ s`,
`s = log2 n - 52`, and every finite magnitude above `2 ^ (52 + s)` and below `2 ^ (53 + s)` is
such a multiple.  From this follows fdlibm's compensated difference: for `|w| ≤ |a| / 4` and
`s = a - w` rounded, `a - s` and `(a - s) - w` are exact, so `s + ((a - s) - w) = a - w`.
-/

namespace Verified.Examples.TrigNearest

set_option exponentiation.threshold 4096

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools

/-- `roundShift n s` is a nearest multiple of `2 ^ s`. -/
theorem roundShift_near (n s : Nat) (hs : 1 ≤ s) (M : Int) :
    |((Wasm.IEEE32.roundShift n s : Nat) : Int) * 2 ^ s - n| ≤ |M * 2 ^ s - n| := by
  have hP : 0 < 2 ^ s := by positivity
  have hdm := Nat.div_add_mod n (2 ^ s)
  have hr : n % 2 ^ s < 2 ^ s := Nat.mod_lt _ hP
  have heven : 2 ^ s = 2 * (2 ^ s / 2) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [pow_add, pow_one, Nat.mul_div_cancel_left _ (by norm_num)]
  have hR : (Wasm.IEEE32.roundShift n s = n / 2 ^ s ∧ n % 2 ^ s ≤ 2 ^ s - n % 2 ^ s) ∨
      (Wasm.IEEE32.roundShift n s = n / 2 ^ s + 1 ∧ 2 ^ s - n % 2 ^ s ≤ n % 2 ^ s) := by
    unfold Wasm.IEEE32.roundShift
    dsimp only
    split_ifs <;> omega
  generalize n / 2 ^ s = q at hdm hR
  generalize n % 2 ^ s = r at hdm hr hR
  generalize hPd : (2 : Nat) ^ s = P at hdm hr hR hP
  have hPi : (2 : Int) ^ s = (P : Int) := by rw [← hPd, Nat.cast_pow, Nat.cast_ofNat]
  rw [hPi]
  have hn : (n : Int) = q * P + r := by rw [← hdm]; push_cast; ring
  rw [hn]
  have hPpos : (0 : Int) < P := by exact_mod_cast hP
  rcases hR with ⟨hR, hle⟩ | ⟨hR, hle⟩
  · rw [hR]
    have hle' : (r : Int) ≤ P - r := by omega
    rw [show ((q : Nat) : Int) * P - (q * P + r) = -(r : Int) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    rcases le_or_gt M q with hM | hM
    · have : (M - q) * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hPpos.le
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have : (P : Int) ≤ (M - q) * P := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      linarith
  · rw [hR]
    have hle' : (P : Int) - r ≤ r := by omega
    rw [show ((q + 1 : Nat) : Int) * P - (q * P + r) = (P : Int) - r by push_cast; ring,
      abs_of_nonneg (by omega)]
    rcases le_or_gt M q with hM | hM
    · have : (M - q) * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hPpos.le
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have : (P : Int) ≤ (M - q) * P := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- The rounded magnitude is nearest among magnitudes with at most 53 significant bits. -/
theorem roundedMagnitude_near (n q k : Nat) (hq : q < 2 ^ 53) :
    |(roundedMagnitude n : Int) - n| ≤ |((q * 2 ^ k : Nat) : Int) - n| := by
  unfold roundedMagnitude
  split
  · simp
  · rename_i hn
    push Not at hn
    have hn0 : n ≠ 0 := by
      have : 0 < 2 ^ 53 := by positivity
      omega
    have hlog : 53 ≤ Nat.log2 n := (Nat.le_log2 hn0).mpr hn
    set s := Nat.log2 n - 52 with hs
    have hs1 : 1 ≤ s := by omega
    have hlo : 2 ^ (52 + s) ≤ n := by
      rw [show 52 + s = Nat.log2 n by omega]
      exact Nat.log2_self_le hn0
    have hhi : n < 2 ^ (53 + s) := by
      rw [show 53 + s = Nat.log2 n + 1 by omega]
      exact Nat.lt_log2_self
    have hval : ((if Wasm.IEEE32.roundShift n s == 2 ^ 53 then 2 ^ 52 * 2 ^ (s + 1)
        else Wasm.IEEE32.roundShift n s * 2 ^ s : Nat) : Int) =
        ((Wasm.IEEE32.roundShift n s : Nat) : Int) * 2 ^ s := by
      split
      · rename_i h
        rw [beq_iff_eq] at h
        rw [h, pow_succ]
        push_cast
        ring
      · push_cast
        ring
    rw [hval]
    have hP : (0 : Int) < 2 ^ s := by positivity
    by_cases h1 : 2 ^ (53 + s) ≤ q * 2 ^ k
    · have e : ((2 ^ (53 + s) : Nat) : Int) = (2 : Int) ^ 53 * 2 ^ s := by
        rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
      have h1' : (2 : Int) ^ 53 * 2 ^ s ≤ ((q * 2 ^ k : Nat) : Int) := by
        rw [← e]
        exact_mod_cast h1
      have hhi' : (n : Int) < (2 : Int) ^ 53 * 2 ^ s := by
        rw [← e]
        exact_mod_cast hhi
      calc |((Wasm.IEEE32.roundShift n s : Nat) : Int) * 2 ^ s - n|
          ≤ |(2 ^ 53 : Int) * 2 ^ s - n| := roundShift_near n s hs1 _
        _ ≤ |((q * 2 ^ k : Nat) : Int) - n| := by
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
    · by_cases h2 : q * 2 ^ k ≤ 2 ^ (52 + s)
      · have e : ((2 ^ (52 + s) : Nat) : Int) = (2 : Int) ^ 52 * 2 ^ s := by
          rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
        have h2' : ((q * 2 ^ k : Nat) : Int) ≤ (2 : Int) ^ 52 * 2 ^ s := by
          rw [← e]
          exact_mod_cast h2
        have hlo' : (2 : Int) ^ 52 * 2 ^ s ≤ (n : Int) := by
          rw [← e]
          exact_mod_cast hlo
        calc |((Wasm.IEEE32.roundShift n s : Nat) : Int) * 2 ^ s - n|
            ≤ |(2 ^ 52 : Int) * 2 ^ s - n| := roundShift_near n s hs1 _
          _ ≤ |((q * 2 ^ k : Nat) : Int) - n| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
      · push Not at h1 h2
        have hks : s ≤ k := by
          by_contra hk
          have hk' : 2 ^ k * 2 ≤ 2 ^ s := by
            rw [← pow_succ]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          have : q * 2 ^ k < 2 ^ 53 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hq (by positivity)
          have h3 : 2 ^ 53 * 2 ^ k * 2 ≤ 2 ^ (52 + s) * 2 := by
            rw [pow_add, show 2 ^ 53 * 2 ^ k * 2 = 2 ^ 52 * (2 ^ k * 2) * 2 by ring]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk')
          omega
        have hm : ((q * 2 ^ k : Nat) : Int) = ((q * 2 ^ (k - s) : Nat) : Int) * 2 ^ s := by
          push_cast
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hks]
        rw [hm]
        exact roundShift_near n s hs1 _

/-- Every finite magnitude has at most 53 significant bits. -/
theorem magnitude_repr (v : UInt64) :
    ∃ q k, q < 2 ^ 53 ∧ Wasm.IEEE64.scaledMagnitude v = q * 2 ^ k := by
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  by_cases he : Wasm.IEEE64.exponent v = 0
  · refine ⟨Wasm.IEEE64.fraction v, 0, by omega, ?_⟩
    simp [Wasm.IEEE64.scaledMagnitude, he]
  · refine ⟨2 ^ 52 + Wasm.IEEE64.fraction v, Wasm.IEEE64.exponent v - 1, by omega, ?_⟩
    simp [Wasm.IEEE64.scaledMagnitude, he]

theorem abs_scaled (v : UInt64) :
    |(Wasm.IEEE64.scaledValue v : Int)| = (Wasm.IEEE64.scaledMagnitude v : Int) := by
  unfold Wasm.IEEE64.scaledValue
  split <;> simp

/-- The signed form of nearness: rounding the magnitude of `S` to a nearest representable
magnitude and restoring the sign is at least as close to `S` as any signed representable value. -/
theorem sign_near (RM m S sv : Int) (hm : 0 ≤ m) (hsv : |sv| = m) (hS : S ≠ 0)
    (hnear : |RM - (|S|)| ≤ |m - (|S|)|) :
    |(if S < 0 then -RM else RM) - S| ≤ |sv - S| := by
  have hsv' : sv = m ∨ sv = -m := by
    rcases abs_choice sv with h | h
    · left; rw [← hsv, h]
    · right; rw [← hsv, h, neg_neg]
  rcases lt_or_gt_of_ne hS with hneg | hpos
  · rw [ite_eq_left hneg]
    rw [abs_of_neg hneg] at hnear
    have e1 : -RM - S = -(RM - -S) := by ring
    rw [e1, abs_neg]
    rcases hsv' with h | h
    · rw [h]
      calc |RM - -S| ≤ |m - -S| := hnear
        _ ≤ |m| + |(-S)| := abs_sub _ _
        _ = m - S := by rw [abs_of_nonneg hm, abs_of_pos (by linarith)]; ring
        _ = |m - S| := by rw [abs_of_nonneg (by linarith)]
    · rw [h, show (-m) - S = -(m - -S) by ring, abs_neg]
      exact hnear
  · rw [ite_eq_right (by linarith)]
    rw [abs_of_pos hpos] at hnear
    rcases hsv' with h | h
    · rw [h]
      exact hnear
    · rw [h]
      calc |RM - S| ≤ |m - S| := hnear
        _ ≤ |m| + |S| := abs_sub _ _
        _ = m + S := by rw [abs_of_nonneg hm, abs_of_pos hpos]
        _ = |(-m) - S| := by rw [show (-m) - S = -(m + S) by ring, abs_neg,
            abs_of_nonneg (by linarith)]

/-- A rounded sum is nearest: no word lies closer to the exact sum. -/
theorem add_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a + value b| < 2 ^ 1023) (v : UInt64) :
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ |value v - (value a + value b)| := by
  set S := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b with hS
  have hSr : value a + value b = (S : ℝ) / 2 ^ 1074 := by
    rw [hS]
    simp only [value]
    push_cast
    ring
  have key : |(Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) : Int) - S| ≤
      |(Wasm.IEEE64.scaledValue v : Int) - S| := by
    by_cases hz : S = 0
    · have hadd : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = 0 := by
        have heq : Wasm.IEEE64.add a b =
            if Wasm.IEEE64.sign a && Wasm.IEEE64.sign b then Wasm.IEEE64.signMask true else 0 := by
          simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
            not_infinite_of_finite ha, not_infinite_of_finite hb, ← hS, hz]
        rw [heq]
        split <;> decide
      rw [hadd, hz]
      simp
    · have hmax : S.natAbs < 2 ^ 2097 := by
        have h1 : |(S : ℝ)| < 2 ^ 1023 * 2 ^ 1074 := by
          rw [hSr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
            div_lt_iff₀ (by positivity)] at hbound
          exact hbound
        have h2 : ((S.natAbs : Nat) : ℝ) < ((2 ^ 2097 : Nat) : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat]
          calc |(S : ℝ)| < 2 ^ 1023 * 2 ^ 1074 := h1
            _ = 2 ^ 2097 := by rw [← pow_add]
        exact_mod_cast h2
      have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (S < 0) S.natAbs := by
        simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
          not_infinite_of_finite ha, not_infinite_of_finite hb, ← hS, hz]
      have hv := F64Packing.scaledValue_pack (decide (S < 0)) S.natAbs hmax
      rw [heq, hv]
      obtain ⟨q, k, hq, hm⟩ := magnitude_repr v
      have hnear := roundedMagnitude_near S.natAbs q k hq
      rw [← hm, Int.natCast_natAbs] at hnear
      have hif : (if decide (S < 0) = true then -((roundedMagnitude S.natAbs : Nat) : Int)
          else ((roundedMagnitude S.natAbs : Nat) : Int)) =
          (if S < 0 then -((roundedMagnitude S.natAbs : Nat) : Int)
          else ((roundedMagnitude S.natAbs : Nat) : Int)) := by
        simp only [decide_eq_true_eq]
      rw [hif]
      exact sign_near _ _ S _ (Int.natCast_nonneg _) (abs_scaled v) hz hnear
  have hl : value (Wasm.IEEE64.add a b) - (value a + value b) =
      (((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) : Int) - S : Int) : ℝ) / 2 ^ 1074 := by
    rw [hSr]
    simp only [value]
    push_cast
    ring
  have hr : value v - (value a + value b) =
      (((Wasm.IEEE64.scaledValue v : Int) - S : Int) : ℝ) / 2 ^ 1074 := by
    rw [hSr]
    simp only [value]
    push_cast
    ring
  rw [hl, hr, abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast key

/-- A rounded difference is nearest. -/
theorem sub_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a - value b| < 2 ^ 1023) (v : UInt64) :
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ |value v - (value a - value b)| := by
  have hn := F64Magnitude.negate_value b hb
  have h := add_nearest a (Wasm.IEEE64.negate b) ha hn.1 (by rw [hn.2, ← sub_eq_add_neg]; exact hbound) v
  rw [hn.2, ← sub_eq_add_neg] at h
  exact h

theorem abs_value (v : UInt64) :
    |value v| = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
  have h := abs_scaled v
  simp only [value]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  have h' : |((Wasm.IEEE64.scaledValue v : Int) : ℝ)| = ((Wasm.IEEE64.scaledMagnitude v : Int) : ℝ) := by
    rw [← Int.cast_abs, h]
  rw [h']
  push_cast
  ring

/-- A word is a multiple of `2 ^ (e - 1)` scaled units, `e` its exponent field. -/
theorem grid_dvd (v : UInt64) :
    (2 : Int) ^ (Wasm.IEEE64.exponent v - 1) ∣ Wasm.IEEE64.scaledValue v := by
  have hd : 2 ^ (Wasm.IEEE64.exponent v - 1) ∣ Wasm.IEEE64.scaledMagnitude v := by
    by_cases he : Wasm.IEEE64.exponent v = 0
    · simp [he]
    · simp only [Wasm.IEEE64.scaledMagnitude, show (Wasm.IEEE64.exponent v == 0) = false by
        simpa using he, Bool.false_eq_true, ite_false]
      exact Dvd.intro_left _ rfl
  have hz : ((2 : Nat) ^ (Wasm.IEEE64.exponent v - 1) : Int) ∣
      (Wasm.IEEE64.scaledMagnitude v : Int) := Int.natCast_dvd_natCast.mpr hd
  push_cast at hz
  unfold Wasm.IEEE64.scaledValue
  split
  · exact (dvd_neg).mpr hz
  · exact hz

/-- A word's magnitude is below `2 ^ (53 + e - 1)` scaled units. -/
theorem grid_bound (v : UInt64) :
    |value v| < (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 := by
  rw [abs_value, div_lt_div_iff_of_pos_right (by positivity)]
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have h : Wasm.IEEE64.scaledMagnitude v < 2 ^ (53 + (Wasm.IEEE64.exponent v - 1)) := by
    by_cases he : Wasm.IEEE64.exponent v = 0
    · simp only [Wasm.IEEE64.scaledMagnitude, he, beq_self_eq_true, ite_true]
      calc Wasm.IEEE64.fraction v < 2 ^ 52 := hf
        _ ≤ 2 ^ (53 + (0 - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · simp only [Wasm.IEEE64.scaledMagnitude, show (Wasm.IEEE64.exponent v == 0) = false by
        simpa using he, Bool.false_eq_true, ite_false]
      rw [pow_add]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  exact_mod_cast h

/-- A normal word's magnitude is at least `2 ^ (52 + e - 1)` scaled units. -/
theorem grid_lower (v : UInt64) (he : 1 ≤ Wasm.IEEE64.exponent v) :
    (2 : ℝ) ^ (52 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 ≤ |value v| := by
  rw [abs_value, div_le_div_iff_of_pos_right (by positivity)]
  have h : 2 ^ (52 + (Wasm.IEEE64.exponent v - 1)) ≤ Wasm.IEEE64.scaledMagnitude v := by
    simp only [Wasm.IEEE64.scaledMagnitude, show (Wasm.IEEE64.exponent v == 0) = false by
      simp; omega, Bool.false_eq_true, ite_false]
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (by omega)
  exact_mod_cast h

/-- fdlibm's compensated difference: for `|w| ≤ |a| / 4` and `s = a - w` rounded, `a - s` and
`(a - s) - w` are exact, so `(a - s) - w` is the rounding error `a - w - s`. -/
theorem small_two_diff (a w : UInt64) (ha : Finite a) (hw : Finite w)
    (hsmall : 4 * |value w| ≤ |value a|) (hbig : |value a| < 2 ^ 1020) :
    Finite (Wasm.IEEE64.sub a w) ∧
      |value (Wasm.IEEE64.sub a w) - (value a - value w)| ≤ |value a - value w| / 2 ^ 53 ∧
      Finite (Wasm.IEEE64.sub a (Wasm.IEEE64.sub a w)) ∧
      value (Wasm.IEEE64.sub a (Wasm.IEEE64.sub a w)) = value a - value (Wasm.IEEE64.sub a w) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub a (Wasm.IEEE64.sub a w)) w) ∧
      value (Wasm.IEEE64.sub (Wasm.IEEE64.sub a (Wasm.IEEE64.sub a w)) w) =
        value a - value w - value (Wasm.IEEE64.sub a w) := by
  have hw0 := abs_nonneg (value w)
  have haw : |value a - value w| ≤ 5 / 4 * |value a| := by
    have := abs_sub (value a) (value w)
    linarith
  have haw' : 3 / 4 * |value a| ≤ |value a - value w| := by
    have := abs_sub_abs_le_abs_sub (value a) (value w)
    linarith
  obtain ⟨hsf, hse⟩ := sub_rel a w ha hw (by linarith)
  have hnear := sub_nearest a w ha hw (by linarith) a
  rw [show value a - (value a - value w) = value w by ring] at hnear
  generalize Wasm.IEEE64.sub a w = s at hsf hse hnear ⊢
  refine ⟨hsf, hse, ?_⟩
  -- The grid of `a`, one binade below.
  have heA : Wasm.IEEE64.exponent a ≤ 2043 := by
    by_contra hc
    have hl := grid_lower a (by omega)
    have : (2 : ℝ) ^ 1021 ≤ (2 : ℝ) ^ (52 + (Wasm.IEEE64.exponent a - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ 1020 < 2 ^ 1021 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith
  set ga := Wasm.IEEE64.exponent a - 1 with hga
  set g' := ga - 1 with hg'
  have hdA : (2 : Int) ^ g' ∣ Wasm.IEEE64.scaledValue a :=
    dvd_trans (pow_dvd_pow 2 (by omega)) (grid_dvd a)
  have haB := grid_bound a
  rw [← hga] at haB
  have hs2 : |value a| / 2 ≤ |value s| := by
    have := abs_sub_abs_le_abs_sub (value a - value w) (value s)
    rw [abs_sub_comm] at hse
    have h53 : |value a - value w| / 2 ^ 53 ≤ 5 / 4 * |value a| / 2 ^ 53 :=
      div_le_div_of_nonneg_right haw (by positivity)
    have : 5 / 4 * |value a| / 2 ^ 53 ≤ |value a| / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg (value a)]
    linarith
  have hdS : (2 : Int) ^ g' ∣ Wasm.IEEE64.scaledValue s := by
    by_cases hg0 : ga = 0
    · rw [hg', hg0]
      simp
    · apply dvd_of_value s hsf g'
      have hlow := grid_lower a (by omega)
      rw [← hga] at hlow
      have e : (2 : ℝ) ^ (52 + g') / 2 ^ 1074 = (2 : ℝ) ^ (52 + ga) / 2 ^ 1074 / 2 := by
        rw [show 52 + ga = (52 + g') + 1 by omega, pow_succ]
        ring
      rw [e]
      linarith
  have has : |value a - value s| ≤ |value a| / 2 := by
    have h := abs_sub_le (value a) (value a - value w) (value s)
    rw [show value a - (value a - value w) = value w by ring,
      abs_sub_comm (value a - value w) (value s)] at h
    linarith
  have hbnd : |value a| / 2 ≤ (2 : ℝ) ^ (53 + g') / 2 ^ 1074 := by
    by_cases hg0 : ga = 0
    · have : (2 : ℝ) ^ (53 + ga) / 2 ^ 1074 = 2 ^ (53 + g') / 2 ^ 1074 := by
        rw [hg', hg0]
      linarith
    · have e : (2 : ℝ) ^ (53 + g') / 2 ^ 1074 = (2 : ℝ) ^ (53 + ga) / 2 ^ 1074 / 2 := by
        rw [show 53 + ga = (53 + g') + 1 by omega, pow_succ]
        ring
      rw [e]
      linarith
  obtain ⟨hdf, hdv⟩ := sub_exact a s ha hsf g' (by omega) hdA hdS (has.trans hbnd)
  refine ⟨hdf, hdv, ?_⟩
  have hsd := scaled_of_value_sub a s _ hdv
  generalize Wasm.IEEE64.sub a s = d at hdf hdv hsd ⊢
  -- The grid of `w`.
  set gw := Wasm.IEEE64.exponent w - 1 with hgw
  have hdW : (2 : Int) ^ (min g' gw) ∣ Wasm.IEEE64.scaledValue w :=
    dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) (grid_dvd w)
  have hdD : (2 : Int) ^ (min g' gw) ∣ Wasm.IEEE64.scaledValue d := by
    rw [hsd]
    exact dvd_sub (dvd_trans (pow_dvd_pow 2 (min_le_left _ _)) hdA)
      (dvd_trans (pow_dvd_pow 2 (min_le_left _ _)) hdS)
  have hwB := grid_bound w
  rw [← hgw] at hwB
  have hdw : |value d - value w| ≤ |value w| := by
    rw [hdv, show value a - value s - value w = -(value s - (value a - value w)) by ring, abs_neg]
    exact hnear
  have hmin : |value d - value w| ≤ (2 : ℝ) ^ (53 + min g' gw) / 2 ^ 1074 := by
    rcases min_choice g' gw with h | h <;> rw [h]
    · linarith
    · linarith
  obtain ⟨hef, hev⟩ := sub_exact d w hdf hw (min g' gw) (by omega) hdD hdW hmin
  refine ⟨hef, ?_⟩
  rw [hev, hdv]
  ring

#print axioms roundShift_near
#print axioms roundedMagnitude_near
#print axioms add_nearest
#print axioms sub_nearest
#print axioms grid_dvd
#print axioms grid_bound
#print axioms grid_lower
#print axioms small_two_diff

end Verified.Examples.TrigNearest
