import LeanExe.ProofKit.F64TopPack
import LeanExe.ProofKit.F64TwoSum
import LeanExe.ProofKit.F64Admissibility

/-!
Exact sums and Dekker's error-free sum up to the overflow threshold.  `F64GridExact` packs a grid
value `z 2^shift` with `|z| ≤ 2^53` for `shift ≤ 2043`, below `2^1023`, and
`F64TwoSum.fast_two_sum` takes `|a| < 2^900`.  With `F64TopPack.pack_top` the packing holds while
`|z| 2^shift` stays below the scaled threshold less `2^2044` (`signed_grid_packing_top`), and with
it the exact sums and differences (`grid_add_top`, `sub_grid_top`), the nearest rounding of a sum
(`add_rounded_top`), the grid of a rounded sum (`rounded_dvd_top`), and the error-free sum for
`|a| + |b| < 2^1024 - 2^971` (`fast_two_sum_top`), with the proofs of the originals.  The margin
`2^971` keeps the even neighbour of the sum, which the proof compares with the rounded sum, finite.
-/

namespace LeanExe.ProofKit.F64TopTwoSum
open CodeLib.IEEE64 F64RoundNearest F64TwoSum

set_option exponentiation.threshold 4096

theorem signed_grid_packing_top (z : Int) (shift : Nat)
    (hz : z.natAbs ≤ 2 ^ 53) (hmax : z.natAbs * 2 ^ shift + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift)) ∧
    Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift)) =
      z * 2 ^ shift := by
  have hp := F64TopPack.pack_top (z < 0) _ hmax
  have hv : Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift)) =
      if (z < 0) then -(roundedMagnitude (z.natAbs * 2 ^ shift) : Int)
      else roundedMagnitude (z.natAbs * 2 ^ shift) := by
    simp [Wasm.IEEE64.scaledValue, hp.2.1, hp.2.2]
  rw [F64GridExact.roundedMagnitude_shifted_small _ _ hz] at hv
  refine ⟨hp.1, ?_⟩
  rw [hv]
  by_cases hn : z < 0
  · rw [ite_eq_left (by simpa using hn)]
    have habs := Int.eq_neg_natAbs_of_nonpos hn.le
    simp only [Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
    calc
      _ = (-(z.natAbs : Int)) * (2 : Int) ^ shift := by ring
      _ = z * (2 : Int) ^ shift := congrArg (fun x : Int => x * 2 ^ shift) habs.symm
  · rw [ite_eq_right (by simpa using hn)]
    have habs := Int.eq_natAbs_of_nonneg (le_of_not_gt hn)
    simp only [Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
    exact congrArg (fun x : Int => x * 2 ^ shift) habs.symm

theorem grid_add_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (z : Int) (shift : Nat)
    (hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = z * 2 ^ shift)
    (hz : z.natAbs ≤ 2 ^ 53) (hmax : z.natAbs * 2 ^ shift + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.add a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) =
      Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
  by_cases hz0 : z = 0
  · have hs0 : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0 := by
      rw [hsum, hz0, zero_mul]
    have hmax0 : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs <
        2 ^ 2097 := by rw [hs0]; norm_num
    have hp := F64AddBounds.add_scaled_relative a b ha hb hmax0
    have he := hp.2
    rw [hs0] at he
    norm_num at he
    have he0 : |Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b)| = 0 := by
      have hn := abs_nonneg (Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b))
      omega
    exact ⟨hp.1, by rw [hs0]; exact abs_eq_zero.mp he0⟩
  · have hd : 0 < (2 : Int) ^ shift := by positivity
    have hnz : z * (2 : Int) ^ shift ≠ 0 := mul_ne_zero hz0 hd.ne'
    have hni : z * (2 : Int) ^ shift < 0 ↔ z < 0 := by
      constructor
      · intro h
        by_contra hzn
        exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hzn) hd.le)) h
      · intro hzn
        have hm := mul_pos (neg_pos.mpr hzn) hd
        nlinarith only [hm]
    have habs : (z * (2 : Int) ^ shift).natAbs = z.natAbs * 2 ^ shift := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      rfl
    have heq : Wasm.IEEE64.add a b =
        Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift) := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, hsum, hnz, hni, habs]
    rw [heq, hsum]
    exact signed_grid_packing_top z shift hz hmax

/-- `grid_add_exact` for a difference. -/
theorem sub_grid_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (z : Int) (shift : Nat)
    (hdiff : Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b = z * 2 ^ shift)
    (hz : z.natAbs ≤ 2 ^ 53) (hmax : z.natAbs * 2 ^ shift + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.sub a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) =
      Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b := by
  have hneg := negate_spec b hb
  have h := grid_add_top a (Wasm.IEEE64.negate b) ha hneg.1 z shift
    (by rw [hneg.2, ← sub_eq_add_neg]; exact hdiff) hz hmax
  rw [hneg.2, ← sub_eq_add_neg] at h
  exact h

theorem add_rounded_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h0 : value a + value b ≠ 0) (hmax : |value a + value b| < 2 ^ 1024 - 2 ^ 970) :
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
  have hn : S.natAbs + 2 ^ 2044 < 2 ^ 2098 := by
    rw [hSv, abs_div, abs_of_pos h2, div_lt_iff₀ h2, hcast] at hmax
    have h1 : (S.natAbs : ℝ) + 2 ^ 2044 < 2 ^ 2098 := by
      have : (2 ^ 1024 - 2 ^ 970 : ℝ) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2044 := by norm_num
      linarith
    exact_mod_cast h1
  have heq : Wasm.IEEE64.add a b =
      Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs := by
    have hne : (S == 0) = false := by simpa using hS0
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hSdef, hne]
  obtain ⟨hf, hmag, hsign⟩ := F64TopPack.pack_top (decide (S < 0)) S.natAbs hn
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
    rw [F64RoundNearest.abs_value, F64RoundNearest.abs_value v, hmag, hSv, abs_div, abs_of_pos h2, hcast,
      ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos h2]
    exact div_le_div_of_nonneg_right (F64RoundNearest.rounded_nearest _ v) h2.le

theorem rounded_dvd_top (c : UInt64) (S : ℝ) (hc : Rounded c S) (g : ℕ) (hg : g ≤ 2044)
    (hS : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |S|) :
    (2 : ℤ) ^ (g + 1) ∣ Wasm.IEEE64.scaledValue c := by
  obtain ⟨v, -, hvv⟩ : ∃ v : UInt64, Finite v ∧ Wasm.IEEE64.scaledValue v = 2 ^ 52 * 2 ^ (g + 1) :=
    ⟨_, signed_grid_packing_top (2 ^ 52) (g + 1) (by norm_num) (by
      have h1 : (2 ^ 52 : ℤ).natAbs * 2 ^ (g + 1) ≤ 2 ^ 52 * 2 ^ 2045 := by
        rw [show (2 ^ 52 : ℤ).natAbs = 2 ^ 52 from rfl]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : (2 : ℕ) ^ 52 * 2 ^ 2045 + 2 ^ 2044 < 2 ^ 2098 := by norm_num
      omega)⟩
  have hvv' : Wasm.IEEE64.scaledValue v = 2 ^ (53 + g) := by
    rw [hvv, ← pow_add]
    congr 1
    omega
  have hvabs : |value v| = 2 ^ (53 + g) / 2 ^ 1074 := by
    rw [value, hvv', abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    push_cast
    rw [abs_of_pos (by positivity)]
  have h := hc.2.2.2 v
  rw [hvabs, abs_of_nonpos (by linarith : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 - |S| ≤ 0)] at h
  have hcabs : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value c| := by
    have := neg_abs_le (|value c| - |S|)
    linarith
  have hmag : 2 ^ (53 + g) ≤ Wasm.IEEE64.scaledMagnitude c := by
    rw [F64RoundNearest.abs_value] at hcabs
    have h := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp hcabs
    exact_mod_cast h
  have hfc : Wasm.IEEE64.fraction c < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hec : g + 2 ≤ Wasm.IEEE64.exponent c := by
    by_contra hlt
    push Not at hlt
    by_cases he0 : Wasm.IEEE64.exponent c = 0
    · have : Wasm.IEEE64.scaledMagnitude c < 2 ^ 52 := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, he0, ite_true]
        exact hfc
      have : 2 ^ 52 ≤ 2 ^ (53 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hm : Wasm.IEEE64.scaledMagnitude c < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent c - 1) := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, he0, ite_false]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      have : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent c - 1) ≤ 2 ^ (53 + g) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨M, -, hM⟩ := sv_grid c
  rw [hM]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) M

theorem fast_two_sum_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hab : |value b| ≤ |value a|) (hlim : |value a| + |value b| < 2 ^ 1024 - 2 ^ 971) :
    Finite (Wasm.IEEE64.add a b) ∧
      Finite (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) ∧
      value (Wasm.IEEE64.add a b) +
          value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) =
        value a + value b ∧
      Rounded (Wasm.IEEE64.add a b) (value a + value b) ∧
      |value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a))| ≤ |value b| := by
  set X := Wasm.IEEE64.scaledValue a with hX
  set Y := Wasm.IEEE64.scaledValue b with hY
  have h1074 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hva : value a = (X : ℝ) / 2 ^ 1074 := rfl
  have hvb : value b = (Y : ℝ) / 2 ^ 1074 := rfl
  -- exponents and grids
  have hmag : Wasm.IEEE64.scaledMagnitude b ≤ Wasm.IEEE64.scaledMagnitude a := by
    rw [abs_value, abs_value] at hab
    have := (div_le_div_iff_of_pos_right h1074).mp hab
    exact_mod_cast this
  have heab := exponent_le_of_magnitude a b hmag
  have hea := F64Admissibility.finite_exponent_bound a ha
  set g := Wasm.IEEE64.exponent b - 1 with hg
  obtain ⟨Mb, hMb, hYM⟩ := sv_grid b
  obtain ⟨Ma, hMa, hXM⟩ := sv_grid a
  have hXg : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g)) * 2 ^ g := by
    rw [hX, hXM, mul_assoc, ← pow_add]
    congr 2
    omega
  set A := Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g) with hA
  have hYg : Y = Mb * 2 ^ g := hYM
  have hpg : (0 : ℤ) < 2 ^ g := by positivity
  set N := A + Mb with hN
  have hsum : X + Y = N * 2 ^ g := by rw [hXg, hYg, hN]; ring
  have hgle : g ≤ 2045 := by omega
  -- the scaled bounds of the sum and of `b`
  have hXY : |X + Y| + 2 ^ 2045 < 2 ^ 2098 := by
    have h1 : |value a + value b| < 2 ^ 1024 - 2 ^ 971 := (abs_add_le _ _).trans_lt hlim
    rw [hva, hvb, ← add_div, abs_div, abs_of_pos h1074, div_lt_iff₀ h1074] at h1
    have h2 : |((X + Y : ℤ) : ℝ)| + 2 ^ 2045 < 2 ^ 2098 := by
      have : (2 ^ 1024 - 2 ^ 971 : ℝ) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2045 := by norm_num
      push_cast
      linarith
    rw [← Int.cast_abs] at h2
    exact_mod_cast h2
  have hY2 : 2 * |Y| + 2 ^ 2045 < 2 ^ 2098 := by
    have h1 : 2 * |value b| < 2 ^ 1024 - 2 ^ 971 := by linarith
    rw [hvb, abs_div, abs_of_pos h1074] at h1
    have h2 : 2 * |(Y : ℝ)| + 2 ^ 2045 < 2 ^ 2098 := by
      have : (2 ^ 1024 - 2 ^ 971 : ℝ) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2045 := by norm_num
      have h3 : 2 * |(Y : ℝ)| < (2 ^ 1024 - 2 ^ 971) * 2 ^ 1074 := by
        rw [mul_div_assoc'] at h1
        rwa [div_lt_iff₀ h1074] at h1
      linarith
    rw [← Int.cast_abs] at h2
    exact_mod_cast h2
  have habsN (z : ℤ) (sh : ℕ) (h : |z * 2 ^ sh| + 2 ^ 2045 < 2 ^ 2098) :
      z.natAbs * 2 ^ sh + 2 ^ 2044 < 2 ^ 2098 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ sh)] at h
    have h1 : ((z.natAbs * 2 ^ sh : ℕ) : ℤ) = |z| * 2 ^ sh := by
      simp [Int.natCast_natAbs]
    have h2 : ((z.natAbs * 2 ^ sh + 2 ^ 2044 : ℕ) : ℤ) < ((2 ^ 2098 : ℕ) : ℤ) := by
      push_cast
      push_cast at h1
      have : (2 : ℤ) ^ 2044 < 2 ^ 2045 := by norm_num
      linarith
    exact_mod_cast h2
  by_cases hsmall : N.natAbs ≤ 2 ^ 53
  · -- the sum is exact
    obtain ⟨hsf, hsv⟩ := grid_add_top a b ha hb N g hsum hsmall
      (habsN N g (by rw [← hsum]; exact hXY))
    set s := Wasm.IEEE64.add a b
    obtain ⟨hzf, hzv⟩ := sub_grid_top s a hsf ha Mb g
      (by rw [hsv, ← hX, ← hY, hYg]; ring) (by omega)
      (habsN Mb g (by rw [← hYg]; have := abs_nonneg Y; linarith))
    set z := Wasm.IEEE64.sub s a
    obtain ⟨htf, htv⟩ := sub_grid_top b z hb hzf 0 0
      (by rw [hzv, hsv, ← hX, ← hY]; ring) (by norm_num) (by norm_num)
    have hvs : value s = value a + value b := by
      rw [value, hsv, hva, hvb]
      push_cast
      ring
    have hvt : value (Wasm.IEEE64.sub b z) = 0 := by
      rw [value, htv, hzv, hsv, ← hX, ← hY]
      simp
    refine ⟨hsf, htf, by rw [hvs, hvt, add_zero], ?_, by rw [hvt, abs_zero]; exact abs_nonneg _⟩
    rw [← hvs]
    exact rounded_self s hsf
  · -- the sum has more than 53 bits on the grid of `2 ^ g`
    push Not at hsmall
    have hS : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value a + value b| := by
      rw [hva, hvb, ← add_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      have : ((2 : ℤ) ^ (53 + g) : ℝ) ≤ |((X + Y : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        have h2 : (2 : ℤ) ^ (53 + g) ≤ |X + Y| := by
          rw [hsum, abs_mul, abs_of_pos hpg, pow_add]
          apply mul_le_mul_of_nonneg_right _ hpg.le
          have : ((2 ^ 53 : ℕ) : ℤ) < (N.natAbs : ℤ) := by exact_mod_cast hsmall
          rw [Int.natCast_natAbs] at this
          push_cast at this
          linarith
        exact_mod_cast h2
      push_cast at this
      linarith
    have hS0 : value a + value b ≠ 0 := by
      intro h
      rw [h, abs_zero] at hS
      have : (0 : ℝ) < 2 ^ (53 + g) / 2 ^ 1074 := by positivity
      linarith
    have hmax : |value a + value b| < 2 ^ 1024 - 2 ^ 970 := by
      calc |value a + value b| ≤ |value a| + |value b| := abs_add_le _ _
        _ < 2 ^ 1024 - 2 ^ 971 := hlim
        _ ≤ 2 ^ 1024 - 2 ^ 970 := by norm_num
    have hsr := add_rounded_top a b ha hb hS0 hmax
    have hg44 : g ≤ 2044 := by
      by_contra hg45
      have hg' : g = 2045 := by omega
      rw [hg'] at hS
      have : (2 : ℝ) ^ (53 + 2045) / 2 ^ 1074 = 2 ^ 1024 := by norm_num
      linarith
    set s := Wasm.IEEE64.add a b with hsdef
    have hsf : Finite s := hsr.1
    have hdvd := rounded_dvd_top s _ hsr g hg44 hS
    obtain ⟨K, hK⟩ := hdvd
    set Sv := Wasm.IEEE64.scaledValue s with hSv
    have hvsS : value s = (Sv : ℝ) / 2 ^ 1074 := rfl
    have hscale : ∀ T : ℤ, value s - (value a + value b) = ((Sv - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 ∧
        (T : ℝ) / 2 ^ 1074 - (value a + value b) = ((T - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 := by
      intro T
      constructor <;> (rw [hva, hvb]; try rw [hvsS]) <;> push_cast <;> ring
    have hcmp : ∀ v : UInt64, |Sv - (X + Y)| ≤ |Wasm.IEEE64.scaledValue v - (X + Y)| := by
      intro v
      have h := rounded_le hsr v
      rw [(hscale (Wasm.IEEE64.scaledValue v)).1, show value v =
        (Wasm.IEEE64.scaledValue v : ℝ) / 2 ^ 1074 from rfl,
        (hscale (Wasm.IEEE64.scaledValue v)).2, abs_div, abs_div, abs_of_pos h1074] at h
      have h2 := (div_le_div_iff_of_pos_right h1074).mp h
      rw [← Int.cast_abs, ← Int.cast_abs] at h2
      exact_mod_cast h2
    -- the error of `s` is at most `|b|`
    have herr : |Sv - (X + Y)| ≤ |Y| := by
      have := hcmp a
      rwa [← hX, show X - (X + Y) = -Y by ring, abs_neg] at this
    -- `z = s - a` is exact
    have hzex : ∃ (w : ℤ) (sh : ℕ), Sv - X = w * 2 ^ sh ∧ w.natAbs ≤ 2 ^ 53 ∧
        |w * 2 ^ sh| + 2 ^ 2045 < 2 ^ 2098 := by
      by_cases hlt : g + 1 ≤ Wasm.IEEE64.exponent a - 1
      · have hXg1 : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) := by
          rw [hX, hXM, mul_assoc, ← pow_add]
          congr 2
          omega
        refine ⟨K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1)), g + 1, ?_, ?_, ?_⟩
        rotate_left 2
        · rw [show (K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) = Sv - X by
            rw [hK, hXg1]; ring]
          have := abs_sub_le Sv (X + Y) X
          rw [show X + Y - X = Y by ring] at this
          linarith [herr]
        · rw [hK, hXg1]
          ring
        · have hb2 : |Sv - X| ≤ 2 * |Y| := by
            have := abs_sub_le Sv (X + Y) X
            rw [show X + Y - X = Y by ring] at this
            linarith
          apply natAbs_le_of_abs (g + 1)
          have heq : (K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) =
              Sv - X := by rw [hK, hXg1]; ring
          rw [heq]
          calc |Sv - X| ≤ 2 * |Y| := hb2
            _ = ((2 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
            _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((2 : ℕ) * 2 ^ g) := mb_bound Mb hMb 2 g
            _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ (g + 1) := by rw [pow_succ]; push_cast; ring
      · -- equal exponents: the error is at most `2 ^ g`
        have heq : Wasm.IEEE64.exponent a - 1 = g := by omega
        have hAeq : A = Ma := by rw [hA, show Wasm.IEEE64.exponent a - 1 - g = 0 by omega]; ring
        have hNlt : N.natAbs < 2 ^ 54 := by
          rw [hN, hAeq]
          have := Int.natAbs_add_le Ma Mb
          omega
        -- the even neighbour of `N` on the grid of `2 ^ (g + 1)`
        set R : ℤ := (N + N % 2) / 2 with hR
        have hRN : 2 * R = N + N % 2 := by
          rw [hR]
          omega
        have hRabs : R.natAbs ≤ 2 ^ 53 := by omega
        have hRmax : R.natAbs * 2 ^ (g + 1) + 2 ^ 2044 < 2 ^ 2098 := by
          have hR1 : (R.natAbs : ℤ) * 2 ^ (g + 1) ≤ |X + Y| + 2 ^ g := by
            rw [hsum, abs_mul, abs_of_pos hpg, pow_succ, Int.natCast_natAbs]
            have hRb : |R| * 2 ≤ |N| + 1 := by
              have e0 := Int.emod_nonneg N (by norm_num : (2 : ℤ) ≠ 0)
              have e1 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 2)
              rcases abs_cases R with ⟨hr, _⟩ | ⟨hr, _⟩ <;>
                rcases abs_cases N with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rw [hr, hn] <;> omega
            nlinarith [hpg]
          have hg2 : (2 : ℤ) ^ g ≤ 2 ^ 2044 := pow_le_pow_right₀ (by norm_num) hg44
          have h3 : ((R.natAbs * 2 ^ (g + 1) + 2 ^ 2044 : ℕ) : ℤ) < ((2 ^ 2098 : ℕ) : ℤ) := by
            push_cast
            have : (2 : ℤ) ^ 2044 + 2 ^ 2044 = 2 ^ 2045 := by norm_num
            push_cast at hR1
            linarith [hXY]
          exact_mod_cast h3
        obtain ⟨hvf, hvv⟩ := signed_grid_packing_top R (g + 1) hRabs hRmax
        set v := Wasm.IEEE64.roundScaledMagnitude (R < 0) (R.natAbs * 2 ^ (g + 1))
        have hdist : |Wasm.IEEE64.scaledValue v - (X + Y)| ≤ 2 ^ g := by
          rw [hvv, hsum, pow_succ, show R * (2 ^ g * 2) - N * 2 ^ g = (2 * R - N) * 2 ^ g by ring,
            hRN, show N + N % 2 - N = N % 2 by ring, abs_mul, abs_of_pos hpg]
          have : |N % 2| ≤ 1 := by
            have h0 := Int.emod_nonneg N (by norm_num : (2 : ℤ) ≠ 0)
            have h1 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 2)
            rw [abs_of_nonneg h0]
            omega
          nlinarith
        have herr2 : |Sv - (X + Y)| ≤ 2 ^ g := (hcmp v).trans hdist
        refine ⟨(Sv - X) / 2 ^ g, g, ?_, ?_, ?_⟩
        rotate_left 2
        · have hd : (2 : ℤ) ^ g ∣ Sv - X := by
            rw [hK, hXg, hAeq, pow_succ]
            exact ⟨K * 2 - Ma, by ring⟩
          rw [Int.ediv_mul_cancel hd]
          have := abs_sub_le Sv (X + Y) X
          rw [show X + Y - X = Y by ring] at this
          linarith [herr]
        · have hd : (2 : ℤ) ^ g ∣ Sv - X := by
            rw [hK, hXg, hAeq, pow_succ]
            exact ⟨K * 2 - Ma, by ring⟩
          rw [Int.ediv_mul_cancel hd]
        · have hd : (2 : ℤ) ^ g ∣ Sv - X := by
            rw [hK, hXg, hAeq, pow_succ]
            exact ⟨K * 2 - Ma, by ring⟩
          apply natAbs_le_of_abs g
          rw [Int.ediv_mul_cancel hd]
          have hYa : |Y| = |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]
          have hM1 : |Mb| + 1 ≤ ((2 ^ 53 : ℕ) : ℤ) := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast hMb
          calc |Sv - X| ≤ |Sv - (X + Y)| + |Y| := by
                have := abs_sub_le Sv (X + Y) X
                rw [show X + Y - X = Y by ring] at this
                exact this
            _ ≤ (|Mb| + 1) * 2 ^ g := by rw [hYa]; linarith
            _ ≤ ((2 ^ 53 : ℕ) : ℤ) * 2 ^ g := mul_le_mul_of_nonneg_right hM1 hpg.le
    obtain ⟨w, sh, hw, hwabs, hsh⟩ := hzex
    obtain ⟨hzf, hzv⟩ := sub_grid_top s a hsf ha w sh hw hwabs (habsN w sh hsh)
    set z := Wasm.IEEE64.sub s a
    -- `t = b - z` is the rounding error of `s`
    have hd : (2 : ℤ) ^ g ∣ X + Y - Sv := by
      rw [hsum, hK, pow_succ]
      exact ⟨N - K * 2, by ring⟩
    obtain ⟨htf, htv⟩ := sub_grid_top b z hb hzf ((X + Y - Sv) / 2 ^ g) g
      (by rw [Int.ediv_mul_cancel hd, hzv, ← hSv, ← hX, ← hY]; ring)
      (by
        apply natAbs_le_of_abs g
        rw [Int.ediv_mul_cancel hd, show X + Y - Sv = -(Sv - (X + Y)) by ring, abs_neg]
        calc |Sv - (X + Y)| ≤ |Y| := herr
          _ = ((1 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
          _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((1 : ℕ) * 2 ^ g) := mb_bound Mb hMb 1 g
          _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ g := by push_cast; ring)
      (habsN _ g (by
        rw [Int.ediv_mul_cancel hd, show X + Y - Sv = -(Sv - (X + Y)) by ring, abs_neg]
        have := abs_nonneg Y
        linarith [herr]))
    have hvt : value (Wasm.IEEE64.sub b z) = (((X + Y - Sv) : ℤ) : ℝ) / 2 ^ 1074 := by
      rw [value, htv, hzv, ← hSv, ← hX, ← hY]
      congr 1
      push_cast
      ring
    refine ⟨hsf, htf, ?_, hsr, ?_⟩
    · rw [hvt, hva, hvb, value, ← hSv]
      push_cast
      ring
    · rw [hvt, hvb, abs_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      rw [show X + Y - Sv = -(Sv - (X + Y)) by ring, Int.cast_neg, abs_neg, ← Int.cast_abs,
        ← Int.cast_abs]
      exact_mod_cast herr

/-- **Dekker's error-free sum with a small addend** up to the overflow threshold: for
`|b| ≤ |a|` with the exponent of `b` below that of `a` and `|b| < 2^1022`, it is enough that
`|a + b|` lies below the threshold. -/
theorem fast_two_sum_small (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hab : |value b| ≤ |value a|) (hexp : Wasm.IEEE64.exponent b < Wasm.IEEE64.exponent a)
    (hea2 : 2 ≤ Wasm.IEEE64.exponent a)
    (hb2 : |value b| < 2 ^ 1022) (hlim : |value a + value b| < 2 ^ 1024 - 2 ^ 970) :
    Finite (Wasm.IEEE64.add a b) ∧
      Finite (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) ∧
      value (Wasm.IEEE64.add a b) +
          value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) =
        value a + value b ∧
      Rounded (Wasm.IEEE64.add a b) (value a + value b) ∧
      |value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a))| ≤ |value b| := by
  set X := Wasm.IEEE64.scaledValue a with hX
  set Y := Wasm.IEEE64.scaledValue b with hY
  have h1074 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hva : value a = (X : ℝ) / 2 ^ 1074 := rfl
  have hvb : value b = (Y : ℝ) / 2 ^ 1074 := rfl
  -- exponents and grids
  have hmag : Wasm.IEEE64.scaledMagnitude b ≤ Wasm.IEEE64.scaledMagnitude a := by
    rw [abs_value, abs_value] at hab
    have := (div_le_div_iff_of_pos_right h1074).mp hab
    exact_mod_cast this
  have heab := exponent_le_of_magnitude a b hmag
  have hea := F64Admissibility.finite_exponent_bound a ha
  set g := Wasm.IEEE64.exponent b - 1 with hg
  obtain ⟨Mb, hMb, hYM⟩ := sv_grid b
  obtain ⟨Ma, hMa, hXM⟩ := sv_grid a
  have hXg : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g)) * 2 ^ g := by
    rw [hX, hXM, mul_assoc, ← pow_add]
    congr 2
    omega
  set A := Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g) with hA
  have hYg : Y = Mb * 2 ^ g := hYM
  have hpg : (0 : ℤ) < 2 ^ g := by positivity
  set N := A + Mb with hN
  have hsum : X + Y = N * 2 ^ g := by rw [hXg, hYg, hN]; ring
  have hgle : g ≤ 2045 := by omega
  -- the scaled bounds of the sum and of `b`
  have hXY : |X + Y| + 2 ^ 2044 < 2 ^ 2098 := by
    have h1 := hlim
    rw [hva, hvb, ← add_div, abs_div, abs_of_pos h1074, div_lt_iff₀ h1074] at h1
    have h2 : |((X + Y : ℤ) : ℝ)| + 2 ^ 2044 < 2 ^ 2098 := by
      have : (2 ^ 1024 - 2 ^ 970 : ℝ) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2044 := by norm_num
      push_cast
      linarith
    rw [← Int.cast_abs] at h2
    exact_mod_cast h2
  have hY2 : 2 * |Y| + 2 ^ 2045 < 2 ^ 2098 := by
    have h1 : 2 * |value b| < 2 ^ 1023 := by linarith
    rw [hvb, abs_div, abs_of_pos h1074] at h1
    have h2 : 2 * |(Y : ℝ)| + 2 ^ 2045 < 2 ^ 2098 := by
      have h3 : 2 * |(Y : ℝ)| < 2 ^ 1023 * 2 ^ 1074 := by
        rw [mul_div_assoc'] at h1
        rwa [div_lt_iff₀ h1074] at h1
      have : (2 : ℝ) ^ 1023 * 2 ^ 1074 + 2 ^ 2045 < 2 ^ 2098 := by norm_num
      linarith
    rw [← Int.cast_abs] at h2
    exact_mod_cast h2
  have habsN (z : ℤ) (sh : ℕ) (h : |z * 2 ^ sh| + 2 ^ 2045 < 2 ^ 2098) :
      z.natAbs * 2 ^ sh + 2 ^ 2044 < 2 ^ 2098 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ sh)] at h
    have h1 : ((z.natAbs * 2 ^ sh : ℕ) : ℤ) = |z| * 2 ^ sh := by
      simp [Int.natCast_natAbs]
    have h2 : ((z.natAbs * 2 ^ sh + 2 ^ 2044 : ℕ) : ℤ) < ((2 ^ 2098 : ℕ) : ℤ) := by
      push_cast
      push_cast at h1
      have : (2 : ℤ) ^ 2044 < 2 ^ 2045 := by norm_num
      linarith
    exact_mod_cast h2
  by_cases hsmall : N.natAbs ≤ 2 ^ 53
  · -- the sum is exact
    obtain ⟨hsf, hsv⟩ := grid_add_top a b ha hb N g hsum hsmall
      (by
        have h1 : |N * 2 ^ g| + 2 ^ 2044 < 2 ^ 2098 := by rw [← hsum]; exact hXY
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ g)] at h1
        have h2 : ((N.natAbs * 2 ^ g + 2 ^ 2044 : ℕ) : ℤ) < ((2 ^ 2098 : ℕ) : ℤ) := by
          have e : ((N.natAbs * 2 ^ g : ℕ) : ℤ) = |N| * 2 ^ g := by simp [Int.natCast_natAbs]
          push_cast
          push_cast at e
          linarith
        exact_mod_cast h2)
    set s := Wasm.IEEE64.add a b
    obtain ⟨hzf, hzv⟩ := sub_grid_top s a hsf ha Mb g
      (by rw [hsv, ← hX, ← hY, hYg]; ring) (by omega)
      (habsN Mb g (by rw [← hYg]; have := abs_nonneg Y; linarith))
    set z := Wasm.IEEE64.sub s a
    obtain ⟨htf, htv⟩ := sub_grid_top b z hb hzf 0 0
      (by rw [hzv, hsv, ← hX, ← hY]; ring) (by norm_num) (by norm_num)
    have hvs : value s = value a + value b := by
      rw [value, hsv, hva, hvb]
      push_cast
      ring
    have hvt : value (Wasm.IEEE64.sub b z) = 0 := by
      rw [value, htv, hzv, hsv, ← hX, ← hY]
      simp
    refine ⟨hsf, htf, by rw [hvs, hvt, add_zero], ?_, by rw [hvt, abs_zero]; exact abs_nonneg _⟩
    rw [← hvs]
    exact rounded_self s hsf
  · -- the sum has more than 53 bits on the grid of `2 ^ g`
    push Not at hsmall
    have hS : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value a + value b| := by
      rw [hva, hvb, ← add_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      have : ((2 : ℤ) ^ (53 + g) : ℝ) ≤ |((X + Y : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        have h2 : (2 : ℤ) ^ (53 + g) ≤ |X + Y| := by
          rw [hsum, abs_mul, abs_of_pos hpg, pow_add]
          apply mul_le_mul_of_nonneg_right _ hpg.le
          have : ((2 ^ 53 : ℕ) : ℤ) < (N.natAbs : ℤ) := by exact_mod_cast hsmall
          rw [Int.natCast_natAbs] at this
          push_cast at this
          linarith
        exact_mod_cast h2
      push_cast at this
      linarith
    have hS0 : value a + value b ≠ 0 := by
      intro h
      rw [h, abs_zero] at hS
      have : (0 : ℝ) < 2 ^ (53 + g) / 2 ^ 1074 := by positivity
      linarith
    have hmax : |value a + value b| < 2 ^ 1024 - 2 ^ 970 := hlim
    have hsr := add_rounded_top a b ha hb hS0 hmax
    have hg44 : g ≤ 2044 := by
      by_contra hg45
      have hg' : g = 2045 := by omega
      rw [hg'] at hS
      have : (2 : ℝ) ^ (53 + 2045) / 2 ^ 1074 = 2 ^ 1024 := by norm_num
      linarith
    set s := Wasm.IEEE64.add a b with hsdef
    have hsf : Finite s := hsr.1
    have hdvd := rounded_dvd_top s _ hsr g hg44 hS
    obtain ⟨K, hK⟩ := hdvd
    set Sv := Wasm.IEEE64.scaledValue s with hSv
    have hvsS : value s = (Sv : ℝ) / 2 ^ 1074 := rfl
    have hscale : ∀ T : ℤ, value s - (value a + value b) = ((Sv - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 ∧
        (T : ℝ) / 2 ^ 1074 - (value a + value b) = ((T - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 := by
      intro T
      constructor <;> (rw [hva, hvb]; try rw [hvsS]) <;> push_cast <;> ring
    have hcmp : ∀ v : UInt64, |Sv - (X + Y)| ≤ |Wasm.IEEE64.scaledValue v - (X + Y)| := by
      intro v
      have h := rounded_le hsr v
      rw [(hscale (Wasm.IEEE64.scaledValue v)).1, show value v =
        (Wasm.IEEE64.scaledValue v : ℝ) / 2 ^ 1074 from rfl,
        (hscale (Wasm.IEEE64.scaledValue v)).2, abs_div, abs_div, abs_of_pos h1074] at h
      have h2 := (div_le_div_iff_of_pos_right h1074).mp h
      rw [← Int.cast_abs, ← Int.cast_abs] at h2
      exact_mod_cast h2
    -- the error of `s` is at most `|b|`
    have herr : |Sv - (X + Y)| ≤ |Y| := by
      have := hcmp a
      rwa [← hX, show X - (X + Y) = -Y by ring, abs_neg] at this
    -- `z = s - a` is exact
    have hzex : ∃ (w : ℤ) (sh : ℕ), Sv - X = w * 2 ^ sh ∧ w.natAbs ≤ 2 ^ 53 ∧
        |w * 2 ^ sh| + 2 ^ 2045 < 2 ^ 2098 := by
      by_cases hlt : g + 1 ≤ Wasm.IEEE64.exponent a - 1
      · have hXg1 : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) := by
          rw [hX, hXM, mul_assoc, ← pow_add]
          congr 2
          omega
        refine ⟨K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1)), g + 1, ?_, ?_, ?_⟩
        rotate_left 2
        · rw [show (K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) = Sv - X by
            rw [hK, hXg1]; ring]
          have := abs_sub_le Sv (X + Y) X
          rw [show X + Y - X = Y by ring] at this
          linarith [herr]
        · rw [hK, hXg1]
          ring
        · have hb2 : |Sv - X| ≤ 2 * |Y| := by
            have := abs_sub_le Sv (X + Y) X
            rw [show X + Y - X = Y by ring] at this
            linarith
          apply natAbs_le_of_abs (g + 1)
          have heq : (K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) =
              Sv - X := by rw [hK, hXg1]; ring
          rw [heq]
          calc |Sv - X| ≤ 2 * |Y| := hb2
            _ = ((2 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
            _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((2 : ℕ) * 2 ^ g) := mb_bound Mb hMb 2 g
            _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ (g + 1) := by rw [pow_succ]; push_cast; ring
      · exfalso
        omega
    obtain ⟨w, sh, hw, hwabs, hsh⟩ := hzex
    obtain ⟨hzf, hzv⟩ := sub_grid_top s a hsf ha w sh hw hwabs (habsN w sh hsh)
    set z := Wasm.IEEE64.sub s a
    -- `t = b - z` is the rounding error of `s`
    have hd : (2 : ℤ) ^ g ∣ X + Y - Sv := by
      rw [hsum, hK, pow_succ]
      exact ⟨N - K * 2, by ring⟩
    obtain ⟨htf, htv⟩ := sub_grid_top b z hb hzf ((X + Y - Sv) / 2 ^ g) g
      (by rw [Int.ediv_mul_cancel hd, hzv, ← hSv, ← hX, ← hY]; ring)
      (by
        apply natAbs_le_of_abs g
        rw [Int.ediv_mul_cancel hd, show X + Y - Sv = -(Sv - (X + Y)) by ring, abs_neg]
        calc |Sv - (X + Y)| ≤ |Y| := herr
          _ = ((1 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
          _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((1 : ℕ) * 2 ^ g) := mb_bound Mb hMb 1 g
          _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ g := by push_cast; ring)
      (habsN _ g (by
        rw [Int.ediv_mul_cancel hd, show X + Y - Sv = -(Sv - (X + Y)) by ring, abs_neg]
        have := abs_nonneg Y
        linarith [herr]))
    have hvt : value (Wasm.IEEE64.sub b z) = (((X + Y - Sv) : ℤ) : ℝ) / 2 ^ 1074 := by
      rw [value, htv, hzv, ← hSv, ← hX, ← hY]
      congr 1
      push_cast
      ring
    refine ⟨hsf, htf, ?_, hsr, ?_⟩
    · rw [hvt, hva, hvb, value, ← hSv]
      push_cast
      ring
    · rw [hvt, hvb, abs_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      rw [show X + Y - Sv = -(Sv - (X + Y)) by ring, Int.cast_neg, abs_neg, ← Int.cast_abs,
        ← Int.cast_abs]
      exact_mod_cast herr

#print axioms signed_grid_packing_top
#print axioms add_rounded_top
#print axioms rounded_dvd_top
#print axioms fast_two_sum_top
#print axioms fast_two_sum_small

end LeanExe.ProofKit.F64TopTwoSum
