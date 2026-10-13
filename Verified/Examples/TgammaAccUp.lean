import Verified.Examples.TgammaAccShift
import LeanExe.ProofKit.F64Admissibility
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64NearestScale

/-!
The loop of `Tgamma.accurate` for `x < j`, which multiplies the factors `x, x + 1, …` and divides
the product by `2 ^ 500` whenever its high part exceeds `2 ^ 518`.  `prod_small` bounds the product
of the factors below 1 in magnitude: of the factors `x + i`, only the two next to the integer part
of `-x` lie below 1, and their product is at least `2 ^ -55` when `x` lies at least `2 ^ -54` from
every integer.  `scale_down` shows that the division of the high part by `2 ^ 500` is exact.
-/

namespace Verified.Examples.TgammaAccUp
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccShift

set_option exponentiation.threshold 4096

/-- The factor `min 1 |v + n|`. -/
noncomputable def g (v : ℝ) (n : ℤ) : ℝ := min 1 |v + n|

/-- **The factors below 1.**  For `v` at least `2 ^ -54` from every integer, the product of
`min 1 |v + i|` over `i ≤ m` is at least `2 ^ -55`. -/
theorem prod_small (v : ℝ) (hv : ∀ n : ℤ, 1 / 2 ^ 54 ≤ |v + n|) (m : ℕ) :
    1 / 2 ^ 55 ≤ ∏ i ∈ Finset.range (m + 1), g v i := by
  set a : ℤ := ⌊-v⌋ with ha
  have hfl := Int.floor_le (-v)
  have hlt := Int.lt_floor_add_one (-v)
  rw [← ha] at hfl hlt
  have hg1 : ∀ n : ℤ, g v n ≤ 1 := fun n => min_le_left _ _
  have hg0 : ∀ n : ℤ, 0 ≤ g v n := fun n => le_min zero_le_one (abs_nonneg _)
  have hone : ∀ n : ℤ, n ≠ a → n ≠ a + 1 → g v n = 1 := by
    intro n h1 h2
    apply min_eq_left
    rcases lt_or_gt_of_ne h1 with h | h
    · have : (n : ℝ) ≤ a - 1 := by exact_mod_cast (show n ≤ a - 1 by omega)
      rw [abs_of_neg (by linarith)]; linarith
    · have : (a : ℝ) + 2 ≤ n := by exact_mod_cast (show a + 2 ≤ n by omega)
      rw [abs_of_pos (by linarith)]; linarith
  -- the product after `m` factors
  have key : ∀ m : ℕ, (if a ≤ m then g v a else 1) * (if a + 1 ≤ m then g v (a + 1) else 1) ≤
      ∏ i ∈ Finset.range (m + 1), g v i := by
    intro m
    induction m with
    | zero =>
      simp only [zero_add, Finset.prod_range_one, Nat.cast_zero]
      by_cases ha0 : a = 0
      · rw [if_pos (by omega), if_neg (by omega), mul_one, ha0]
      · by_cases ha1 : a = -1
        · rw [if_pos (by omega), if_pos (by omega)]
          have : g v (a + 1) = g v 0 := by rw [ha1]; norm_num
          rw [this]
          nlinarith [hg1 a, hg0 a, hg0 0]
        · have h0 : g v 0 = 1 := hone 0 (by omega) (by omega)
          rw [h0]
          split_ifs <;> nlinarith [hg1 a, hg1 (a + 1), hg0 a, hg0 (a + 1)]
    | succ m ih =>
      rw [Finset.prod_range_succ]
      have hP0 : 0 ≤ ∏ i ∈ Finset.range (m + 1), g v i :=
        Finset.prod_nonneg (fun i _ => hg0 i)
      have hcast : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      by_cases h0 : (m : ℤ) + 1 = a
      · rw [if_neg (by omega), if_neg (by omega), one_mul] at ih
        rw [if_pos (by omega), if_neg (by omega), mul_one, ← h0]
        nlinarith [hg0 ((m : ℤ) + 1)]
      · by_cases h1 : (m : ℤ) + 1 = a + 1
        · rw [if_pos (by omega), if_neg (by omega), mul_one] at ih
          rw [if_pos (by omega), if_pos (by omega), h1]
          exact mul_le_mul_of_nonneg_right ih (hg0 _)
        · rw [hone _ h0 h1, mul_one]
          have e1 : (a ≤ (m : ℤ) + 1) ↔ (a ≤ (m : ℤ)) := by omega
          have e2 : (a + 1 ≤ (m : ℤ) + 1) ↔ (a + 1 ≤ (m : ℤ)) := by omega
          simp only [e1, e2]
          exact ih
  -- the two special factors
  have ht0 : 0 < v + a + 1 := by linarith
  have ht1 : v + a + 1 ≤ 1 := by linarith
  have hga : g v a = -(v + a) := by
    have h := hv a
    have hn : v + a ≤ 0 := by linarith
    rw [g, abs_of_nonpos hn]
    exact min_eq_right (by linarith)
  have hgb : g v (a + 1) = v + a + 1 := by
    rw [g]; push_cast
    rw [abs_of_pos (by linarith), min_eq_right (by linarith)]
    ring
  have hA := hv a
  have hB := hv (a + 1)
  push_cast at hB
  rw [abs_of_pos (by linarith)] at hB
  rw [abs_of_nonpos (by linarith)] at hA
  have hprod : 1 / 2 ^ 55 ≤ g v a * g v (a + 1) := by
    rw [hga, hgb]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ v + a + 1 - 1 / 2 ^ 54)
      (by linarith : (0 : ℝ) ≤ -(v + a) - 1 / 2 ^ 54)]
  refine le_trans hprod (le_trans ?_ (key m))
  split_ifs <;> nlinarith [hg1 a, hg1 (a + 1), hg0 a, hg0 (a + 1)]

/-- **Division of the high part by `2 ^ 500`** is exact above `2 ^ 518`. -/
theorem scale_down (w : Float) (hw : Finite w.toBits) (hlo : 2 ^ 518 < |value w.toBits|) :
    Finite (w * Float.ofBits 0x20B0000000000000).toBits ∧
      value (w * Float.ofBits 0x20B0000000000000).toBits = value w.toBits / 2 ^ 500 := by
  have hcw : Wasm.IEEE64.isFinite 0x20B0000000000000 = true := by decide
  have hc : (Float.ofBits 0x20B0000000000000).toBits = Wasm.IEEE64.encodeFinite false 523 0 := by
    rw [TgammaWords.ofBits_bits _ hcw]; decide
  have hcf := TgammaWords.ofBits_finite _ hcw
  have he : 1541 ≤ Wasm.IEEE64.exponent w.toBits := by
    by_contra hn
    have := F64Magnitude.magnitude_lt w.toBits 1541 518 (by norm_num) (by norm_num) (by omega)
    rw [show ((2 : ℝ) ^ (518 : ℤ)) = 2 ^ 518 by norm_num] at this
    linarith
  have hb := F64Admissibility.finite_exponent_bound w.toBits hw
  rw [F64Bits.toBits_mul, F64NearestScale.mul_comm_finite _ _ hw hcf, hc]
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite 523 w.toBits (by norm_num) (by norm_num) hw
    (by omega) (by omega) (by omega)
  refine ⟨hf, ?_⟩
  rw [hv]
  norm_num
  ring

/-- **One product of the loop.**  The factor `f1 + f2 = X` times the product `wh + wl ≈ W`. -/
theorem prod_step (hF : FmaSpec.FmaNearest) (f1 f2 wh wl : Float) (X W δ : ℝ)
    (hf1 : Finite f1.toBits) (hf2 : Finite f2.toBits) (hwh : Finite wh.toBits)
    (hwl : Finite wl.toBits) (hX : value f1.toBits + value f2.toBits = X)
    (hf2b : |value f2.toBits| ≤ |value f1.toBits| / 2 ^ 50) (hX54 : 1 / 2 ^ 54 ≤ |X|)
    (hX8 : |X| ≤ 2 ^ 8) (hW : |value wh.toBits + value wl.toBits - W| ≤ δ * |W|)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2 ^ 80) (hwlb : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 50)
    (hwhb : |value wh.toBits| ≤ 2 ^ 518) (hWlo : 1 / 2 ^ 57 ≤ |W|) :
    Finite (mulDD3 f1 f2 wh wl).1.toBits ∧ Finite (mulDD3 f1 f2 wh wl).2.toBits ∧
      |value (mulDD3 f1 f2 wh wl).1.toBits + value (mulDD3 f1 f2 wh wl).2.toBits - X * W| ≤
        (δ + 1 / 2 ^ 96) * |X * W| ∧
      |value (mulDD3 f1 f2 wh wl).2.toBits| ≤ |value (mulDD3 f1 f2 wh wl).1.toBits| / 2 ^ 51 ∧
      |value (mulDD3 f1 f2 wh wl).1.toBits| ≤ 4 * |X * W| ∧
      |X * W| / 4 ≤ |value (mulDD3 f1 f2 wh wl).1.toBits| := by
  set a := value f1.toBits
  set b := value f2.toBits
  set c := value wh.toBits
  set e := value wl.toBits
  have hXp : 0 < |X| := lt_of_lt_of_le (by positivity) hX54
  have hWp : 0 < |W| := lt_of_lt_of_le (by positivity) hWlo
  -- `|a|` and `|c|` within `2 ^ -49` of `|X|` and `|W|`
  have ha1 : |a| ≤ |X| * (1 + 1 / 2 ^ 49) := by
    have h1 := abs_add_le (a + b) (-b)
    rw [show a + b + -b = a by ring, abs_neg, hX] at h1
    have : |a| * (1 - 1 / 2 ^ 50) ≤ |X| := by nlinarith
    nlinarith [abs_nonneg a]
  have ha2 : |X| * (1 - 1 / 2 ^ 49) ≤ |a| := by
    have h1 := abs_add_le a b
    rw [hX] at h1
    nlinarith [abs_nonneg a]
  have hce : |c + e| ≤ |W| * (1 + δ) := by
    have := abs_sub_abs_le_abs_sub (c + e) W
    nlinarith
  have hce' : |W| * (1 - δ) ≤ |c + e| := by
    have := abs_sub_abs_le_abs_sub W (c + e)
    rw [abs_sub_comm] at this
    nlinarith
  have hc1 : |c| ≤ |W| * (1 + 1 / 2 ^ 49) := by
    have h1 := abs_add_le (c + e) (-e)
    rw [show c + e + -e = c by ring, abs_neg] at h1
    have : |c| * (1 - 1 / 2 ^ 50) ≤ |W| * (1 + δ) := by nlinarith
    nlinarith [abs_nonneg c]
  have hc2 : |W| * (1 - 1 / 2 ^ 49) ≤ |c| := by
    have h1 := abs_add_le c e
    nlinarith [abs_nonneg c]
  have hP1 : |a| * |c| ≤ 2 * (|X| * |W|) := by
    have := mul_le_mul ha1 hc1 (abs_nonneg _) (by positivity)
    nlinarith [mul_pos hXp hWp]
  have hP2 : |X| * |W| / 2 ≤ |a| * |c| := by
    have := mul_le_mul ha2 hc2 (by positivity) (abs_nonneg _)
    nlinarith [mul_pos hXp hWp]
  obtain ⟨hp1f, hp2f, hpe, hp2b, hp1b, hp1b'⟩ := TgammaMulDD3.mulDD3_spec hF f1 f2 wh wl hf1 hf2 hwh
    hwl hf2b hwlb (by
      have : 1 / 2 ^ 54 * (1 / 2 ^ 57) ≤ |X| * |W| := mul_le_mul hX54 hWlo (by positivity)
        (abs_nonneg _)
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 54 * (1 / 2 ^ 57) / 2)])
    (by
      have : |a| * |c| ≤ |X| * (1 + 1 / 2 ^ 49) * 2 ^ 518 :=
        mul_le_mul ha1 hwhb (abs_nonneg _) (by positivity)
      have : |X| * (1 + 1 / 2 ^ 49) * 2 ^ 518 ≤ 2 ^ 8 * (1 + 1 / 2 ^ 49) * 2 ^ 518 := by gcongr
      linarith [(by norm_num : (2 : ℝ) ^ 8 * (1 + 1 / 2 ^ 49) * 2 ^ 518 ≤ 2 ^ 899)])
  rw [abs_mul]
  refine ⟨hp1f, hp2f, ?_, hp2b, by linarith, by linarith⟩
  have e1 : value (mulDD3 f1 f2 wh wl).1.toBits + value (mulDD3 f1 f2 wh wl).2.toBits - X * W =
      (value (mulDD3 f1 f2 wh wl).1.toBits + value (mulDD3 f1 f2 wh wl).2.toBits -
        (a + b) * (c + e)) + X * (c + e - W) := by rw [hX]; ring
  rw [e1]
  have h2 := abs_add_le (value (mulDD3 f1 f2 wh wl).1.toBits +
    value (mulDD3 f1 f2 wh wl).2.toBits - (a + b) * (c + e)) (X * (c + e - W))
  have h3 : |X * (c + e - W)| ≤ |X| * (δ * |W|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hW (abs_nonneg _)
  have h4 : |a| * |c| / 2 ^ 98 ≤ 2 * (|X| * |W|) / 2 ^ 98 :=
    div_le_div_of_nonneg_right hP1 (by norm_num)
  have e2 : (δ + 1 / 2 ^ 96) * (|X| * |W|) = |X| * (δ * |W|) + (|X| * |W|) / 2 ^ 96 := by ring
  have h5 : 2 * (|X| * |W|) / 2 ^ 98 ≤ (|X| * |W|) / 2 ^ 96 := by
    have : 0 ≤ |X| * |W| := by positivity
    linarith [(by ring : 2 * (|X| * |W|) / 2 ^ 98 = (|X| * |W|) / 2 ^ 97),
      div_le_div_of_nonneg_left this (by norm_num : (0 : ℝ) < 2 ^ 96)
        (by norm_num : (2 : ℝ) ^ 96 ≤ 2 ^ 97)]
  linarith

/-- **The division of the product by `2 ^ 500`.** -/
theorem rescale (p1 p2 : Float) (hp1f : Finite p1.toBits) (hp2f : Finite p2.toBits)
    (hp1 : 2 ^ 518 < |value p1.toBits|) (hp2 : |value p2.toBits| ≤ |value p1.toBits| / 2 ^ 51) :
    Finite (p1 * Float.ofBits 0x20B0000000000000).toBits ∧
      Finite (p2 * Float.ofBits 0x20B0000000000000).toBits ∧
      value (p1 * Float.ofBits 0x20B0000000000000).toBits = value p1.toBits / 2 ^ 500 ∧
      |value (p2 * Float.ofBits 0x20B0000000000000).toBits - value p2.toBits / 2 ^ 500| ≤
        |value p1.toBits| / 2 ^ 500 / 2 ^ 100 ∧
      |value (p2 * Float.ofBits 0x20B0000000000000).toBits| ≤
        |value (p1 * Float.ofBits 0x20B0000000000000).toBits| / 2 ^ 50 := by
  obtain ⟨hsf, hsv⟩ := scale_down p1 hp1f hp1
  have hcw : Wasm.IEEE64.isFinite 0x20B0000000000000 = true := by decide
  have hcv : value (Float.ofBits 0x20B0000000000000).toBits = 1 / 2 ^ 500 := by
    rw [TgammaWords.ofBits_value _ hcw, show PolyBound.ratOfWord 0x20B0000000000000 = 1 / 2 ^ 500
      by decide +kernel]
    norm_num
  have hc := fapprox_self _ (TgammaWords.ofBits_finite _ hcw)
  rw [hcv] at hc
  have hp1max : |value p1.toBits| ≤ 2 ^ 1024 := by
    have := F64Admissibility.finite_exponent_bound p1.toBits hp1f
    have := F64Magnitude.magnitude_lt p1.toBits 2047 1024 (by norm_num) (by norm_num) (by omega)
    rw [show ((2 : ℝ) ^ (1024 : ℤ)) = 2 ^ 1024 by norm_num] at this
    linarith
  have hm := fapprox_mul (fapprox_self p2 hp2f) hc |value p2.toBits| (1 / 2 ^ 500) le_rfl
    (by rw [abs_of_pos (by positivity)]) ((|value p2.toBits| + 0) * (1 / 2 ^ 500 + 0)) le_rfl
    (by
      have : |value p2.toBits| ≤ 2 ^ 1024 := by
        have : |value p1.toBits| / 2 ^ 51 ≤ |value p1.toBits| := div_le_self (abs_nonneg _)
          (by norm_num)
        linarith
      have : (|value p2.toBits| + 0) * (1 / 2 ^ 500 + 0) ≤ 2 ^ 1024 * (1 / 2 ^ 500) := by
        simp only [add_zero]; exact mul_le_mul_of_nonneg_right this (by positivity)
      linarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 / 2 ^ 500) < 2 ^ 1022)])
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hm
  have h2 := hm.2
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ |value p1.toBits| / 2 ^ 500 / 2 ^ 101 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 * (2 ^ 500 * 2 ^ 101) ≤ 2 ^ 518)]
  have hb : |value p2.toBits| * (1 / 2 ^ 500) / 2 ^ 53 ≤ |value p1.toBits| / 2 ^ 500 / 2 ^ 101 := by
    have : |value p2.toBits| * (1 / 2 ^ 500) / 2 ^ 53 ≤ |value p1.toBits| / 2 ^ 51 * (1 / 2 ^ 500) /
        2 ^ 53 := by gcongr
    have e : |value p1.toBits| / 2 ^ 51 * (1 / 2 ^ 500) / 2 ^ 53 =
        |value p1.toBits| / 2 ^ 500 / 2 ^ 104 := by ring
    have : |value p1.toBits| / 2 ^ 500 / 2 ^ 104 ≤ |value p1.toBits| / 2 ^ 500 / 2 ^ 101 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
    linarith
  have herr : |value (p2 * Float.ofBits 0x20B0000000000000).toBits - value p2.toBits / 2 ^ 500| ≤
      |value p1.toBits| / 2 ^ 500 / 2 ^ 100 := by
    rw [show value p2.toBits / 2 ^ 500 = value p2.toBits * (1 / 2 ^ 500) by ring]
    have e : |value p1.toBits| / 2 ^ 500 / 2 ^ 101 + |value p1.toBits| / 2 ^ 500 / 2 ^ 101 =
        |value p1.toBits| / 2 ^ 500 / 2 ^ 100 := by ring
    linarith
  refine ⟨hsf, hm.1, hsv, herr, ?_⟩
  rw [hsv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 500)]
  have := abs_sub_abs_le_abs_sub (value (p2 * Float.ofBits 0x20B0000000000000).toBits)
    (value p2.toBits / 2 ^ 500)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 500)] at this
  have h3 : |value p2.toBits| / 2 ^ 500 ≤ |value p1.toBits| / 2 ^ 51 / 2 ^ 500 :=
    div_le_div_of_nonneg_right hp2 (by positivity)
  have e : |value p1.toBits| / 2 ^ 51 / 2 ^ 500 + |value p1.toBits| / 2 ^ 500 / 2 ^ 100 ≤
      |value p1.toBits| / 2 ^ 500 / 2 ^ 50 := by
    have e2 : |value p1.toBits| / 2 ^ 51 / 2 ^ 500 + |value p1.toBits| / 2 ^ 500 / 2 ^ 100 =
        (|value p1.toBits| / 2 ^ 500) * (1 / 2 ^ 51 + 1 / 2 ^ 100) := by ring
    have e3 : |value p1.toBits| / 2 ^ 500 / 2 ^ 50 =
        (|value p1.toBits| / 2 ^ 500) * (1 / 2 ^ 50) := by ring
    rw [e2, e3]
    exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  linarith

#print axioms prod_small
#print axioms scale_down
#print axioms prod_step
#print axioms rescale

end Verified.Examples.TgammaAccUp
