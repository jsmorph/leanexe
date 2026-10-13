import Verified.Examples.TgammaAccShift
import LeanExe.ProofKit.F64Admissibility
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64NearestScale
import Mathlib.Data.UInt

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

/-- `x (x + 1) ⋯ (x + m)` divided by `2 ^ (500 r)`. -/
noncomputable def W (v : ℝ) (r m : ℕ) : ℝ := (∏ i ∈ Finset.range (m + 1), (v + i)) / 2 ^ (500 * r)

/-- The product of `min 1 |x + i|` for `i ≤ m`. -/
noncomputable def S (v : ℝ) (m : ℕ) : ℝ := ∏ i ∈ Finset.range (m + 1), g v i

theorem eoff_step (e0 : UInt64) (r : ℕ) :
    e0 - 500 * UInt64.ofNat r - 500 = e0 - 500 * UInt64.ofNat (r + 1) := by
  rw [UInt64.ofNat_add, mul_add]
  simp [sub_sub]

/-- The state `(xph, xpl, wh, wl, eoff)` of the loop after `m` steps: the factor `x + m` exact on
the grid `2 ^ -54`, and `wh + wl` within `m 2 ^ -95` of `W v r m` relative after `r` divisions
by `2 ^ 500`. -/
def UpInv (v : ℝ) (e0 : UInt64) (m : ℕ) (s : Float × Float × Float × Float × UInt64) : Prop :=
  Finite s.1.toBits ∧ Finite s.2.1.toBits ∧ Finite s.2.2.1.toBits ∧ Finite s.2.2.2.1.toBits ∧
    value s.1.toBits + value s.2.1.toBits = v + m ∧
    (∃ z : ℤ, value s.1.toBits = z / 2 ^ 54) ∧ (∃ z : ℤ, value s.2.1.toBits = z / 2 ^ 54) ∧
    |value s.2.1.toBits| ≤ 1 / 2 ^ 43 ∧
    |value s.2.1.toBits| ≤ |value s.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 ∧
    ∃ r : ℕ, r ≤ m ∧ s.2.2.2.2 = e0 - 500 * UInt64.ofNat r ∧
      |value s.2.2.1.toBits + value s.2.2.2.1.toBits - W v r m| ≤ m / 2 ^ 95 * |W v r m| ∧
      |value s.2.2.2.1.toBits| ≤ |value s.2.2.1.toBits| / 2 ^ 50 ∧
      |value s.2.2.1.toBits| ≤ 2 ^ 518 ∧ S v m / 4 ≤ |W v r m|

/-- One step of the loop for `x < j`. -/
def upStep (s : Float × Float × Float × Float × UInt64) : Float × Float × Float × Float × UInt64 :=
  if (mulDD3 (fshift s.1 s.2.1).1 (fshift s.1 s.2.1).2 s.2.2.1 s.2.2.2.1).1.abs >
      Float.ofBits 0x6050000000000000 then
    ((fshift s.1 s.2.1).1, (fshift s.1 s.2.1).2,
      (mulDD3 (fshift s.1 s.2.1).1 (fshift s.1 s.2.1).2 s.2.2.1 s.2.2.2.1).1 *
        Float.ofBits 0x20B0000000000000,
      (mulDD3 (fshift s.1 s.2.1).1 (fshift s.1 s.2.1).2 s.2.2.1 s.2.2.2.1).2 *
        Float.ofBits 0x20B0000000000000, s.2.2.2.2 - 500)
  else
    ((fshift s.1 s.2.1).1, (fshift s.1 s.2.1).2,
      (mulDD3 (fshift s.1 s.2.1).1 (fshift s.1 s.2.1).2 s.2.2.1 s.2.2.2.1).1,
      (mulDD3 (fshift s.1 s.2.1).1 (fshift s.1 s.2.1).2 s.2.2.1 s.2.2.2.1).2, s.2.2.2.2)

theorem W_succ (v : ℝ) (r m : ℕ) : W v r (m + 1) = (v + (m + 1 : ℕ)) * W v r m := by
  rw [W, W, Finset.prod_range_succ]; ring

theorem W_rescale (v : ℝ) (r m : ℕ) : W v (r + 1) m = W v r m / 2 ^ 500 := by
  rw [W, W, show 500 * (r + 1) = 500 * r + 500 by ring, pow_add]; ring

theorem S_succ (v : ℝ) (m : ℕ) : S v (m + 1) = S v m * g v ((m + 1 : ℕ) : ℤ) := by
  rw [S, S, Finset.prod_range_succ]

theorem S_le_one (v : ℝ) (m : ℕ) : S v m ≤ 1 :=
  Finset.prod_le_one (fun _ _ => le_min zero_le_one (abs_nonneg _)) (fun _ _ => min_le_left _ _)

theorem S_nonneg (v : ℝ) (m : ℕ) : 0 ≤ S v m :=
  Finset.prod_nonneg (fun _ _ => le_min zero_le_one (abs_nonneg _))

/-- The bounds after a division by `2 ^ 500`, on the real numbers. -/
theorem resc_real (a b q2 Wn δ Sv : ℝ) (hδ0 : 0 ≤ δ)
    (hpe : |a + b - Wn| ≤ (δ + 1 / 2 ^ 96) * |Wn|) (hp1b : |a| ≤ 4 * |Wn|)
    (ht : 2 ^ 518 < |a|) (hq2e : |q2 - b / 2 ^ 500| ≤ |a| / 2 ^ 500 / 2 ^ 100)
    (hWs : |Wn| ≤ 2 ^ 528) (hS : Sv ≤ 1) :
    |a / 2 ^ 500 + q2 - Wn / 2 ^ 500| ≤ (δ + 1 / 2 ^ 95) * |Wn / 2 ^ 500| ∧
      |a / 2 ^ 500| ≤ 2 ^ 518 ∧ Sv / 4 ≤ |Wn / 2 ^ 500| := by
  have h500 : (0 : ℝ) < 2 ^ 500 := by positivity
  rw [abs_div, abs_of_pos h500, abs_div, abs_of_pos h500]
  refine ⟨?_, ?_, ?_⟩
  · have e1 : a / 2 ^ 500 + q2 - Wn / 2 ^ 500 = (a + b - Wn) / 2 ^ 500 + (q2 - b / 2 ^ 500) := by
      ring
    rw [e1]
    have h2 := abs_add_le ((a + b - Wn) / 2 ^ 500) (q2 - b / 2 ^ 500)
    rw [abs_div, abs_of_pos h500] at h2
    have h3 : |a| / 2 ^ 500 / 2 ^ 100 ≤ |Wn| / 2 ^ 500 / 2 ^ 98 := by
      have := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hp1b h500.le)
        (by positivity : (0 : ℝ) ≤ 2 ^ 100)
      have e2 : 4 * |Wn| / 2 ^ 500 / 2 ^ 100 = |Wn| / 2 ^ 500 / 2 ^ 98 := by ring
      linarith
    have h4 : |a + b - Wn| / 2 ^ 500 ≤ (δ + 1 / 2 ^ 96) * |Wn| / 2 ^ 500 :=
      div_le_div_of_nonneg_right hpe h500.le
    have e3 : (δ + 1 / 2 ^ 95) * (|Wn| / 2 ^ 500) = (δ + 1 / 2 ^ 96) * |Wn| / 2 ^ 500 +
        |Wn| / 2 ^ 500 / 2 ^ 96 := by ring
    have h5 : |Wn| / 2 ^ 500 / 2 ^ 98 ≤ |Wn| / 2 ^ 500 / 2 ^ 96 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
    linarith
  · rw [div_le_iff₀ h500]
    linarith [(by norm_num : (4 : ℝ) * 2 ^ 528 ≤ 2 ^ 518 * 2 ^ 500)]
  · rw [le_div_iff₀ h500]
    have h6 : Sv / 4 * 2 ^ 500 ≤ 1 / 4 * 2 ^ 500 :=
      mul_le_mul_of_nonneg_right (by linarith) h500.le
    linarith [(by norm_num : (1 : ℝ) / 4 * 2 ^ 500 ≤ 2 ^ 518 / 4)]

/-- **One step of the loop for `x < j`** keeps the invariant. -/
theorem up_step (hF : FmaSpec.FmaNearest) (v : ℝ) (e0 : UInt64) (m : ℕ)
    (s : Float × Float × Float × Float × UInt64) (hm : m + 1 ≤ 187)
    (hv : ∀ n : ℤ, 1 / 2 ^ 54 ≤ |v + n|) (hX : |v + m + 1| ≤ 2 ^ 8) (hX0 : |v + m| ≤ 2 ^ 8)
    (h : UpInv v e0 m s) : UpInv v e0 (m + 1) (upStep s) := by
  obtain ⟨xph, xpl, wh, wl, e⟩ := s
  obtain ⟨hphf, hplf, hwhf, hwlf, hsum, ⟨zh, hzh⟩, ⟨zl, hzl⟩, hpl43, hplr, r, hr, he, hWe, hwlb,
    hwhb, hS⟩ := h
  dsimp only at hphf hplf hwhf hwlf hsum hzh hzl hpl43 hplr he hWe hwlb hwhb
  have hm' : (m : ℝ) + 1 ≤ 187 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the factor
  obtain ⟨hf1f, hf2f, hfsum, hfg1, hfg2, hf243, hf2r⟩ := fshift_spec xph xpl hphf hplf zh zl hzh
    hzl hpl43 (by rw [hsum]; exact hX) (by rw [hsum]; exact hX0)
  set f := fshift xph xpl with hfdef
  set X := v + ((m + 1 : ℕ) : ℝ) with hXdef
  have hXv : value f.1.toBits + value f.2.toBits = X := by rw [hfsum, hsum, hXdef]; push_cast; ring
  have hX54 : 1 / 2 ^ 54 ≤ |X| := by
    have := hv ((m + 1 : ℕ) : ℤ)
    rw [hXdef]; push_cast at this ⊢; exact this
  have hX8 : |X| ≤ 2 ^ 8 := by rw [hXdef]; push_cast; rw [← add_assoc]; exact hX
  have hf1lo : 1 / 2 ^ 56 ≤ |value f.1.toBits| := by
    have := abs_add_le (value f.1.toBits) (value f.2.toBits)
    rw [hXv] at this
    nlinarith [abs_nonneg (value f.1.toBits)]
  have hf2b : |value f.2.toBits| ≤ |value f.1.toBits| / 2 ^ 50 := by
    have : (1 : ℝ) / 2 ^ 1074 ≤ |value f.1.toBits| / 2 ^ 52 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 * 2 ^ 52 ≤ 1 / 2 ^ 56)]
    have e : |value f.1.toBits| / 2 ^ 52 + |value f.1.toBits| / 2 ^ 52 ≤
        |value f.1.toBits| / 2 ^ 50 := by
      have e2 : |value f.1.toBits| / 2 ^ 52 + |value f.1.toBits| / 2 ^ 52 =
          |value f.1.toBits| * (2 / 2 ^ 52) := by ring
      have e3 : |value f.1.toBits| / 2 ^ 50 = |value f.1.toBits| * (1 / 2 ^ 50) := by ring
      rw [e2, e3]; exact mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    linarith
  -- the product
  have hSlo := prod_small v hv m
  have hWlo : 1 / 2 ^ 57 ≤ |W v r m| := by
    have : S v m = ∏ i ∈ Finset.range (m + 1), g v i := rfl
    rw [← this] at hSlo
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 55 / 4 = 1 / 2 ^ 57)]
  have hδ : (m : ℝ) / 2 ^ 95 ≤ 1 / 2 ^ 80 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨hp1f, hp2f, hpe, hp2b, hp1b, hp1b'⟩ := prod_step hF f.1 f.2 wh wl X (W v r m)
    (m / 2 ^ 95) hf1f hf2f hwhf hwlf hXv hf2b hX54 hX8 hWe (by positivity) hδ hwlb hwhb hWlo
  have hWs : X * W v r m = W v r (m + 1) := by rw [W_succ]
  rw [hWs] at hpe hp1b hp1b'
  set p := mulDD3 f.1 f.2 wh wl with hpdef
  -- the size of `W` before the step
  have hWhi : |W v r m| ≤ 2 ^ 520 := by
    have h1 := abs_sub_abs_le_abs_sub (W v r m) (value wh.toBits + value wl.toBits)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le (value wh.toBits) (value wl.toBits)
    have : (m : ℝ) / 2 ^ 95 * |W v r m| ≤ |W v r m| / 2 := by
      have := mul_le_mul_of_nonneg_right hδ (abs_nonneg (W v r m))
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 80 ≤ 1 / 2), abs_nonneg (W v r m)]
    have : |value wh.toBits| / 2 ^ 50 ≤ 2 ^ 518 := by
      have := div_le_self (abs_nonneg (value wh.toBits)) (by norm_num : (1 : ℝ) ≤ 2 ^ 50)
      linarith
    linarith [(by norm_num : (2 : ℝ) ^ 518 + 2 ^ 518 + 2 ^ 519 ≤ 2 ^ 520)]
  have hWs' : |W v r (m + 1)| ≤ 2 ^ 528 := by
    rw [← hWs, abs_mul]
    have := mul_le_mul hX8 hWhi (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 8 * 2 ^ 520 = 2 ^ 528)]
  -- the test against `2 ^ 518`
  have hcw : Wasm.IEEE64.isFinite 0x6050000000000000 = true := by decide
  have hcv : value (Float.ofBits 0x6050000000000000).toBits = 2 ^ 518 := by
    rw [TgammaWords.ofBits_value _ hcw, show PolyBound.ratOfWord 0x6050000000000000 = 2 ^ 518
      by decide +kernel]
    norm_num
  obtain ⟨hpaf, hpav⟩ := TgammaFloor.abs_float p.1 hp1f
  have htest : p.1.abs > Float.ofBits 0x6050000000000000 ↔ 2 ^ 518 < |value p.1.toBits| := by
    rw [GT.gt, F64UpperWord.float_lt_iff _ _ (TgammaWords.ofBits_finite _ hcw) hpaf, hcv, hpav]
  have hstep : upStep (xph, xpl, wh, wl, e) =
      if p.1.abs > Float.ofBits 0x6050000000000000 then
        (f.1, f.2, p.1 * Float.ofBits 0x20B0000000000000, p.2 * Float.ofBits 0x20B0000000000000,
          e - 500)
      else (f.1, f.2, p.1, p.2, e) := rfl
  rw [hstep]
  have hS1 : S v (m + 1) / 4 ≤ |W v r (m + 1)| := by
    rw [S_succ, ← hWs, abs_mul]
    have hg : g v ((m + 1 : ℕ) : ℤ) ≤ |X| := by
      rw [g, hXdef]; push_cast; exact min_le_right _ _
    have hg0 : 0 ≤ g v ((m + 1 : ℕ) : ℤ) := le_min zero_le_one (abs_nonneg _)
    have h7 : S v m / 4 * g v ((m + 1 : ℕ) : ℤ) ≤ |W v r m| * |X| :=
      mul_le_mul hS hg hg0 (abs_nonneg _)
    have e5 : S v m * g v ((m + 1 : ℕ) : ℤ) / 4 = S v m / 4 * g v ((m + 1 : ℕ) : ℤ) := by ring
    rw [e5, mul_comm |X|]
    exact h7
  by_cases ht : p.1.abs > Float.ofBits 0x6050000000000000
  · rw [ite_eq_left ht]
    have ht' := htest.mp ht
    obtain ⟨hq1f, hq2f, hq1v, hq2e, hq2b⟩ := rescale p.1 p.2 hp1f hp2f ht' hp2b
    unfold UpInv
    dsimp only
    obtain ⟨hr1, hr2, hr3⟩ := resc_real _ _ _ _ _ _ (by positivity) hpe hp1b ht' hq2e hWs'
      (S_le_one v (m + 1))
    refine ⟨hf1f, hf2f, hq1f, hq2f, by rw [hXv, hXdef], hfg1, hfg2, hf243, hf2r, r + 1,
      by omega, by rw [he, eoff_step], ?_, hq2b, by rw [hq1v]; exact hr2,
      by rw [W_rescale]; exact hr3⟩
    rw [W_rescale, hq1v]
    refine hr1.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    push_cast
    have e4 : ((m : ℝ) + 1) / 2 ^ 95 = m / 2 ^ 95 + 1 / 2 ^ 95 := by ring
    linarith
  · rw [ite_eq_right ht]
    have ht' : |value p.1.toBits| ≤ 2 ^ 518 := by
      by_contra hc
      exact ht (htest.mpr (lt_of_not_ge hc))
    unfold UpInv
    dsimp only
    refine ⟨hf1f, hf2f, hp1f, hp2f, by rw [hXv, hXdef], hfg1, hfg2, hf243, hf2r, r,
      by omega, he, ?_, ?_, ht', hS1⟩
    · refine hpe.trans ?_
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      push_cast
      have : (1 : ℝ) / 2 ^ 96 ≤ 1 / 2 ^ 95 := by norm_num
      have e4 : ((m : ℝ) + 1) / 2 ^ 95 = m / 2 ^ 95 + 1 / 2 ^ 95 := by ring
      linarith
    · have := div_le_div_of_nonneg_left (abs_nonneg (value p.1.toBits))
        (by positivity : (0 : ℝ) < 2 ^ 50) (by norm_num : (2 : ℝ) ^ 50 ≤ 2 ^ 51)
      linarith

/-- The state before the loop: the factor and the product are `x`. -/
theorem up_init (x : Float) (e0 : UInt64) (hx : Finite x.toBits) (z : ℤ)
    (hz : value x.toBits = z / 2 ^ 54) (hq : 1 / 4 ≤ |value x.toBits|)
    (h518 : |value x.toBits| ≤ 2 ^ 518) :
    UpInv (value x.toBits) e0 0 (x, (0.0 : Float), x, (0.0 : Float), e0) := by
  unfold UpInv
  dsimp only
  rw [TgammaMainRed.zero_value]
  refine ⟨hx, TgammaMainRed.zero_finite, hx, TgammaMainRed.zero_finite, by simp, ⟨z, hz⟩,
    ⟨0, by simp⟩, by norm_num, by simp; positivity, 0, le_rfl, by simp, ?_, by simp; positivity,
    h518, ?_⟩
  · simp [W]
  · have hW0 : W (value x.toBits) 0 0 = value x.toBits := by simp [W]
    have hS0 : S (value x.toBits) 0 = g (value x.toBits) 0 := by simp [S]
    rw [hW0, hS0]
    have : g (value x.toBits) 0 ≤ |value x.toBits| := by rw [g]; simp
    have h0 : 0 ≤ g (value x.toBits) 0 := le_min zero_le_one (abs_nonneg _)
    linarith

/-- **The loop for `x < j`** after `m` steps. -/
theorem up_loop (hF : FmaSpec.FmaNearest) (x : Float) (e0 : UInt64) (M : ℕ) (hM : M ≤ 186)
    (hx : Finite x.toBits) (z : ℤ) (hz : value x.toBits = z / 2 ^ 54)
    (hq : 1 / 4 ≤ |value x.toBits|) (hlo : -2 ^ 8 ≤ value x.toBits)
    (hhi : value x.toBits + M ≤ 2 ^ 8)
    (hv : ∀ n : ℤ, 1 / 2 ^ 54 ≤ |value x.toBits + n|) :
    ∀ m, m ≤ M → UpInv (value x.toBits) e0 m
      (LeanExe.loop (UInt64.ofNat m) (x, (0.0 : Float), x, (0.0 : Float), e0)
        (fun _ s => upStep s)) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : LeanExe.loop (UInt64.ofNat 0) (x, (0.0 : Float), x, (0.0 : Float), e0)
        (fun _ s => upStep s) = (x, (0.0 : Float), x, (0.0 : Float), e0) := by
      simp [LeanExe.loop]
    rw [h0]
    exact up_init x e0 hx z hz hq (by
      rw [abs_le]; constructor <;> linarith [(by norm_num : (2 : ℝ) ^ 8 ≤ 2 ^ 518)])
  | succ m ih =>
    intro hm
    have hst := ih (by omega)
    rw [TgammaPoly.loop_succ m (by omega)]
    have hm' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact up_step hF (value x.toBits) e0 m _ (by omega) hv
      (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith) hst

#print axioms prod_small
#print axioms scale_down
#print axioms prod_step
#print axioms rescale
#print axioms resc_real
#print axioms up_step
#print axioms up_init
#print axioms up_loop

end Verified.Examples.TgammaAccUp
