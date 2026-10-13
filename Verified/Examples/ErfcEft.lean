import Verified.Examples.TrigNearest
import Verified.Examples.FmaSpec
import LeanExe.ProofKit.F64Sterbenz
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64RelativeStep
import LeanExe.ProofKit.F64NearestSum

/-!
Error-free transformations of binary64 arithmetic for the proof of `Erfc.erfc`.  `fast_two_sum`
proves Dekker's `Fast2Sum`: for `|b| ≤ |a|`, `s = a + b` rounded, `z = s - a`, and `t = b - z` are
computed exactly except for the rounding of `s`, so that `s + t = a + b`.  `two_sum` proves Knuth's
`TwoSum` for any finite operands from `Fast2Sum` and Sterbenz's lemma, and `two_prod` proves that
`fma (a, b, -a b)` gives the error of a product, under `FmaSpec.FmaNearest`.  The proofs work on the
grid of each word: its scaled value is a multiple of `2 ^ (e - 1)` for its exponent field `e`, so a
real number on a grid `2 ^ k` with at most 53 bits is held by a word, and a nearest word to such a
number holds it.
-/

namespace Verified.Examples.ErfcEft

open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 2200

/-- A real number that some finite word holds. -/
def Rep (r : ℝ) : Prop := ∃ w : UInt64, Finite w ∧ value w = r

theorem rep_word (w : UInt64) (h : Finite w) : Rep (value w) := ⟨w, h, rfl⟩

theorem rep_neg {r : ℝ} (h : Rep r) : Rep (-r) := by
  obtain ⟨w, hw, hv⟩ := h
  obtain ⟨hf, hn⟩ := F64Magnitude.negate_value w hw
  exact ⟨_, hf, by rw [hn, hv]⟩

/-- A number on the grid `2 ^ k` with at most 53 bits is held by a word. -/
theorem rep_grid (z : ℤ) (k : ℕ) (hz : |z| ≤ 2 ^ 53) (hk : k ≤ 2043) :
    Rep ((z : ℝ) * 2 ^ k / 2 ^ 1074) := by
  have hz' : z.natAbs ≤ 2 ^ 53 := by
    have : ((z.natAbs : ℕ) : ℤ) ≤ 2 ^ 53 := by rw [Int.natCast_natAbs]; exact hz
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact z k hz' hk
  exact ⟨_, hf, by rw [value, hv]; push_cast; ring⟩

/-- `r` is a multiple of `2 ^ k` scaled units. -/
def OnGrid (r : ℝ) (k : ℕ) : Prop := ∃ n : ℤ, r = (n : ℝ) * 2 ^ k / 2 ^ 1074

theorem onGrid_mono {r : ℝ} {k j : ℕ} (h : OnGrid r k) (hjk : j ≤ k) : OnGrid r j := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n * 2 ^ (k - j), ?_⟩
  rw [hn]
  push_cast
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hjk]

theorem onGrid_add {r q : ℝ} {k : ℕ} (hr : OnGrid r k) (hq : OnGrid q k) : OnGrid (r + q) k := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hq
  exact ⟨n + m, by rw [hn, hm]; push_cast; ring⟩

theorem onGrid_sub {r q : ℝ} {k : ℕ} (hr : OnGrid r k) (hq : OnGrid q k) : OnGrid (r - q) k := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hq
  exact ⟨n - m, by rw [hn, hm]; push_cast; ring⟩

/-- The grid exponent of a word: `exponent - 1`, and 0 for the subnormals. -/
def gx (w : UInt64) : ℕ := Wasm.IEEE64.exponent w - 1

theorem onGrid_word (w : UInt64) : OnGrid (value w) (gx w) := by
  obtain ⟨n, hn⟩ := TrigNearest.grid_dvd w
  refine ⟨n, ?_⟩
  unfold gx
  rw [value, hn]
  push_cast
  ring

theorem word_lt (w : UInt64) : |value w| < 2 ^ (53 + gx w) / 2 ^ 1074 := TrigNearest.grid_bound w

/-- Discreteness: a grid number below `2 ^ 53 + 1` grid steps has at most 53 bits. -/
theorem rep_of_onGrid {r : ℝ} {k : ℕ} (h : OnGrid r k) (hk : k ≤ 2043)
    (hb : |r| < (2 ^ 53 + 1) * 2 ^ k / 2 ^ 1074) : Rep r := by
  obtain ⟨n, hn⟩ := h
  have hpos : (0 : ℝ) < 2 ^ k / 2 ^ 1074 := by positivity
  have h1 : |(n : ℝ)| < 2 ^ 53 + 1 := by
    rw [hn, show (n : ℝ) * 2 ^ k / 2 ^ 1074 = (n : ℝ) * (2 ^ k / 2 ^ 1074) by ring, abs_mul,
      abs_of_pos hpos] at hb
    rw [show (2 ^ 53 + 1 : ℝ) * 2 ^ k / 2 ^ 1074 = (2 ^ 53 + 1) * (2 ^ k / 2 ^ 1074) by ring]
      at hb
    exact lt_of_mul_lt_mul_right hb hpos.le
  have h2 : |n| < 2 ^ 53 + 1 := by exact_mod_cast h1
  rw [hn]
  exact rep_grid n k (by omega) hk

/-- A word at least `2 ^ (52 + k)` scaled units in magnitude has grid exponent at least `k`. -/
theorem gx_ge (w : UInt64) (k : ℕ) (h : 2 ^ (52 + k) / 2 ^ 1074 ≤ |value w|) : k ≤ gx w := by
  by_contra hc
  have h1 := word_lt w
  have h2 : (2 : ℝ) ^ (53 + gx w) ≤ 2 ^ (52 + k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (53 + gx w) / 2 ^ 1074 ≤ 2 ^ (52 + k) / 2 ^ 1074 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  linarith

/-- A normal word is at least `2 ^ (52 + gx w)` scaled units in magnitude. -/
theorem word_ge (w : UInt64) (h : 1 ≤ Wasm.IEEE64.exponent w) :
    2 ^ (52 + gx w) / 2 ^ 1074 ≤ |value w| := TrigNearest.grid_lower w h

/-- A word of grid exponent `g` is at most `(2 ^ 53 - 1) 2 ^ g` scaled units. -/
theorem word_le (w : UInt64) : |value w| ≤ (2 ^ 53 - 1) * 2 ^ gx w / 2 ^ 1074 := by
  obtain ⟨n, hn⟩ := onGrid_word w
  have h := word_lt w
  have hpos : (0 : ℝ) < 2 ^ gx w / 2 ^ 1074 := by positivity
  rw [hn, show (n : ℝ) * 2 ^ gx w / 2 ^ 1074 = (n : ℝ) * (2 ^ gx w / 2 ^ 1074) by ring, abs_mul,
    abs_of_pos hpos] at h ⊢
  rw [show (2 : ℝ) ^ (53 + gx w) / 2 ^ 1074 = 2 ^ 53 * (2 ^ gx w / 2 ^ 1074) by
    rw [pow_add]; ring] at h
  have h1 : |(n : ℝ)| < 2 ^ 53 := lt_of_mul_lt_mul_right h hpos.le
  have h2 : |n| < 2 ^ 53 := by exact_mod_cast h1
  have h3 : |n| ≤ 2 ^ 53 - 1 := by omega
  have h4 : |(n : ℝ)| ≤ 2 ^ 53 - 1 := by exact_mod_cast h3
  rw [show (2 ^ 53 - 1 : ℝ) * 2 ^ gx w / 2 ^ 1074 = (2 ^ 53 - 1) * (2 ^ gx w / 2 ^ 1074) by ring]
  exact mul_le_mul_of_nonneg_right h4 hpos.le

/-- A power of two up to `2 ^ 2096` scaled units is held by a word. -/
theorem rep_pow (n : ℕ) (hn : n ≤ 2096) : Rep (2 ^ n / 2 ^ 1074) := by
  by_cases h : n ≤ 2043
  · have := rep_grid 1 n (by norm_num) h
    simpa using this
  · have := rep_grid (2 ^ (n - 2043)) 2043
      (by rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_right₀ (by norm_num) (by omega))
      le_rfl
    convert this using 1
    push_cast
    rw [← pow_add, Nat.sub_add_cancel (by omega)]

/-- A nearest word to a held number holds it. -/
theorem eq_of_nearest (c : UInt64) (r : ℝ) (hn : ∀ v : UInt64, |value c - r| ≤ |value v - r|)
    (hr : Rep r) : value c = r := by
  obtain ⟨w, -, hv⟩ := hr
  have h := hn w
  rw [hv, sub_self, abs_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- A nearest word to `t` is at least any held `P ≤ |t|` in magnitude. -/
theorem nearest_ge (c : UInt64) (t P : ℝ) (hn : ∀ v : UInt64, |value c - t| ≤ |value v - t|)
    (hP : Rep P) (hP0 : 0 ≤ P) (htP : P ≤ |t|) : P ≤ |value c| := by
  have h3 := abs_sub_abs_le_abs_sub t (value c)
  rw [abs_sub_comm t] at h3
  rcases le_total 0 t with ht | ht
  · obtain ⟨w, -, hv⟩ := hP
    have h := hn w
    rw [hv, abs_of_nonpos (show P - t ≤ 0 by rw [abs_of_nonneg ht] at htP; linarith)] at h
    rw [abs_of_nonneg ht] at h3 htP
    linarith
  · obtain ⟨w, -, hv⟩ := rep_neg hP
    have h := hn w
    rw [hv, abs_of_nonneg (show 0 ≤ -P - t by rw [abs_of_nonpos ht] at htP; linarith)] at h
    rw [abs_of_nonpos ht] at h3 htP
    linarith

/-- A nearest word to `t` is at most any held `P ≥ |t|` in magnitude. -/
theorem nearest_le (c : UInt64) (t P : ℝ) (hn : ∀ v : UInt64, |value c - t| ≤ |value v - t|)
    (hP : Rep P) (htP : |t| ≤ P) : |value c| ≤ P := by
  have h3 := abs_sub_abs_le_abs_sub (value c) t
  rcases le_total 0 t with ht | ht
  · obtain ⟨w, -, hv⟩ := hP
    have h := hn w
    rw [hv, abs_of_nonneg (show 0 ≤ P - t by rw [abs_of_nonneg ht] at htP; linarith)] at h
    rw [abs_of_nonneg ht] at h3 htP
    linarith
  · obtain ⟨w, -, hv⟩ := rep_neg hP
    have h := hn w
    rw [hv, abs_of_nonpos (show -P - t ≤ 0 by rw [abs_of_nonpos ht] at htP; linarith)] at h
    rw [abs_of_nonpos ht] at h3 htP
    linarith

/-- A nearest word to `t` below `2 ^ 1022` keeps `t` below the top of its own binade. -/
theorem lt_binade (c : UInt64) (t : ℝ) (hn : ∀ v : UInt64, |value c - t| ≤ |value v - t|)
    (ht : |t| ≤ 2 ^ 1022) : |t| < 2 ^ (53 + gx c) / 2 ^ 1074 := by
  by_contra h
  push_neg at h
  have hc := word_lt c
  have hle : 53 + gx c ≤ 2096 := by
    by_contra h'
    have h1 : (2 : ℝ) ^ 2097 ≤ 2 ^ (53 + gx c) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 1022 < 2 ^ 2097 / 2 ^ 1074 := by norm_num
    have h3 : (2 : ℝ) ^ 2097 / 2 ^ 1074 ≤ 2 ^ (53 + gx c) / 2 ^ 1074 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h4 : |value c| ≤ 2 ^ 1022 := by
      have := nearest_le c t (2 ^ (1022 + 1074) / 2 ^ 1074) hn (rep_pow _ (by norm_num))
        (by rw [pow_add, mul_div_cancel_right₀ _ (by positivity)]; exact ht)
      rwa [pow_add, mul_div_cancel_right₀ _ (by positivity)] at this
    linarith
  have := nearest_ge c t _ hn (rep_pow _ hle) (by positivity) h
  linarith

/-- `add a b` is `sub a (negate b)`. -/
theorem add_eq_sub (a b : UInt64) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) := by
  rw [show Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) =
    Wasm.IEEE64.add a (Wasm.IEEE64.negate (Wasm.IEEE64.negate b)) from rfl,
    F64RelativeStep.negate_negate]

/-- `|x + y| = | |x| - |y| |` for operands of opposite signs. -/
theorem abs_add_opp (x y : ℝ) (h : x * y < 0) : |x + y| = |(|x| - |y|)| := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at h) with hx | hx
  · have hy : 0 < y := by nlinarith
    rw [abs_of_neg hx, abs_of_pos hy, show -x - y = -(x + y) by ring, abs_neg]
  · have hy : y < 0 := by nlinarith
    rw [abs_of_pos hx, abs_of_neg hy, sub_neg_eq_add]

/-- The sum of two words of the same sign is at least either in magnitude. -/
theorem abs_add_same (x y : ℝ) (h : 0 ≤ x * y) : |x + y| = |x| + |y| := by
  rcases le_total 0 x with hx | hx
  · rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (by linarith)]
    · have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
      have hxy : x * y = 0 := le_antisymm this h
      rcases mul_eq_zero.mp hxy with h0 | h0 <;> simp [h0, abs_nonneg]
  · rcases le_total 0 y with hy | hy
    · have : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hy
      have hxy : x * y = 0 := le_antisymm this h
      rcases mul_eq_zero.mp hxy with h0 | h0 <;> simp [h0, abs_nonneg]
    · rw [abs_of_nonpos hx, abs_of_nonpos hy, abs_of_nonpos (by linarith)]
      ring

/-- The rounded sum of two words with a sum below `2 ^ 1022`: finite and nearest. -/
theorem add_near (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hs : |value a + value b| ≤ 2 ^ 1022) :
    Finite (Wasm.IEEE64.add a b) ∧ ∀ v : UInt64,
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ |value v - (value a + value b)| := by
  have h : |value a + value b| < 2 ^ 1023 := lt_of_le_of_lt hs (by norm_num)
  exact ⟨(F64AddBounds.add_real_relative a b ha hb h).1, TrigNearest.add_nearest a b ha hb h⟩

/-- The rounded difference of two words with a difference below `2 ^ 1022`: finite and nearest. -/
theorem sub_near (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hs : |value a - value b| ≤ 2 ^ 1022) :
    Finite (Wasm.IEEE64.sub a b) ∧ ∀ v : UInt64,
      |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ |value v - (value a - value b)| := by
  have h : |value a - value b| < 2 ^ 1023 := lt_of_le_of_lt hs (by norm_num)
  exact ⟨(F64AddBounds.sub_real_relative a b ha hb h).1, TrigNearest.sub_nearest a b ha hb h⟩

/-- A difference that a word holds is computed exactly. -/
theorem sub_exact_rep (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hs : |value a - value b| ≤ 2 ^ 1022) (hr : Rep (value a - value b)) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  obtain ⟨hf, hn⟩ := sub_near a b ha hb hs
  exact ⟨hf, eq_of_nearest _ _ hn hr⟩

/-- A sum that a word holds is computed exactly. -/
theorem add_exact_rep (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hs : |value a + value b| ≤ 2 ^ 1022) (hr : Rep (value a + value b)) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = value a + value b := by
  obtain ⟨hf, hn⟩ := add_near a b ha hb hs
  exact ⟨hf, eq_of_nearest _ _ hn hr⟩

/-- A word no larger than another has no larger grid exponent. -/
theorem gx_le_of_abs (a b : UInt64) (hab : |value b| ≤ |value a|) : gx b ≤ gx a := by
  by_contra h
  have hbe : 1 ≤ Wasm.IEEE64.exponent b := by unfold gx at h; omega
  have h1 := word_ge b hbe
  have h2 := word_lt a
  have h3 : (2 : ℝ) ^ (53 + gx a) ≤ 2 ^ (52 + gx b) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
  linarith

/-- The grid exponent of a word below `2 ^ 1021` is at most 2042. -/
theorem gx_small (a : UInt64) (h : |value a| < 2 ^ 1021) : gx a ≤ 2042 := by
  by_contra hc
  have hae : 1 ≤ Wasm.IEEE64.exponent a := by unfold gx at hc; omega
  have h1 := word_ge a hae
  have h2 : (2 : ℝ) ^ (52 + 2043) ≤ 2 ^ (52 + gx a) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
  have h4 : (2 : ℝ) ^ 1021 = 2 ^ (52 + 2043) / 2 ^ 1074 := by norm_num
  linarith

/-- Dekker's `Fast2Sum`: for `|b| ≤ |a|`, `z = (a + b) - a` and `t = b - z` are exact, and `t` is
the rounding error of `a + b`, at most `|b|`. -/
theorem fast_two_sum (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hab : |value b| ≤ |value a|) (hbig : |value a| ≤ 2 ^ 1020) :
    Finite (Wasm.IEEE64.add a b) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a) ∧
      value (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a) = value (Wasm.IEEE64.add a b) - value a ∧
      Finite (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) ∧
      value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) =
        value a + value b - value (Wasm.IEEE64.add a b) ∧
      |value a + value b - value (Wasm.IEEE64.add a b)| ≤ |value b| := by
  set s := Wasm.IEEE64.add a b with hsdef
  have ht2 : |value a + value b| ≤ 2 * |value a| := by
    have := abs_add_le (value a) (value b); linarith
  have hb0 := abs_nonneg (value b)
  obtain ⟨hsf, hn⟩ := add_near a b ha hb (by linarith [show (2 : ℝ) * 2 ^ 1020 ≤ 2 ^ 1022 by norm_num])
  have he : |value a + value b - value s| ≤ |value b| := by
    have h := hn a
    rw [show value a - (value a + value b) = -value b by ring, abs_neg, abs_sub_comm] at h
    exact h
  have hgb := gx_le_of_abs a b hab
  have hga := gx_small a (by linarith [show (2 : ℝ) ^ 1020 < 2 ^ 1021 by norm_num])
  have hts := lt_binade s _ hn (by linarith [show (2 : ℝ) * 2 ^ 1020 ≤ 2 ^ 1022 by norm_num])
  have hgs : gx s ≤ 2043 := by
    have h := hts
    by_contra hc
    have h1 : (2 : ℝ) ^ (53 + 2044) ≤ 2 ^ (53 + gx s) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hs2 : |value s| ≤ 2 ^ 1021 := by
      have := nearest_le s _ (2 ^ (1021 + 1074) / 2 ^ 1074) hn (rep_pow _ (by norm_num))
        (by rw [pow_add, mul_div_cancel_right₀ _ (by positivity)]
            linarith [show (2 : ℝ) * 2 ^ 1020 ≤ 2 ^ 1021 by norm_num])
      rwa [pow_add, mul_div_cancel_right₀ _ (by positivity)] at this
    have hse : 1 ≤ Wasm.IEEE64.exponent s := by unfold gx at hc; omega
    have h2 := word_ge s hse
    have h3 : (2 : ℝ) ^ (52 + 2044) ≤ 2 ^ (52 + gx s) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
    have h5 : (2 : ℝ) ^ 1021 < 2 ^ (52 + 2044) / 2 ^ 1074 := by norm_num
    linarith
  have hhs : |value s - (value a + value b)| ≤ 2 ^ gx s / 2 / 2 ^ 1074 :=
    (F64NearestSum.add_half_spacing a b ha hb (gx s) hts (by omega)).2
  -- The error of `s` on the grid of `a`, one step coarser.
  have hha : |value s - (value a + value b)| ≤ 2 ^ gx a / 2 ^ 1074 := by
    have hlt : |value a + value b| < 2 ^ (53 + (gx a + 1)) / 2 ^ 1074 := by
      have := word_lt a
      rw [show 53 + (gx a + 1) = (53 + gx a) + 1 by ring, pow_succ]
      linarith [show 2 * (2 : ℝ) ^ (53 + gx a) / 2 ^ 1074 = 2 ^ (53 + gx a) * 2 / 2 ^ 1074 by ring]
    have h := (F64NearestSum.add_half_spacing a b ha hb (gx a + 1) hlt (by omega)).2
    rwa [pow_succ, mul_div_cancel_right₀ _ (by norm_num)] at h
  -- `z = s - a` is held by a word.
  have hz : Rep (value s - value a) := by
    by_cases hst : value a * value b < 0 ∧ |value a| ≤ 2 * |value b|
    · obtain ⟨hnb, hnbv⟩ := F64Magnitude.negate_value b hb
      have hab' : |value a - value (Wasm.IEEE64.negate b)| = |value a + value b| := by
        rw [hnbv, sub_neg_eq_add]
      have hopp := abs_add_opp _ _ hst.1
      obtain ⟨-, hsv⟩ := F64Sterbenz.sub_exact a (Wasm.IEEE64.negate b) ha hnb
        (by rw [hab', hopp, abs_le]; constructor <;>
          linarith [abs_nonneg (value a), abs_nonneg (value b)])
        (by rw [hab', hopp, hnbv, abs_neg, abs_le]; constructor <;> linarith)
        (by rw [hnbv, abs_neg]; linarith [show (2 : ℝ) ^ 1020 < 2 ^ 1021 by norm_num])
      rw [← add_eq_sub, hnbv, sub_neg_eq_add] at hsv
      rw [hsv, add_sub_cancel_left]
      exact rep_word b hb
    · -- The binade of `s` is at least one below that of `a`.
      have hge : gx a - 1 ≤ gx s := by
        by_cases hae : 1 ≤ Wasm.IEEE64.exponent a
        · have hA := word_ge a hae
          by_cases hga1 : gx a = 0
          · omega
          · have hP : (2 : ℝ) ^ (52 + (gx a - 1)) / 2 ^ 1074 ≤ |value a + value b| := by
              have h2 : (2 : ℝ) ^ (52 + (gx a - 1)) * 2 = 2 ^ (52 + gx a) := by
                rw [← pow_succ]; congr 1; omega
              rcases le_or_gt 0 (value a * value b) with hsame | hopp
              · rw [abs_add_same _ _ hsame]
                have : (2 : ℝ) ^ (52 + (gx a - 1)) ≤ 2 ^ (52 + gx a) :=
                  pow_le_pow_right₀ (by norm_num) (by omega)
                have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
                linarith
              · have h3 : 2 * |value b| < |value a| := by
                  by_contra h4; exact hst ⟨hopp, not_lt.mp h4⟩
                rw [abs_add_opp _ _ hopp, abs_of_nonneg (by linarith)]
                have : (2 : ℝ) ^ (52 + (gx a - 1)) / 2 ^ 1074 * 2 = 2 ^ (52 + gx a) / 2 ^ 1074 := by
                  rw [← h2]; ring
                linarith
            exact gx_ge s (gx a - 1)
              (nearest_ge s _ _ hn (rep_pow _ (by omega)) (by positivity) hP)
        · have : gx a = 0 := by unfold gx; omega
          omega
      have hgo : OnGrid (value s - value a) (min (gx s) (gx a)) :=
        onGrid_sub (onGrid_mono (onGrid_word s) (min_le_left _ _))
          (onGrid_mono (onGrid_word a) (min_le_right _ _))
      refine rep_of_onGrid hgo (by omega) ?_
      have hd : |value s - value a| ≤ |value s - (value a + value b)| + |value b| := by
        have := abs_add_le (value s - (value a + value b)) (value b)
        rwa [show value s - (value a + value b) + value b = value s - value a by ring] at this
      rcases le_or_gt (gx a) (gx s) with hle | hle
      · rw [min_eq_right hle]
        have h1 := word_lt a
        rw [pow_add] at h1
        have : (2 ^ 53 + 1 : ℝ) * 2 ^ gx a / 2 ^ 1074 =
            2 ^ 53 * 2 ^ gx a / 2 ^ 1074 + 2 ^ gx a / 2 ^ 1074 := by ring
        linarith
      · rw [min_eq_left hle.le]
        -- `s` one binade below `a`: opposite signs with `2 |b| < |a|`.
        have hsg : gx s = gx a - 1 := by omega
        have hopp : value a * value b < 0 := by
          by_contra hc
          push_neg at hc
          have hae : 1 ≤ Wasm.IEEE64.exponent a := by unfold gx at hsg; unfold gx at hle; omega
          have hA := word_ge a hae
          have := gx_ge s (gx a) (nearest_ge s _ _ hn (rep_pow _ (by omega)) (by positivity)
            (by rw [abs_add_same _ _ hc]; linarith))
          omega
        have h3 : 2 * |value b| < |value a| := by
          by_contra h4; exact hst ⟨hopp, not_lt.mp h4⟩
        have h1 := word_lt a
        have h5 : (2 : ℝ) ^ (53 + gx a) = 2 * (2 ^ 53 * 2 ^ gx s) := by
          rw [show 53 + gx a = 53 + gx s + 1 by omega, pow_succ, pow_add]
          ring
        rw [h5] at h1
        have : (2 ^ 53 + 1 : ℝ) * 2 ^ gx s / 2 ^ 1074 =
            2 ^ 53 * 2 ^ gx s / 2 ^ 1074 + 2 ^ gx s / 2 ^ 1074 := by ring
        have h6 : (2 : ℝ) ^ gx s / 2 / 2 ^ 1074 < 2 ^ gx s / 2 ^ 1074 := by
          have : (0 : ℝ) < 2 ^ gx s / 2 ^ 1074 := by positivity
          linarith [show (2 : ℝ) ^ gx s / 2 / 2 ^ 1074 = (2 ^ gx s / 2 ^ 1074) / 2 by ring]
        have h7 : 2 * (2 ^ 53 * 2 ^ gx s) / 2 ^ 1074 = 2 * (2 ^ 53 * 2 ^ gx s / (2 : ℝ) ^ 1074) := by
          ring
        linarith
  have hsa : |value s - value a| ≤ 2 * |value b| := by
    have := abs_add_le (value s - (value a + value b)) (value b)
    rw [show value s - (value a + value b) + value b = value s - value a by ring,
      abs_sub_comm (value s) (value a + value b)] at this
    linarith
  obtain ⟨hzf, hzv⟩ := sub_exact_rep s a hsf ha
    (by linarith [show (2 : ℝ) * 2 ^ 1020 ≤ 2 ^ 1022 by norm_num]) hz
  -- `t = b - z` is held by a word.
  have hr : Rep (value a + value b - value s) := by
    have hgo : OnGrid (value a + value b - value s) (min (gx b) (gx s)) :=
      onGrid_sub (onGrid_add (onGrid_mono (onGrid_word a) (le_trans (min_le_left _ _) hgb))
        (onGrid_mono (onGrid_word b) (min_le_left _ _))) (onGrid_mono (onGrid_word s)
          (min_le_right _ _))
    refine rep_of_onGrid hgo (by omega) ?_
    rcases le_total (gx b) (gx s) with hle | hle
    · rw [min_eq_left hle]
      have h1 := word_lt b
      rw [pow_add] at h1
      have : (2 ^ 53 + 1 : ℝ) * 2 ^ gx b / 2 ^ 1074 =
          2 ^ 53 * 2 ^ gx b / 2 ^ 1074 + 2 ^ gx b / 2 ^ 1074 := by ring
      have : (0 : ℝ) < 2 ^ gx b / 2 ^ 1074 := by positivity
      linarith
    · rw [min_eq_right hle, abs_sub_comm]
      have : (2 ^ 53 + 1 : ℝ) * 2 ^ gx s / 2 ^ 1074 =
          2 ^ 53 * 2 ^ gx s / 2 ^ 1074 + 2 ^ gx s / 2 ^ 1074 := by ring
      have : (0 : ℝ) < 2 ^ 53 * 2 ^ gx s / 2 ^ 1074 := by positivity
      have : (2 : ℝ) ^ gx s / 2 / 2 ^ 1074 ≤ 2 ^ gx s / 2 ^ 1074 := by
        have : (0 : ℝ) ≤ 2 ^ gx s / 2 ^ 1074 := by positivity
        linarith [show (2 : ℝ) ^ gx s / 2 / 2 ^ 1074 = (2 ^ gx s / 2 ^ 1074) / 2 by ring]
      linarith
  have hbz : value b - value (Wasm.IEEE64.sub s a) = value a + value b - value s := by
    rw [hzv]; ring
  obtain ⟨htf, htv⟩ := sub_exact_rep b _ hb hzf
    (by rw [hbz]; linarith [show (2 : ℝ) ^ 1020 ≤ 2 ^ 1022 by norm_num]) (by rw [hbz]; exact hr)
  exact ⟨hsf, hzf, hzv, htf, by rw [htv, hbz], he⟩

#print axioms rep_of_onGrid
#print axioms nearest_ge
#print axioms nearest_le
#print axioms lt_binade
#print axioms fast_two_sum

end Verified.Examples.ErfcEft
