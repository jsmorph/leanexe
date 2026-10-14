import Verified.Examples.TgammaAcc1

/-!
`Tgamma.sprod`, the step `x (x0 + x1 + x2)` of the powers of `d` in the accurate path of `Tgamma`.
The high part `z0 = x x0` is split by `splt` at multiples of `2^-26`, its remainder and the error of
the product join the low parts, and the result is a triple whose first part is a multiple of
`2^-26` and whose sum lies within `2^-76` of `x (x0 + x1 + x2)` (`sprod_spec`).  `fts_approx`
bounds `fastTwoSum a b` without Dekker's condition `|b| ≤ |a|`.
-/

namespace Verified.Examples.TgammaAcc2
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAcc1 TgammaFloor

set_option exponentiation.threshold 4096

/-- `fastTwoSum a b` without the condition `|b| ≤ |a|`. -/
theorem fts_approx (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℝ)
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A + B ≤ 2 ^ 1000) :
    Finite (fastTwoSum a b).1.toBits ∧ Finite (fastTwoSum a b).2.toBits ∧
      |value (fastTwoSum a b).1.toBits + value (fastTwoSum a b).2.toBits -
        (value a.toBits + value b.toBits)| ≤ B / 2 ^ 53 + (A + B) / 2 ^ 104 ∧
      |value (fastTwoSum a b).1.toBits| ≤ (A + B) * (1 + 1 / 2 ^ 53) ∧
      |value (fastTwoSum a b).2.toBits| ≤ (A + B) / 2 ^ 51 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hAB53 : (A + B) / 2 ^ 53 ≤ A + B := div_le_self (by positivity) (by norm_num)
  have hAB53' : (A + B) / 2 ^ 53 / 2 ^ 53 ≤ A + B := by
    have : (A + B) / 2 ^ 53 / 2 ^ 53 ≤ (A + B) / 2 ^ 53 := div_le_self (by positivity) (by norm_num)
    linarith
  have hs := fapprox_add (fapprox_self a ha) (fapprox_self b hb) (A + B)
    (by linarith [abs_add_le (value a.toBits) (value b.toBits)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)])
  have hse := hs.2
  simp only [zero_add] at hse
  have hz := fapprox_sub (fapprox_self _ hs.1) (fapprox_self a ha) (B + (A + B) / 2 ^ 53)
    (by
      have : |value (a + b).toBits - value a.toBits| ≤ |value b.toBits| + (A + B) / 2 ^ 53 := by
        have h1 := abs_sub_le (value (a + b).toBits) (value a.toBits + value b.toBits)
          (value a.toBits)
        rw [show value a.toBits + value b.toBits - value a.toBits = value b.toBits by ring] at h1
        linarith
      linarith) (by linarith [(by norm_num : (2 : ℝ) * 2 ^ 1000 < 2 ^ 1023)])
  have hze := hz.2
  simp only [zero_add] at hze
  have hbz : |value b.toBits - value ((a + b) - a).toBits| ≤
      (A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53 := by
    have h1 := abs_sub_le (value b.toBits) (value (a + b).toBits - value a.toBits)
      (value ((a + b) - a).toBits)
    rw [show value b.toBits - (value (a + b).toBits - value a.toBits) =
      -(value (a + b).toBits - (value a.toBits + value b.toBits)) by ring, abs_neg,
      abs_sub_comm (value (a + b).toBits - value a.toBits)] at h1
    linarith
  have ht := fapprox_sub (fapprox_self b hb) (fapprox_self _ hz.1)
    ((A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53) (by linarith)
    (by linarith [(by norm_num : (3 : ℝ) * 2 ^ 1000 < 2 ^ 1023)])
  have hte := ht.2
  simp only [zero_add] at hte
  unfold fastTwoSum
  dsimp only
  refine ⟨hs.1, ht.1, ?_, ?_, ?_⟩
  · have hsplit : value (a + b).toBits + value (b - ((a + b) - a)).toBits -
        (value a.toBits + value b.toBits) =
        (value (b - ((a + b) - a)).toBits - (value b.toBits - value ((a + b) - a).toBits)) -
        (value ((a + b) - a).toBits - (value (a + b).toBits - value a.toBits)) := by ring
    rw [hsplit]
    have h1 := abs_sub
      (value (b - ((a + b) - a)).toBits - (value b.toBits - value ((a + b) - a).toBits))
      (value ((a + b) - a).toBits - (value (a + b).toBits - value a.toBits))
    have h2 : (A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53 ≤ 3 * (A + B) / 2 ^ 53 := by
      have : (A + B) / 2 ^ 53 / 2 ^ 53 ≤ (A + B) / 2 ^ 53 := by
        apply div_le_self (by positivity) (by norm_num)
      linarith
    have h3 : ((A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53) / 2 ^ 53 ≤
        3 * (A + B) / 2 ^ 106 := by
      have := div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by ring : 3 * (A + B) / 2 ^ 53 / 2 ^ 53 = 3 * (A + B) / 2 ^ 106)]
    linarith
  · have := abs_sub_abs_le_abs_sub (value (a + b).toBits) (value a.toBits + value b.toBits)
    linarith [abs_add_le (value a.toBits) (value b.toBits)]
  · have h1 := abs_sub_abs_le_abs_sub (value (b - ((a + b) - a)).toBits)
      (value b.toBits - value ((a + b) - a).toBits)
    have h2 : (A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53 ≤ 3 * (A + B) / 2 ^ 53 := by
      have : (A + B) / 2 ^ 53 / 2 ^ 53 ≤ (A + B) / 2 ^ 53 := by
        apply div_le_self (by positivity) (by norm_num)
      linarith
    have h3 : ((A + B) / 2 ^ 53 + (B + (A + B) / 2 ^ 53) / 2 ^ 53) / 2 ^ 53 ≤
        3 * (A + B) / 2 ^ 106 := by
      have := div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by ring : 3 * (A + B) / 2 ^ 53 / 2 ^ 53 = 3 * (A + B) / 2 ^ 106)]
    linarith

/-- **`sprod`**: the next power of `d` as a triple. -/
theorem sprod_spec (hF : FmaSpec.FmaNearest) (x x0 x1 x2 : Float) (hxf : Finite x.toBits)
    (h0f : Finite x0.toBits) (h1f : Finite x1.toBits) (h2f : Finite x2.toBits)
    (hx : |value x.toBits| ≤ 1) (h0b : |value x0.toBits| ≤ 2) (h1b : |value x1.toBits| ≤ 1 / 2 ^ 20)
    (h2b : |value x2.toBits| ≤ 1 / 2 ^ 46) :
    Finite (sprod x x0 x1 x2).1.toBits ∧ Finite (sprod x x0 x1 x2).2.1.toBits ∧
      Finite (sprod x x0 x1 x2).2.2.toBits ∧
      (∃ k : ℤ, value (sprod x x0 x1 x2).1.toBits = k / 2 ^ 26) ∧
      |value (sprod x x0 x1 x2).1.toBits - value x.toBits * value x0.toBits| ≤ 1 / 2 ^ 24 ∧
      |value (sprod x x0 x1 x2).2.1.toBits| ≤ |value x.toBits| * |value x1.toBits| + 1 / 2 ^ 24 ∧
      |value (sprod x x0 x1 x2).2.2.toBits| ≤ |value x.toBits| * |value x2.toBits| + 1 / 2 ^ 50 ∧
      |value (sprod x x0 x1 x2).1.toBits + value (sprod x x0 x1 x2).2.1.toBits +
          value (sprod x x0 x1 x2).2.2.toBits -
          value x.toBits * (value x0.toBits + value x1.toBits + value x2.toBits)| ≤ 1 / 2 ^ 76 := by
  have hx0 := abs_nonneg (value x.toBits)
  -- the products
  have hp0 : |value x.toBits| * |value x0.toBits| ≤ 2 := by nlinarith [abs_nonneg (value x0.toBits)]
  have hp1 : |value x.toBits| * |value x1.toBits| ≤ 1 / 2 ^ 20 := by
    nlinarith [abs_nonneg (value x1.toBits)]
  have hp2 : |value x.toBits| * |value x2.toBits| ≤ 1 / 2 ^ 46 := by
    nlinarith [abs_nonneg (value x2.toBits)]
  have hz0 := fapprox_mul (fapprox_self x hxf) (fapprox_self x0 h0f) |value x.toBits|
    |value x0.toBits| le_rfl le_rfl (|value x.toBits| * |value x0.toBits|) (by simp)
    (by linarith [(by norm_num : (2 : ℝ) < 2 ^ 1022)])
  have hz0e := hz0.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hz0e
  have hz1 := fapprox_mul (fapprox_self x hxf) (fapprox_self x1 h1f) |value x.toBits|
    |value x1.toBits| le_rfl le_rfl (|value x.toBits| * |value x1.toBits|) (by simp)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 20 < 2 ^ 1022)])
  have hz1e := hz1.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hz1e
  have hz2a := fapprox_mul (fapprox_self x hxf) (fapprox_self x2 h2f) |value x.toBits|
    |value x2.toBits| le_rfl le_rfl (|value x.toBits| * |value x2.toBits|) (by simp)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 < 2 ^ 1022)])
  have hz2ae := hz2a.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hz2ae
  -- the errors of the products by `fma`
  obtain ⟨hn0f, hn0v⟩ := neg_float _ hz0.1
  obtain ⟨hn1f, hn1v⟩ := neg_float _ hz1.1
  have hf0 := fma_approx hF x x0 (-(x * x0)) hxf h0f hn0f (by
    rw [hn0v, ← sub_eq_add_neg, abs_sub_comm]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
      (by linarith : |value x.toBits| * |value x0.toBits| / 2 ^ 53 ≤ 2 / 2 ^ 53)])
  rw [hn0v, ← sub_eq_add_neg] at hf0
  have hf1 := fma_approx hF x x1 (-(x * x1)) hxf h1f hn1f (by
    rw [hn1v, ← sub_eq_add_neg, abs_sub_comm]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
      (by linarith : |value x.toBits| * |value x1.toBits| / 2 ^ 53 ≤ 2 / 2 ^ 53)])
  rw [hn1v, ← sub_eq_add_neg] at hf1
  have hf0e : |value (Fma.fma x x0 (-(x * x0))).toBits -
      (value x.toBits * value x0.toBits - value (x * x0).toBits)| ≤ 1 / 2 ^ 104 := by
    have h := hf0.2
    have : |value x.toBits * value x0.toBits - value (x * x0).toBits| ≤
        2 / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]; linarith
    have : |value x.toBits * value x0.toBits - value (x * x0).toBits| / 2 ^ 53 ≤
        (2 / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 := div_le_div_of_nonneg_right this (by norm_num)
    linarith [(by norm_num : (2 / 2 ^ 53 + 1 / 2 ^ 1075 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
  have hf1e : |value (Fma.fma x x1 (-(x * x1))).toBits -
      (value x.toBits * value x1.toBits - value (x * x1).toBits)| ≤ 1 / 2 ^ 120 := by
    have h := hf1.2
    have h3 : |value x.toBits * value x1.toBits - value (x * x1).toBits| ≤
        1 / 2 ^ 20 / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]
      have : |value x.toBits| * |value x1.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 20 / 2 ^ 53 :=
        div_le_div_of_nonneg_right hp1 (by norm_num)
      linarith
    have : |value x.toBits * value x1.toBits - value (x * x1).toBits| / 2 ^ 53 ≤
        (1 / 2 ^ 20 / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 := div_le_div_of_nonneg_right h3 (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 20 / 2 ^ 53 + 1 / 2 ^ 1075 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 120)]
  -- names for the words
  set z0 := x * x0 with hz0d
  set z0l := Fma.fma x x0 (-z0) with hz0ld
  set z1 := x * x1 with hz1d
  set f1 := Fma.fma x x1 (-z1) with hf1d
  set p2 := x * x2 with hp2d
  set vx := value x.toBits with hvx
  have hz0b : |value z0.toBits| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub (value z0.toBits) (vx * value x0.toBits)
    rw [abs_mul] at this
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1)]
  have hd0 : |vx * value x0.toBits - value z0.toBits| ≤ 1 / 2 ^ 51 := by
    rw [abs_sub_comm]
    have : |vx| * |value x0.toBits| / 2 ^ 53 ≤ 2 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hp0 (by norm_num)
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 51)]
  have hz0lb : |value z0l.toBits| ≤ 1 / 2 ^ 50 := by
    have := abs_sub_abs_le_abs_sub (value z0l.toBits) (vx * value x0.toBits - value z0.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 104 ≤ 1 / 2 ^ 50)]
  have hd1 : |vx * value x1.toBits - value z1.toBits| ≤ 1 / 2 ^ 72 := by
    rw [abs_sub_comm]
    have : |vx| * |value x1.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 20 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hp1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 20 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 72)]
  have hf1b : |value f1.toBits| ≤ 1 / 2 ^ 71 := by
    have := abs_sub_abs_le_abs_sub (value f1.toBits) (vx * value x1.toBits - value z1.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 72 + 1 / 2 ^ 120 ≤ 1 / 2 ^ 71)]
  have hd2 : |value p2.toBits - vx * value x2.toBits| ≤ 1 / 2 ^ 98 := by
    have : |vx| * |value x2.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 46 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hp2 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 98)]
  have hp2b : |value p2.toBits| ≤ |vx| * |value x2.toBits| + 1 / 2 ^ 98 := by
    have := abs_sub_abs_le_abs_sub (value p2.toBits) (vx * value x2.toBits)
    rw [abs_mul] at this
    linarith
  -- `z2 = x x2 + fma x x1 (-z1)`
  have hz2 := fapprox_add (fapprox_self p2 hz2a.1) (fapprox_self f1 hf1.1) (1 / 2 ^ 45) (by
      simp only [add_zero]
      have := abs_add_le (value p2.toBits) (value f1.toBits)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 + 1 / 2 ^ 98 + 1 / 2 ^ 71 ≤ 1 / 2 ^ 45)])
    (by norm_num)
  set z2 := p2 + f1 with hz2d
  have hz2e : |value z2.toBits - (value p2.toBits + value f1.toBits)| ≤ 1 / 2 ^ 98 := by
    have h := hz2.2
    simp only [zero_add] at h
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 / 2 ^ 53 = 1 / 2 ^ 98)]
  -- `splt z0`
  obtain ⟨hhf, hef, ⟨k, hk⟩, hhe, hee⟩ := TgammaAcc1.splt_spec z0 hz0.1
    (by linarith [(by norm_num : (3 : ℝ) ≤ 2 ^ 26)])
  set zh := (splt z0).1 with hzhd
  set e := (splt z0).2 with hed
  have heb : |value e.toBits| ≤ 1 / 2 ^ 25 + 1 / 2 ^ 77 := by
    have := abs_sub_abs_le_abs_sub (value e.toBits) (value z0.toBits - value zh.toBits)
    rw [abs_sub_comm (value z0.toBits)] at this
    linarith
  -- `fastTwoSum e z0l`, without the order of magnitudes
  obtain ⟨hgf, hg2f, hge, hg1b, hg2b⟩ := fts_approx e z0l hef hf0.1 (1 / 2 ^ 25 + 1 / 2 ^ 77)
    (1 / 2 ^ 50) heb hz0lb (by norm_num)
  set g := fastTwoSum e z0l with hgd
  -- `twoSum g.1 z1`, exact
  have hz1b : |value z1.toBits| ≤ |vx| * |value x1.toBits| + 1 / 2 ^ 72 := by
    have := abs_sub_abs_le_abs_sub (value z1.toBits) (vx * value x1.toBits)
    rw [abs_sub_comm (value z1.toBits), abs_mul] at this
    linarith
  obtain ⟨hl1f, hl2f, hlsum, hl2b⟩ := twoSum_spec g.1 z1 hgf hz1.1
    (by linarith [(by norm_num : ((1 : ℝ) / 2 ^ 25 + 1 / 2 ^ 77 + 1 / 2 ^ 50) *
      (1 + 1 / 2 ^ 53) < 2 ^ 900)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 20 + 1 / 2 ^ 72 < 2 ^ 900)])
  set l := twoSum g.1 z1 with hld
  have hl1b : |value l.1.toBits| ≤ |vx| * |value x1.toBits| + 1 / 2 ^ 24 := by
    have h3 := abs_sub_abs_le_abs_sub (value l.1.toBits) (-(value l.2.toBits))
    rw [sub_neg_eq_add, abs_neg, hlsum] at h3
    have h4 := abs_add_le (value g.1.toBits) (value z1.toBits)
    have h0 := abs_nonneg (value l.1.toBits)
    -- `|l1| (1 - 2^-52) ≤ |g1| + |z1| + 2^-1074`
    have hgb : |value g.1.toBits| ≤ 1 / 2 ^ 25 + 1 / 2 ^ 49 := by
      linarith [(by norm_num : ((1 : ℝ) / 2 ^ 25 + 1 / 2 ^ 77 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 53) ≤
        1 / 2 ^ 25 + 1 / 2 ^ 49)]
    have hP : |vx| * |value x1.toBits| ≤ 1 / 2 ^ 20 := hp1
    linarith
  have hl2b' : |value l.2.toBits| ≤ 1 / 2 ^ 71 := by
    refine hl2b.trans ?_
    have : |value l.1.toBits| ≤ 1 / 2 ^ 20 + 1 / 2 ^ 24 := by linarith
    have : |value l.1.toBits| / 2 ^ 52 ≤ (1 / 2 ^ 20 + 1 / 2 ^ 24) / 2 ^ 52 :=
      div_le_div_of_nonneg_right this (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 20 + 1 / 2 ^ 24) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 71)]
  -- the low sum `(l.2 + g.2) + z2`
  have ha := fapprox_add (fapprox_self l.2 hl2f) (fapprox_self g.2 hg2f) (1 / 2 ^ 70) (by
      simp only [add_zero]
      have := abs_add_le (value l.2.toBits) (value g.2.toBits)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 71 + (1 / 2 ^ 25 + 1 / 2 ^ 77 + 1 / 2 ^ 50) / 2 ^ 51 ≤
        1 / 2 ^ 70)])
    (by norm_num)
  set a := l.2 + g.2 with had
  have hae : |value a.toBits - (value l.2.toBits + value g.2.toBits)| ≤ 1 / 2 ^ 123 := by
    have h := ha.2
    simp only [zero_add] at h
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 70 / 2 ^ 53 = 1 / 2 ^ 123)]
  have hab : |value a.toBits| ≤ 1 / 2 ^ 69 := by
    have := abs_sub_abs_le_abs_sub (value a.toBits) (value l.2.toBits + value g.2.toBits)
    have := abs_add_le (value l.2.toBits) (value g.2.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 71 + (1 / 2 ^ 25 + 1 / 2 ^ 77 + 1 / 2 ^ 50) / 2 ^ 51 +
      1 / 2 ^ 123 ≤ 1 / 2 ^ 69)]
  have hz2b : |value z2.toBits| ≤ |vx| * |value x2.toBits| + 1 / 2 ^ 70 := by
    have := abs_sub_abs_le_abs_sub (value z2.toBits) (value p2.toBits + value f1.toBits)
    have := abs_add_le (value p2.toBits) (value f1.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 98 + 1 / 2 ^ 71 + 1 / 2 ^ 98 ≤ 1 / 2 ^ 70)]
  have hr := fapprox_add (fapprox_self a ha.1) (fapprox_self z2 hz2.1) (1 / 2 ^ 45) (by
      simp only [add_zero]
      have := abs_add_le (value a.toBits) (value z2.toBits)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 69 + (1 / 2 ^ 46 + 1 / 2 ^ 70) ≤ 1 / 2 ^ 45)])
    (by norm_num)
  have hre : |value (a + z2).toBits - (value a.toBits + value z2.toBits)| ≤ 1 / 2 ^ 98 := by
    have h := hr.2
    simp only [zero_add] at h
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 / 2 ^ 53 = 1 / 2 ^ 98)]
  have hsp : sprod x x0 x1 x2 = (zh, l.1, a + z2) := rfl
  rw [hsp]
  dsimp only
  refine ⟨hhf, hl1f, hr.1, ⟨k, hk⟩, ?_, hl1b, ?_, ?_⟩
  · have := abs_sub_le (value zh.toBits) (value z0.toBits) (vx * value x0.toBits)
    rw [abs_sub_comm (value z0.toBits)] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 25 + 1 / 2 ^ 51 ≤ 1 / 2 ^ 24)]
  · have := abs_sub_abs_le_abs_sub (value (a + z2).toBits) (value a.toBits + value z2.toBits)
    have := abs_add_le (value a.toBits) (value z2.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 98 + 1 / 2 ^ 69 + 1 / 2 ^ 70 ≤ 1 / 2 ^ 50)]
  · -- the sum telescopes through the exact steps
    have hsplit : value zh.toBits + value l.1.toBits + value (a + z2).toBits -
        vx * (value x0.toBits + value x1.toBits + value x2.toBits) =
        (value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)) +
        (value e.toBits - (value z0.toBits - value zh.toBits)) +
        (value z0l.toBits - (vx * value x0.toBits - value z0.toBits)) +
        (value z2.toBits - (value p2.toBits + value f1.toBits)) +
        (value f1.toBits - (vx * value x1.toBits - value z1.toBits)) +
        (value p2.toBits - vx * value x2.toBits) := by
      linear_combination hlsum
    rw [hsplit]
    have b1 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)) +
        (value e.toBits - (value z0.toBits - value zh.toBits)) +
        (value z0l.toBits - (vx * value x0.toBits - value z0.toBits)) +
        (value z2.toBits - (value p2.toBits + value f1.toBits)) +
        (value f1.toBits - (vx * value x1.toBits - value z1.toBits)))
      (value p2.toBits - vx * value x2.toBits)
    have b2 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)) +
        (value e.toBits - (value z0.toBits - value zh.toBits)) +
        (value z0l.toBits - (vx * value x0.toBits - value z0.toBits)) +
        (value z2.toBits - (value p2.toBits + value f1.toBits)))
      (value f1.toBits - (vx * value x1.toBits - value z1.toBits))
    have b3 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)) +
        (value e.toBits - (value z0.toBits - value zh.toBits)) +
        (value z0l.toBits - (vx * value x0.toBits - value z0.toBits)))
      (value z2.toBits - (value p2.toBits + value f1.toBits))
    have b4 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)) +
        (value e.toBits - (value z0.toBits - value zh.toBits)))
      (value z0l.toBits - (vx * value x0.toBits - value z0.toBits))
    have b5 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)) +
        (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits)))
      (value e.toBits - (value z0.toBits - value zh.toBits))
    have b6 := abs_add_le ((value (a + z2).toBits - (value a.toBits + value z2.toBits)) +
        (value a.toBits - (value l.2.toBits + value g.2.toBits)))
      (value g.1.toBits + value g.2.toBits - (value e.toBits + value z0l.toBits))
    have b7 := abs_add_le (value (a + z2).toBits - (value a.toBits + value z2.toBits))
      (value a.toBits - (value l.2.toBits + value g.2.toBits))
    have hfe : 1 / 2 ^ 50 / 2 ^ 53 + (1 / 2 ^ 25 + 1 / 2 ^ 77 + 1 / 2 ^ 50) / 2 ^ 104 ≤
        (1 : ℝ) / 2 ^ 102 := by norm_num
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 98 + 1 / 2 ^ 123 + 1 / 2 ^ 102 + 1 / 2 ^ 77 +
      1 / 2 ^ 104 + 1 / 2 ^ 98 + 1 / 2 ^ 120 + 1 / 2 ^ 98 ≤ 1 / 2 ^ 76)]

#print axioms fts_approx
#print axioms sprod_spec

end Verified.Examples.TgammaAcc2
