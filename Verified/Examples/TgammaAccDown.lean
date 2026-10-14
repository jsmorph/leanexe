import Verified.Examples.TgammaAccUp

/-!
The loop of `Tgamma.accurate` for `x ≥ j + 1`, which multiplies the factors `x - 1, x - 2, …`.
For `x ≥ 5` every factor `x - k` down to `j ≥ 4` is a double: `x` is a multiple of `2 ^ (a - 52)`
for `2 ^ a ≤ x < 2 ^ (a + 1)`, and so is `x - k`, with a smaller numerator.  The factor's low part
stays zero (`down_factor`), and `TgammaAccUp.prod_step` bounds each product (`down_step`).
-/

namespace Verified.Examples.TgammaAccDown
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAcc1 TgammaAccUp

set_option exponentiation.threshold 4096

/-- One step of the loop for `x ≥ j + 1`. -/
def downStep (s : Float × Float × Float × Float) : Float × Float × Float × Float :=
  ((fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).1,
    (fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).2,
    (mulDD3 (fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).1
      (fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).2
      s.2.2.1 s.2.2.2).1,
    (mulDD3 (fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).1
      (fastTwoSum (fastTwoSum s.1 (-1.0)).1 (s.2.1 + (fastTwoSum s.1 (-1.0)).2)).2
      s.2.2.1 s.2.2.2).2)

theorem neg_one_value : value (-1.0 : Float).toBits = -1 := by
  have := fapprox_neg (fapprox_self _ TgammaRecip.one_finite)
  rw [TgammaRecip.one_value] at this
  have h0 := abs_nonpos_iff.mp this.2
  linarith

theorem neg_one_finite : Finite (-1.0 : Float).toBits :=
  (fapprox_neg (fapprox_self _ TgammaRecip.one_finite)).1

/-- **The factor step**: from the double `xph = F` with `xpl = 0`, the next factor is the double
`F - 1` with a zero low part, when `F - 1` lies on the grid `2 ^ -g` with a numerator at most
`2 ^ 53` and `2 ≤ F`. -/
theorem down_factor (xph xpl : Float) (hph : Finite xph.toBits) (hpl : Finite xpl.toBits)
    (hpl0 : value xpl.toBits = 0) (k : ℤ) (g : ℕ) (hg : g ≤ 1074)
    (hk : value xph.toBits - 1 = k / 2 ^ g) (hkb : |k| ≤ 2 ^ 53) (h2 : 2 ≤ value xph.toBits)
    (h8 : value xph.toBits ≤ 2 ^ 8) :
    Finite (fastTwoSum (fastTwoSum xph (-1.0)).1 (xpl + (fastTwoSum xph (-1.0)).2)).1.toBits ∧
      Finite (fastTwoSum (fastTwoSum xph (-1.0)).1 (xpl + (fastTwoSum xph (-1.0)).2)).2.toBits ∧
      value (fastTwoSum (fastTwoSum xph (-1.0)).1 (xpl + (fastTwoSum xph (-1.0)).2)).1.toBits =
        value xph.toBits - 1 ∧
      value (fastTwoSum (fastTwoSum xph (-1.0)).1 (xpl + (fastTwoSum xph (-1.0)).2)).2.toBits =
        0 := by
  -- `xph - 1` is exact
  obtain ⟨hsf, hsv⟩ := grid_add xph (-1.0) hph neg_one_finite k g
    (by rw [neg_one_value, ← sub_eq_add_neg]; exact hk) hkb hg
  rw [neg_one_value] at hsv
  obtain ⟨hs1f, hs2f, hssum, -, -⟩ := fastTwoSum_spec xph (-1.0) hph neg_one_finite
    (by rw [neg_one_value, abs_neg, abs_one, abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 8 < 2 ^ 900)])
  have hfa : (fastTwoSum xph (-1.0)).1 = xph + -1.0 := rfl
  have ha1 : value (fastTwoSum xph (-1.0)).1.toBits = value xph.toBits - 1 := by
    rw [hfa, hsv]; ring
  have ha2 : value (fastTwoSum xph (-1.0)).2.toBits = 0 := by
    rw [neg_one_value, ha1] at hssum; linarith
  generalize fastTwoSum xph (-1.0) = A at hs1f hs2f ha1 ha2 ⊢
  -- `xpl + A.2 = 0`, exact
  obtain ⟨htf, htv⟩ := grid_add xpl A.2 hpl hs2f 0 0 (by rw [hpl0, ha2]; simp) (by norm_num)
    (by norm_num)
  rw [hpl0, ha2, add_zero] at htv
  generalize xpl + A.2 = t at htf htv ⊢
  -- `fastTwoSum A.1 t` with `t = 0`
  obtain ⟨hu1f, hu2f, husum, hu2t, -⟩ := fastTwoSum_spec A.1 t hs1f htf
    (by rw [htv, abs_zero]; exact abs_nonneg _)
    (by rw [ha1, abs_of_pos (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 8 < 2 ^ 900)])
  have hu2 : value (fastTwoSum A.1 t).2.toBits = 0 := by
    have := hu2t; rw [htv, abs_zero] at this; exact abs_nonpos_iff.mp this
  refine ⟨hu1f, hu2f, ?_, hu2⟩
  rw [hu2, htv] at husum
  linarith

/-- `(x - 1) (x - 2) ⋯ (x - (m + 1))`. -/
noncomputable def D (v : ℝ) (m : ℕ) : ℝ := ∏ i ∈ Finset.range (m + 1), (v - (i + 1 : ℕ))

theorem D_succ (v : ℝ) (m : ℕ) : D v (m + 1) = (v - (m + 2 : ℕ)) * D v m := by
  rw [D, D, Finset.prod_range_succ]; ring

/-- The state `(xph, xpl, wh, wl)` of the loop for `x ≥ j + 1` after `m` steps. -/
def DownInv (v : ℝ) (m : ℕ) (s : Float × Float × Float × Float) : Prop :=
  Finite s.1.toBits ∧ Finite s.2.1.toBits ∧ Finite s.2.2.1.toBits ∧ Finite s.2.2.2.toBits ∧
    value s.1.toBits = v - (m + 1 : ℕ) ∧ value s.2.1.toBits = 0 ∧
    |value s.2.2.1.toBits + value s.2.2.2.toBits - D v m| ≤ m / 2 ^ 95 * |D v m| ∧
    |value s.2.2.2.toBits| ≤ |value s.2.2.1.toBits| / 2 ^ 50 ∧
    |value s.2.2.1.toBits| ≤ 2 ^ 518 ∧ 1 ≤ |D v m| ∧ |D v m| ≤ 2 ^ (8 * (m + 1))

/-- **One step of the loop for `x ≥ j + 1`.** -/
theorem down_step (hF : FmaSpec.FmaNearest) (v : ℝ) (k0 : ℤ) (g : ℕ) (hg : g ≤ 1074)
    (hv : v = k0 / 2 ^ g) (hk0 : |k0| ≤ 2 ^ 53) (m : ℕ) (s : Float × Float × Float × Float)
    (hm : m + 2 ≤ 32) (hv4 : (m + 2 : ℕ) + 4 ≤ v) (hv8 : v ≤ 2 ^ 8) (h : DownInv v m s) :
    DownInv v (m + 1) (downStep s) := by
  obtain ⟨xph, xpl, wh, wl⟩ := s
  obtain ⟨hphf, hplf, hwhf, hwlf, hph, hpl, hWe, hwlb, hwhb, hD1, hD2⟩ := h
  dsimp only at hphf hplf hwhf hwlf hph hpl hWe hwlb hwhb
  have hm' : ((m + 2 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast hm
  have hmm : (m : ℝ) + 2 = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
  -- the factor
  have hkv : value xph.toBits - 1 = ((k0 - (m + 2 : ℕ) * 2 ^ g : ℤ) : ℝ) / 2 ^ g := by
    rw [hph, hv]; push_cast; field_simp; ring
  have hkb : |k0 - (m + 2 : ℕ) * 2 ^ g| ≤ 2 ^ 53 := by
    have h1 : (((k0 - (m + 2 : ℕ) * 2 ^ g : ℤ) : ℝ)) = (v - (m + 2 : ℕ)) * 2 ^ g := by
      rw [hv]; push_cast; field_simp
    have h2 : |((k0 - (m + 2 : ℕ) * 2 ^ g : ℤ) : ℝ)| ≤ |(k0 : ℝ)| := by
      rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g),
        abs_of_pos (by linarith : (0 : ℝ) < v - (m + 2 : ℕ))]
      have : (k0 : ℝ) = v * 2 ^ g := by rw [hv]; field_simp
      rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g),
        abs_of_pos (by linarith : (0 : ℝ) < v)]
      have : (0 : ℝ) ≤ (m + 2 : ℕ) := by positivity
      nlinarith [(by positivity : (0 : ℝ) < 2 ^ g)]
    have h3 : |(k0 : ℝ)| ≤ 2 ^ 53 := by rw [← Int.cast_abs]; exact_mod_cast hk0
    have h4 := h2.trans h3
    rw [← Int.cast_abs] at h4
    exact_mod_cast h4
  obtain ⟨hf1f, hf2f, hf1v, hf2v⟩ := down_factor xph xpl hphf hplf hpl _ g hg hkv hkb
    (by rw [hph]; push_cast at hv4 ⊢; linarith) (by rw [hph]; push_cast at hv4 ⊢; linarith)
  set f := fastTwoSum (fastTwoSum xph (-1.0)).1 (xpl + (fastTwoSum xph (-1.0)).2) with hfdef
  set X := v - (m + 2 : ℕ) with hXdef
  have hXv : value f.1.toBits + value f.2.toBits = X := by
    rw [hf1v, hf2v, hph, hXdef]; push_cast; ring
  have hX4 : 4 ≤ X := by rw [hXdef]; linarith
  -- the product
  have hδ : (m : ℝ) / 2 ^ 95 ≤ 1 / 2 ^ 80 := by
    have : (m : ℝ) ≤ 32 := by push_cast at hm'; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨hp1f, hp2f, hpe, hp2b, hp1b, -⟩ := prod_step hF f.1 f.2 wh wl X (D v m) (m / 2 ^ 95)
    hf1f hf2f hwhf hwlf hXv (by rw [hf2v, abs_zero]; positivity)
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 ≤ 4)])
    (by rw [abs_of_pos (by linarith)]; linarith) hWe (by positivity) hδ hwlb hwhb
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 57 ≤ 1)])
  have hDs : X * D v m = D v (m + 1) := by rw [D_succ]
  rw [hDs] at hpe hp1b
  have hD1' : 1 ≤ |D v (m + 1)| := by
    rw [← hDs, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < X)]
    nlinarith
  have hX8 : |X| ≤ 2 ^ 8 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < X), hXdef]
    have : (0 : ℝ) ≤ (m + 2 : ℕ) := by positivity
    linarith
  have hD2' : |D v (m + 1)| ≤ 2 ^ (8 * (m + 1 + 1)) := by
    rw [← hDs, abs_mul, show 8 * (m + 1 + 1) = 8 + 8 * (m + 1) by ring, pow_add]
    exact mul_le_mul hX8 hD2 (abs_nonneg _) (by positivity)
  have hstep : downStep (xph, xpl, wh, wl) =
      (f.1, f.2, (mulDD3 f.1 f.2 wh wl).1, (mulDD3 f.1 f.2 wh wl).2) := rfl
  rw [hstep]
  unfold DownInv
  dsimp only
  refine ⟨hf1f, hf2f, hp1f, hp2f, by rw [hf1v, hph]; push_cast; ring, hf2v, ?_, ?_, ?_, hD1', hD2'⟩
  · refine hpe.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    push_cast
    have e4 : ((m : ℝ) + 1) / 2 ^ 95 = m / 2 ^ 95 + 1 / 2 ^ 95 := by ring
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 96 ≤ 1 / 2 ^ 95)]
  · have := div_le_div_of_nonneg_left (abs_nonneg (value (mulDD3 f.1 f.2 wh wl).1.toBits))
      (by positivity : (0 : ℝ) < 2 ^ 50) (by norm_num : (2 : ℝ) ^ 50 ≤ 2 ^ 51)
    linarith
  · have h5 : |D v (m + 1)| ≤ 2 ^ 256 := by
      refine hD2'.trans (pow_le_pow_right₀ (by norm_num) ?_)
      omega
    linarith [(by norm_num : (4 : ℝ) * 2 ^ 256 ≤ 2 ^ 518)]

/-- The state before the loop: the factor and the product are `x - 1`. -/
theorem down_init (x : Float) (hx : Finite x.toBits) (k0 : ℤ) (g : ℕ) (hg : g ≤ 1074)
    (hv : value x.toBits = k0 / 2 ^ g) (hk0 : |k0| ≤ 2 ^ 53) (hv5 : 5 ≤ value x.toBits)
    (hv8 : value x.toBits ≤ 2 ^ 8) :
    DownInv (value x.toBits) 0 (x - 1.0, (0.0 : Float), x - 1.0, (0.0 : Float)) := by
  have hkv : value x.toBits - value (1.0 : Float).toBits = ((k0 - 2 ^ g : ℤ) : ℝ) / 2 ^ g := by
    rw [hv, TgammaRecip.one_value]; push_cast; field_simp
  have hkb : |k0 - 2 ^ g| ≤ 2 ^ 53 := by
    have h1 : (((k0 - 2 ^ g : ℤ) : ℝ)) = (value x.toBits - 1) * 2 ^ g := by
      rw [hv]; push_cast; field_simp
    have h2 : |((k0 - 2 ^ g : ℤ) : ℝ)| ≤ |(k0 : ℝ)| := by
      rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g),
        abs_of_pos (by linarith : (0 : ℝ) < value x.toBits - 1)]
      have : (k0 : ℝ) = value x.toBits * 2 ^ g := by rw [hv]; field_simp
      rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g),
        abs_of_pos (by linarith : (0 : ℝ) < value x.toBits)]
      nlinarith [(by positivity : (0 : ℝ) < 2 ^ g)]
    have h3 : |(k0 : ℝ)| ≤ 2 ^ 53 := by rw [← Int.cast_abs]; exact_mod_cast hk0
    have h4 := h2.trans h3
    rw [← Int.cast_abs] at h4
    exact_mod_cast h4
  obtain ⟨hsf, hsv⟩ := grid_sub x 1.0 hx TgammaRecip.one_finite _ g hkv hkb hg
  rw [TgammaRecip.one_value] at hsv
  unfold DownInv
  dsimp only
  have hD : D (value x.toBits) 0 = value x.toBits - 1 := by simp [D]
  rw [TgammaMainRed.zero_value, hD, hsv]
  refine ⟨hsf, TgammaMainRed.zero_finite, hsf, TgammaMainRed.zero_finite, by simp, rfl, by simp,
    by simp; positivity, ?_, ?_, ?_⟩
  · rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 8 ≤ 2 ^ 518)]
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; norm_num; linarith

/-- **The loop for `x ≥ j + 1`** after `m` steps. -/
theorem down_loop (hF : FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits) (k0 : ℤ) (g : ℕ)
    (hg : g ≤ 1074) (hv : value x.toBits = k0 / 2 ^ g) (hk0 : |k0| ≤ 2 ^ 53) (M : ℕ)
    (hM : M + 1 ≤ 31) (hv5 : (M + 1 : ℕ) + 4 ≤ value x.toBits) (hv8 : value x.toBits ≤ 2 ^ 8) :
    ∀ m, m ≤ M → DownInv (value x.toBits) m
      (LeanExe.loop (UInt64.ofNat m) (x - 1.0, (0.0 : Float), x - 1.0, (0.0 : Float))
        (fun _ s => downStep s)) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : LeanExe.loop (UInt64.ofNat 0) (x - 1.0, (0.0 : Float), x - 1.0, (0.0 : Float))
        (fun _ s => downStep s) = (x - 1.0, (0.0 : Float), x - 1.0, (0.0 : Float)) := by
      simp [LeanExe.loop]
    rw [h0]
    exact down_init x hx k0 g hg hv hk0 (by push_cast at hv5; linarith) hv8
  | succ m ih =>
    intro hm
    have hst := ih (by omega)
    rw [TgammaPoly.loop_succ m (by omega)]
    have hm' : ((m + 2 : ℕ) : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast (by omega : m + 2 ≤ M + 1)
    exact down_step hF (value x.toBits) k0 g hg hv hk0 m _ (by omega) (by linarith) hv8 hst

#print axioms down_factor
#print axioms down_step
#print axioms down_init
#print axioms down_loop

end Verified.Examples.TgammaAccDown
