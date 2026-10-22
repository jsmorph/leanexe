import Library.Numerics.Float64.Tgamma.TgammaAsym2
import Library.Numerics.Float64.Tgamma.TgammaAsym3

/-!
The branch of `Tgamma.asLgammaAsym` above `11.5`.  It adds the constant `c0 + c1` to the first
product with `fastSum`, and evaluates the series `F(u) = (c2 + c3) + u G(u)` at `u = z2h`, with
`G` in plain double arithmetic (`TgammaAsym2.hiE`, within `2 ^ -66`) and `c2` added by
`fastTwoSum`.  The state `(lh, ll, fh, fl)` after the branch satisfies `BranchOK`: with `X` the
argument, `lh + ll + (fh + fl)/X` lies within `6 · 2 ^ -63` of `log Γ X`.  The bound adds the
`2 ^ -61` of the first product, the `2 ^ -64` of `StirlingFact`, and the change of the series
between `z2h` and `1/X²`, which `TgammaPolyLip.eval_lip` bounds by `2 ^ -44/340` of `1/X²`
(`asym_hi`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAsym4
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaPolyDDD TgammaPolyLip TgammaAsym2

set_option exponentiation.threshold 4096

/-- The state after the branch of `asLgammaAsym`. -/
def BranchOK (X : ℝ) (t : Float × Float × Float × Float) : Prop :=
  Finite t.1.toBits ∧ Finite t.2.1.toBits ∧ Finite t.2.2.1.toBits ∧ Finite t.2.2.2.toBits ∧
    |value t.1.toBits + value t.2.1.toBits + 1 / X * (value t.2.2.1.toBits + value t.2.2.2.toBits) -
        Real.log (Real.Gamma X)| ≤ 6 / 2 ^ 63 ∧
    1 ≤ value t.1.toBits ∧ value t.1.toBits ≤ 800 ∧ |value t.2.1.toBits| ≤ 3 / 4 / 2 ^ 14 ∧
    |value t.2.2.1.toBits| ≤ 1 / 10 ∧ |value t.2.2.2.toBits| ≤ 1 / 2 ^ 50

/-- The branch of `asLgammaAsym` above `11.5`, as the code computes it. -/
def hiBranch (tab : Array UInt64) (lh ll z2h : Float) : Float × Float × Float × Float :=
  let (lh, ll) := fastSum lh ll (entry tab 0) (entry tab 1)
  let x2 := z2h * z2h
  let q0 := entry tab 4 + z2h * entry tab 6
  let q2 := entry tab 8 + z2h * entry tab 10
  let q4 := entry tab 12 + z2h * entry tab 14
  let fl := z2h * (q0 + x2 * (q2 + x2 * q4))
  let (fh, fl) := fastTwoSum (entry tab 2) fl
  (lh, ll, fh, fl + entry tab 3)

theorem hfl_eq (u : Float) :
    evalF hiE u = u * ((entry asymTable 4 + u * entry asymTable 6) +
      u * u * ((entry asymTable 8 + u * entry asymTable 10) +
        u * u * (entry asymTable 12 + u * entry asymTable 14))) := by
  simp only [evalF, hiE, pairE, u2E, aw]
  rfl

theorem hconst :
    (41 / 100 : ℚ) ≤ PolyBound.ratOfWord asymTable[0]! ∧
    PolyBound.ratOfWord asymTable[0]! ≤ 42 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[1]!) ≤ 1 / 2 ^ 55 ∧
    (1 / 13 : ℚ) ≤ PolyBound.ratOfWord asymTable[2]! ∧
    PolyBound.ratOfWord asymTable[2]! ≤ 1 / 11 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[3]!) ≤ 1 / 2 ^ 57 := by
  decide +kernel

/-- **The branch above `11.5`.** -/
theorem asym_hi
    (hS : ∀ x : ℝ, 11 ≤ x → x ≤ 186 →
      |Real.log (Real.Gamma x) - TgammaApprox.stirHi x| ≤ 1 / 2 ^ 64)
    (Ph Pl u : Float) (hPhf : Finite Ph.toBits) (hPlf : Finite Pl.toBits) (huf : Finite u.toBits)
    (X : ℝ) (hX1 : 23 / 2 - 1 / 2 ^ 44 ≤ X) (hX2 : X ≤ 186)
    (hP : |value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)| ≤ 1 / 2 ^ 61)
    (hPl : |value Pl.toBits| ≤ 73 / 100 / 2 ^ 14) (hPh1 : 1 ≤ value Ph.toBits)
    (hPh2 : value Ph.toBits ≤ 797)
    (hu : |value u.toBits - (1 / X) ^ 2| ≤ (1 / X) ^ 2 / 2 ^ 44) :
    BranchOK X (hiBranch asymTable Ph Pl u) := by
  -- the constants
  obtain ⟨k0lo, k0hi, k1, k2lo, k2hi, k3⟩ := hconst
  obtain ⟨c0, hc0⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[0]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[1]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[2]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[3]! : ℝ) := ⟨_, rfl⟩
  have h0v : value (entry asymTable 0).toBits = c0 := by rw [ev 0 0 rfl (by norm_num), hc0]
  have h1v : value (entry asymTable 1).toBits = c1 := by rw [ev 1 1 rfl (by norm_num), hc1]
  have h2v : value (entry asymTable 2).toBits = c2 := by rw [ev 2 2 rfl (by norm_num), hc2]
  have h3v : value (entry asymTable 3).toBits = c3 := by rw [ev 3 3 rfl (by norm_num), hc3]
  have h0f := ef 0 0 rfl (by norm_num)
  have h1f := ef 1 1 rfl (by norm_num)
  have h2f := ef 2 2 rfl (by norm_num)
  have h3f := ef 3 3 rfl (by norm_num)
  have hc0lo : 41 / 100 ≤ c0 := by
    have : ((41 / 100 : ℚ) : ℝ) ≤ c0 := by rw [hc0]; exact_mod_cast k0lo
    push_cast at this; exact this
  have hc0hi : c0 ≤ 42 / 100 := by
    have : c0 ≤ ((42 / 100 : ℚ) : ℝ) := by rw [hc0]; exact_mod_cast k0hi
    push_cast at this; exact this
  have hc1b : |c1| ≤ 1 / 2 ^ 55 := by
    have := TgammaSmall.abs_rat_le _ _ k1
    rw [← hc1] at this; push_cast at this; exact this
  have hc2lo : 1 / 13 ≤ c2 := by
    have : ((1 / 13 : ℚ) : ℝ) ≤ c2 := by rw [hc2]; exact_mod_cast k2lo
    push_cast at this; exact this
  have hc2hi : c2 ≤ 1 / 11 := by
    have : c2 ≤ ((1 / 11 : ℚ) : ℝ) := by rw [hc2]; exact_mod_cast k2hi
    push_cast at this; exact this
  have hc3b : |c3| ≤ 1 / 2 ^ 57 := by
    have := TgammaSmall.abs_rat_le _ _ k3
    rw [← hc3] at this; push_cast at this; exact this
  obtain ⟨hc11, hc12⟩ := abs_le.mp hc1b
  obtain ⟨hc31, hc32⟩ := abs_le.mp hc3b
  -- `Z = 1/X` and `W = Z²`
  have hX0 : 0 < X := by linarith
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 1 / X := ⟨_, rfl⟩
  rw [← hZ] at hu
  have hZ0 : 0 < Z := by rw [hZ]; exact one_div_pos.mpr hX0
  have hZle : Z ≤ 100 / 1149 := by
    rw [hZ, div_le_div_iff₀ hX0 (by norm_num)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 ≤ 1 / 100)]
  have hW : Z ^ 2 ≤ 1 / 132 := by
    have := pow_le_pow_left₀ hZ0.le hZle 2
    linarith [(by norm_num : ((100 : ℝ) / 1149) ^ 2 ≤ 1 / 132)]
  have hW0 : 0 ≤ Z ^ 2 := sq_nonneg Z
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have hub : |value u.toBits| ≤ 1 / 128 := by
    rw [abs_le]; constructor <;> linarith [(by norm_num : (1 : ℝ) / 132 * (1 + 1 / 2 ^ 44) ≤ 1 / 128)]
  -- the sum with `c0 + c1`
  have hPhb : |value Ph.toBits| ≤ 797 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨hs1f, hs2f, hse, hs2b⟩ := fastSum_spec Ph Pl (entry asymTable 0) (entry asymTable 1)
    hPhf hPlf h0f h1f
    (by rw [h0v, abs_of_pos (by linarith : (0 : ℝ) < c0),
          abs_of_pos (show (0 : ℝ) < value Ph.toBits by linarith)]; linarith)
    (by linarith [(by norm_num : (797 : ℝ) < 2 ^ 898)]) (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55)
    (by rw [h1v]; linarith) (by norm_num)
  rw [h0v, h1v] at hse
  -- the series
  have hu' : |value u.toBits| ≤ ((Uhi : ℚ) : ℝ) := by
    rw [show ((Uhi : ℚ) : ℝ) = 1 / 128 by rw [Uhi]; norm_num]; exact hub
  obtain ⟨hfl, hRm⟩ := evalF_approx hiE Uhi u huf hu' hiE_ok
  have hfle : |value (evalF hiE u).toBits - evalR hiE (value u.toBits)| ≤ 1 / 2 ^ 66 := by
    have h := hfl.2
    have : ((bnd hiE Uhi).2 : ℝ) ≤ ((1 / 2 ^ 66 : ℚ) : ℝ) := by exact_mod_cast hiE_err
    push_cast at this
    linarith
  have hRb : |evalR hiE (value u.toBits)| ≤ 1 / 2 ^ 15 := by
    have : ((bnd hiE Uhi).1 : ℝ) ≤ ((1 / 2 ^ 15 : ℚ) : ℝ) := by exact_mod_cast hiE_mag
    push_cast at this
    linarith
  have hflb : |value (evalF hiE u).toBits| ≤ 1 / 2 ^ 14 := by
    have := abs_sub_abs_le_abs_sub (value (evalF hiE u).toBits) (evalR hiE (value u.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 15 + 1 / 2 ^ 66 ≤ 1 / 2 ^ 14)]
  obtain ⟨ht1f, ht2f, htsum, ht2le, ht2b⟩ := fastTwoSum_spec (entry asymTable 2) (evalF hiE u) h2f
    hfl.1 (by rw [h2v, abs_of_pos (by linarith : (0 : ℝ) < c2)]
              linarith [(by norm_num : (1 : ℝ) / 2 ^ 14 ≤ 1 / 13)])
    (by rw [h2v, abs_of_pos (by linarith : (0 : ℝ) < c2)]
        linarith [(by norm_num : (1 : ℝ) / 11 < 2 ^ 900)])
  rw [h2v] at htsum
  -- the code
  unfold BranchOK hiBranch
  dsimp only
  rw [← hfl_eq u]
  generalize fastSum Ph Pl (entry asymTable 0) (entry asymTable 1) = s at hs1f hs2f hse hs2b ⊢
  obtain ⟨s1, s2⟩ := s
  dsimp only at hs1f hs2f hse hs2b ⊢
  generalize fastTwoSum (entry asymTable 2) (evalF hiE u) = t at ht1f ht2f htsum ht2le ht2b ⊢
  obtain ⟨t1, t2⟩ := t
  dsimp only at ht1f ht2f htsum ht2le ht2b ⊢
  -- `s1` and `s2`
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  obtain ⟨hPl1, hPl2⟩ := abs_le.mp hPl
  have hs1b : |value s1.toBits| ≤ 800 := by
    obtain ⟨he1, he2⟩ := abs_le.mp hse
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2b
    rcases abs_cases (value s1.toBits) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at he1 he2 hl1 hl2 ⊢ <;>
      linarith only [he1, he2, hl1, hl2, hPh1, hPh2, hPl1, hPl2, hc0lo, hc0hi, hc11, hc12]
  have hs2 : |value s2.toBits| ≤ 3 / 4 / 2 ^ 14 := by
    have : |value s1.toBits| / 2 ^ 51 ≤ 800 / 2 ^ 51 := div_le_div_of_nonneg_right hs1b (by norm_num)
    linarith only [hs2b, this, (by norm_num : ((73 : ℝ) / 100 / 2 ^ 14 + 1 / 2 ^ 55) * (1 + 1 / 2 ^ 51) +
      800 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 3 / 4 / 2 ^ 14)]
  have hse' : |value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c0 + c1))| ≤
      1 / 2 ^ 65 := by
    have : |value s1.toBits| / 2 ^ 52 ≤ 800 / 2 ^ 52 := div_le_div_of_nonneg_right hs1b (by norm_num)
    have h2 : (3 * (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55) + |value s1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤ (3 * (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55) + 800 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith only [this]) (by norm_num)
    linarith only [hse, h2, (by norm_num : (3 * ((73 : ℝ) / 100 / 2 ^ 14 + 1 / 2 ^ 55) + 800 / 2 ^ 52 +
      1 / 2 ^ 1074) / 2 ^ 53 ≤ 1 / 2 ^ 65)]
  -- `t1`, `t2`, and `f4 = t2 + c3`
  have ht1b : |value t1.toBits| ≤ 1 / 10 := by
    have h1 := abs_add_le (value t1.toBits + value t2.toBits) (-value t2.toBits)
    rw [add_neg_cancel_right, abs_neg, htsum] at h1
    have h2 := abs_add_le c2 (value (evalF hiE u).toBits)
    rw [abs_of_pos (by linarith : (0 : ℝ) < c2)] at h2
    linarith only [h1, h2, ht2le, hflb, hc2hi, (by norm_num : (1 : ℝ) / 11 + 1 / 2 ^ 14 + 1 / 2 ^ 14 ≤ 1 / 10)]
  have ht2 : |value t2.toBits| ≤ 1 / 10 / 2 ^ 52 + 1 / 2 ^ 1074 := by
    have : |value t1.toBits| / 2 ^ 52 ≤ 1 / 10 / 2 ^ 52 := div_le_div_of_nonneg_right ht1b (by norm_num)
    linarith only [ht2b, this]
  have hf4 := fapprox_add (fapprox_self t2 ht2f) (fapprox_self _ h3f)
    (1 / 10 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 57)
    (by rw [h3v, add_zero, add_zero]; linarith only [abs_add_le (value t2.toBits) c3, ht2, hc3b])
    (by norm_num)
  rw [h3v] at hf4
  have hf4e : |value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)| ≤ 1 / 2 ^ 100 := by
    have := hf4.2
    linarith only [this, (by norm_num : (0 : ℝ) + 0 + (1 / 10 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 57) / 2 ^ 53 ≤
      1 / 2 ^ 100)]
  have hf4b : |value (t2 + entry asymTable 3).toBits| ≤ 1 / 2 ^ 54 := by
    have := abs_sub_abs_le_abs_sub (value (t2 + entry asymTable 3).toBits) (value t2.toBits + c3)
    linarith only [this, hf4e, ht2, hc3b, abs_add_le (value t2.toBits) c3, (by norm_num : (1 : ℝ) / 10 / 2 ^ 52 + 1 / 2 ^ 1074 +
      1 / 2 ^ 57 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 54)]
  refine ⟨hs1f, hs2f, ht1f, hf4.1, ?_, ?_, ?_, hs2, ht1b, hf4b.trans (by norm_num)⟩
  · -- the error
    have hlip := eval_lip Uhi (by rw [Uhi]; norm_num) (value u.toBits) (Z ^ 2) hu'
      (by rw [show ((Uhi : ℚ) : ℝ) = 1 / 128 by rw [Uhi]; norm_num, abs_of_nonneg hW0]
          linarith only [hW, (by norm_num : (1 : ℝ) / 132 ≤ 1 / 128)]) Fhi
    have hlq : ((lipQ Uhi Fhi : ℚ) : ℝ) ≤ 1 / 340 := by
      have : ((lipQ Uhi Fhi : ℚ) : ℝ) ≤ ((1 / 340 : ℚ) : ℝ) := by exact_mod_cast lip_hi
      push_cast at this; exact this
    have hlip' : |PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2)| ≤
        1 / 340 * (1 / 132 / 2 ^ 44) := by
      refine hlip.trans (mul_le_mul hlq ?_ (abs_nonneg _) (by norm_num))
      rw [abs_le]; constructor <;> linarith only [hu1, hu2, hW]
    have hΦ : PolyBound.eval Fhi (value u.toBits) = c2 + c3 + evalR hiE (value u.toBits) := by
      rw [eval_hi]
      simp only [TgammaApprox.q]
      push_cast
      rw [hc2, hc3]
    have hst : TgammaApprox.stirHi X =
        (X - 1 / 2) * (Real.log X - 1) + (c0 + c1) + Z * PolyBound.eval Fhi (Z ^ 2) := by
      rw [TgammaApprox.stirHi, hZ, hc0, hc1, one_div_pow, Fhi]
      simp only [TgammaApprox.q]
      push_cast
      ring
    have hSX := hS X (by linarith only [hX1, (by norm_num : (11 : ℝ) ≤ 23 / 2 - 1 / 2 ^ 44)]) hX2
    rw [← hZ]
    have hsplit : value s1.toBits + value s2.toBits + Z * (value t1.toBits +
        value (t2 + entry asymTable 3).toBits) - Real.log (Real.Gamma X) =
        (value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c0 + c1))) +
        (value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)) +
        Z * ((value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
          (value (evalF hiE u).toBits - evalR hiE (value u.toBits)) +
          (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2))) +
        (TgammaApprox.stirHi X - Real.log (Real.Gamma X)) := by
      linear_combination Z * htsum - Z * hΦ - hst
    rw [hsplit]
    have hD : |(value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
        (value (evalF hiE u).toBits - evalR hiE (value u.toBits)) +
        (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2))| ≤
        1 / 2 ^ 100 + 1 / 2 ^ 66 + 1 / 340 * (1 / 132 / 2 ^ 44) := by
      have e1 := abs_add_le ((value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
        (value (evalF hiE u).toBits - evalR hiE (value u.toBits)))
        (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2))
      have e2 := abs_add_le (value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3))
        (value (evalF hiE u).toBits - evalR hiE (value u.toBits))
      linarith only [e1, e2, hf4e, hfle, hlip']
    have hZD : |Z * ((value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
        (value (evalF hiE u).toBits - evalR hiE (value u.toBits)) +
        (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2)))| ≤
        100 / 1149 * (1 / 2 ^ 100 + 1 / 2 ^ 66 + 1 / 340 * (1 / 132 / 2 ^ 44)) := by
      rw [abs_mul, abs_of_pos hZ0]
      exact mul_le_mul hZle hD (abs_nonneg _) (by norm_num)
    rw [abs_sub_comm] at hSX
    have e1 := abs_add_le
      ((value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c0 + c1))) +
        (value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)) +
        Z * ((value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
          (value (evalF hiE u).toBits - evalR hiE (value u.toBits)) +
          (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2))))
      (TgammaApprox.stirHi X - Real.log (Real.Gamma X))
    have e2 := abs_add_le
      ((value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c0 + c1))) +
        (value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)))
      (Z * ((value (t2 + entry asymTable 3).toBits - (value t2.toBits + c3)) +
          (value (evalF hiE u).toBits - evalR hiE (value u.toBits)) +
          (PolyBound.eval Fhi (value u.toBits) - PolyBound.eval Fhi (Z ^ 2))))
    have e3 := abs_add_le
      (value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c0 + c1)))
      (value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1))
    linarith only [e1, e2, e3, hse', hP, hZD, hSX, (by norm_num : (1 : ℝ) / 2 ^ 65 + 1 / 2 ^ 61 +
      100 / 1149 * (1 / 2 ^ 100 + 1 / 2 ^ 66 + 1 / 340 * (1 / 132 / 2 ^ 44)) + 1 / 2 ^ 64 ≤
      6 / 2 ^ 63)]
  · obtain ⟨he1, he2⟩ := abs_le.mp hse'
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2
    linarith only [he1, he2, hl1, hl2, hPh1, hPl1, hc0lo, hc11,
      (by norm_num : (1 : ℝ) / 2 ^ 65 ≤ 1 / 1000), (by norm_num : (3 : ℝ) / 4 / 2 ^ 14 ≤ 1 / 1000),
      (by norm_num : (73 : ℝ) / 100 / 2 ^ 14 ≤ 1 / 1000), (by norm_num : (1 : ℝ) / 2 ^ 55 ≤ 1 / 1000)]
  · obtain ⟨he1, he2⟩ := abs_le.mp hse'
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2
    linarith only [he1, he2, hl1, hl2, hPh2, hPl2, hc0hi, hc12,
      (by norm_num : (1 : ℝ) / 2 ^ 65 ≤ 1 / 1000), (by norm_num : (3 : ℝ) / 4 / 2 ^ 14 ≤ 1 / 1000),
      (by norm_num : (73 : ℝ) / 100 / 2 ^ 14 ≤ 1 / 1000), (by norm_num : (1 : ℝ) / 2 ^ 55 ≤ 1 / 1000)]

#print axioms asym_hi

end Library.Numerics.Float64.Tgamma.TgammaAsym4
