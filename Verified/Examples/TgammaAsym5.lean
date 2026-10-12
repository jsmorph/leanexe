import Verified.Examples.TgammaAsym4

/-!
The branch of `Tgamma.asLgammaAsym` at or below `11.5`.  It adds the constant `c16 + c17` to the
first product with `fastSum`, and evaluates `(c18 + c19) + z2 ((c20 + c21) + G(u))` with
`u = z2h`, `z2 = z2h + z2l`, and `G` in plain double arithmetic (`TgammaAsym2.loE`, within
`2 ^ -65`).  The products with `z2` keep the error of the series below `2 ^ -62` relative to
`1/X`, and the state satisfies `TgammaAsym4.BranchOK` (`asym_lo`).
-/

namespace Verified.Examples.TgammaAsym5
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaPolyDDD TgammaPolyLip TgammaAsym2 TgammaAsym4

set_option exponentiation.threshold 4096

/-- The branch of `asLgammaAsym` at or below `11.5`, as the code computes it. -/
def loBranch (tab : Array UInt64) (lh ll z2h z2l : Float) : Float × Float × Float × Float :=
  let (lh, ll) := fastSum lh ll (entry tab 16) (entry tab 17)
  let x2 := z2h * z2h
  let x4 := x2 * x2
  let q0 := entry tab 22 + z2h * entry tab 24
  let q2 := entry tab 26 + z2h * entry tab 28
  let q4 := entry tab 30 + z2h * entry tab 32
  let q6 := entry tab 34 + z2h * entry tab 36
  let q8 := entry tab 38 + z2h * entry tab 40
  let q4 := q4 + x2 * (q6 + x2 * q8)
  let q0 := q0 + x2 * q2
  let q0 := q0 + x4 * q4
  let fl := z2h * q0
  let (fh, fl) := fastTwoSum (entry tab 20) fl
  let (fh, fl) := mulDD z2h z2l fh (fl + entry tab 21)
  let (fh, fl) := fastSum (entry tab 18) (entry tab 19) fh fl
  (lh, ll, fh, fl)

theorem lfl_eq (u : Float) :
    evalF loE u = u * (entry asymTable 22 + u * entry asymTable 24 +
      u * u * (entry asymTable 26 + u * entry asymTable 28) +
      u * u * (u * u) * (entry asymTable 30 + u * entry asymTable 32 +
        u * u * (entry asymTable 34 + u * entry asymTable 36 +
          u * u * (entry asymTable 38 + u * entry asymTable 40)))) := by
  simp only [evalF, loE, pairE, u2E, u4E, aw]
  rfl

theorem lconst :
    (41 / 100 : ℚ) ≤ PolyBound.ratOfWord asymTable[16]! ∧
    PolyBound.ratOfWord asymTable[16]! ≤ 42 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[17]!) ≤ 1 / 2 ^ 55 ∧
    (1 / 13 : ℚ) ≤ PolyBound.ratOfWord asymTable[18]! ∧
    PolyBound.ratOfWord asymTable[18]! ≤ 1 / 11 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[19]!) ≤ 1 / 2 ^ 57 ∧
    (-1 / 256 : ℚ) ≤ PolyBound.ratOfWord asymTable[20]! ∧
    PolyBound.ratOfWord asymTable[20]! ≤ -1 / 512 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[21]!) ≤ 1 / 2 ^ 63 := by
  decide +kernel

theorem abs4 {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |a + b + c + d| ≤ A + B + C + D :=
  (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ha hb)) hc)) hd)

theorem abs5 {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E :=
  (abs_add_le _ _).trans (add_le_add (abs4 ha hb hc hd) he)

/-- **The branch at or below `11.5`.** -/
theorem asym_lo (hF : FmaSpec.FmaNearest)
    (hS : ∀ x : ℝ, 4 ≤ x → x ≤ 12 →
      |Real.log (Real.Gamma x) - TgammaApprox.stirLo x| ≤ 1 / 2 ^ 64)
    (Ph Pl u ul : Float) (hPhf : Finite Ph.toBits) (hPlf : Finite Pl.toBits)
    (huf : Finite u.toBits) (hulf : Finite ul.toBits)
    (X : ℝ) (hX1 : 4 ≤ X) (hX2 : X ≤ 23 / 2 + 1 / 2 ^ 44)
    (hP : |value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)| ≤ 1 / 2 ^ 61)
    (hPl : |value Pl.toBits| ≤ 73 / 100 / 2 ^ 14) (hPh1 : 1 ≤ value Ph.toBits)
    (hPh2 : value Ph.toBits ≤ 797)
    (hu : |value u.toBits - (1 / X) ^ 2| ≤ (1 / X) ^ 2 / 2 ^ 44)
    (huu : |value u.toBits + value ul.toBits - (1 / X) ^ 2| ≤ (1 / X) ^ 2 / 2 ^ 76)
    (hul : |value ul.toBits| ≤ (1 / X) ^ 2 / 2 ^ 42) :
    BranchOK X (loBranch asymTable Ph Pl u ul) := by
  -- the constants
  obtain ⟨k16lo, k16hi, k17, k18lo, k18hi, k19, k20lo, k20hi, k21⟩ := lconst
  obtain ⟨c16, hc16⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[16]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c17, hc17⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[17]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c18, hc18⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[18]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c19, hc19⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[19]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c20, hc20⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[20]! : ℝ) := ⟨_, rfl⟩
  obtain ⟨c21, hc21⟩ : ∃ c, c = (PolyBound.ratOfWord asymTable[21]! : ℝ) := ⟨_, rfl⟩
  have h16v : value (entry asymTable 16).toBits = c16 := by rw [ev 16 16 rfl (by norm_num), hc16]
  have h17v : value (entry asymTable 17).toBits = c17 := by rw [ev 17 17 rfl (by norm_num), hc17]
  have h18v : value (entry asymTable 18).toBits = c18 := by rw [ev 18 18 rfl (by norm_num), hc18]
  have h19v : value (entry asymTable 19).toBits = c19 := by rw [ev 19 19 rfl (by norm_num), hc19]
  have h20v : value (entry asymTable 20).toBits = c20 := by rw [ev 20 20 rfl (by norm_num), hc20]
  have h21v : value (entry asymTable 21).toBits = c21 := by rw [ev 21 21 rfl (by norm_num), hc21]
  have h16f := ef 16 16 rfl (by norm_num)
  have h17f := ef 17 17 rfl (by norm_num)
  have h18f := ef 18 18 rfl (by norm_num)
  have h19f := ef 19 19 rfl (by norm_num)
  have h20f := ef 20 20 rfl (by norm_num)
  have h21f := ef 21 21 rfl (by norm_num)
  have hc16lo : 41 / 100 ≤ c16 := by
    have : ((41 / 100 : ℚ) : ℝ) ≤ c16 := by rw [hc16]; exact_mod_cast k16lo
    push_cast at this; exact this
  have hc16hi : c16 ≤ 42 / 100 := by
    have : c16 ≤ ((42 / 100 : ℚ) : ℝ) := by rw [hc16]; exact_mod_cast k16hi
    push_cast at this; exact this
  have hc17b : |c17| ≤ 1 / 2 ^ 55 := by
    have := TgammaSmall.abs_rat_le _ _ k17
    rw [← hc17] at this; push_cast at this; exact this
  have hc18lo : 1 / 13 ≤ c18 := by
    have : ((1 / 13 : ℚ) : ℝ) ≤ c18 := by rw [hc18]; exact_mod_cast k18lo
    push_cast at this; exact this
  have hc18hi : c18 ≤ 1 / 11 := by
    have : c18 ≤ ((1 / 11 : ℚ) : ℝ) := by rw [hc18]; exact_mod_cast k18hi
    push_cast at this; exact this
  have hc19b : |c19| ≤ 1 / 2 ^ 57 := by
    have := TgammaSmall.abs_rat_le _ _ k19
    rw [← hc19] at this; push_cast at this; exact this
  have hc20lo : -1 / 256 ≤ c20 := by
    have : ((-1 / 256 : ℚ) : ℝ) ≤ c20 := by rw [hc20]; exact_mod_cast k20lo
    push_cast at this; exact this
  have hc20hi : c20 ≤ -1 / 512 := by
    have : c20 ≤ ((-1 / 512 : ℚ) : ℝ) := by rw [hc20]; exact_mod_cast k20hi
    push_cast at this; exact this
  have hc21b : |c21| ≤ 1 / 2 ^ 63 := by
    have := TgammaSmall.abs_rat_le _ _ k21
    rw [← hc21] at this; push_cast at this; exact this
  obtain ⟨hc171, hc172⟩ := abs_le.mp hc17b
  obtain ⟨hc191, hc192⟩ := abs_le.mp hc19b
  obtain ⟨hc211, hc212⟩ := abs_le.mp hc21b
  -- `Z = 1/X` and `W = Z²`
  have hX0 : 0 < X := by linarith
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 1 / X := ⟨_, rfl⟩
  rw [← hZ] at hu huu hul
  have hZ0 : 0 < Z := by rw [hZ]; exact one_div_pos.mpr hX0
  have hZle : Z ≤ 1 / 4 := by
    rw [hZ, div_le_div_iff₀ hX0 (by norm_num)]
    linarith
  have hW : Z ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hZ0.le hZle 2
    linarith [(by norm_num : ((1 : ℝ) / 4) ^ 2 = 1 / 16)]
  have hW0 : 0 ≤ Z ^ 2 := sq_nonneg Z
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have hub : |value u.toBits| ≤ 1 / 15 := by
    rw [abs_le]; constructor <;> linarith [(by norm_num : (1 : ℝ) / 16 * (1 + 1 / 2 ^ 44) ≤ 1 / 15)]
  have hulb : |value ul.toBits| ≤ 1 / 16 / 2 ^ 42 := by
    have : Z ^ 2 / 2 ^ 42 ≤ 1 / 16 / 2 ^ 42 := div_le_div_of_nonneg_right hW (by norm_num)
    linarith
  obtain ⟨huu1, huu2⟩ := abs_le.mp huu
  -- the sum with `c16 + c17`
  have hPhb : |value Ph.toBits| ≤ 797 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨hs1f, hs2f, hse, hs2b⟩ := fastSum_spec Ph Pl (entry asymTable 16) (entry asymTable 17)
    hPhf hPlf h16f h17f
    (by rw [h16v, abs_of_pos (by linarith only [hc16lo] : (0 : ℝ) < c16),
          abs_of_pos (show (0 : ℝ) < value Ph.toBits by linarith)]; linarith)
    (by linarith [(by norm_num : (797 : ℝ) < 2 ^ 898)]) (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55)
    (by rw [h17v]; linarith) (by norm_num)
  rw [h16v, h17v] at hse
  -- the series
  have hu' : |value u.toBits| ≤ ((Ulo : ℚ) : ℝ) := by
    rw [show ((Ulo : ℚ) : ℝ) = 1 / 15 by rw [Ulo]; norm_num]; exact hub
  obtain ⟨hfl, hRm⟩ := evalF_approx loE Ulo u huf hu' loE_ok
  have hfle : |value (evalF loE u).toBits - evalR loE (value u.toBits)| ≤ 1 / 2 ^ 65 := by
    have h := hfl.2
    have : ((bnd loE Ulo).2 : ℝ) ≤ ((1 / 2 ^ 65 : ℚ) : ℝ) := by exact_mod_cast loE_err
    push_cast at this
    linarith
  have hRb : |evalR loE (value u.toBits)| ≤ 1 / 2 ^ 14 := by
    have : ((bnd loE Ulo).1 : ℝ) ≤ ((1 / 2 ^ 14 : ℚ) : ℝ) := by exact_mod_cast loE_mag
    push_cast at this
    linarith
  have hflb : |value (evalF loE u).toBits| ≤ 1 / 2 ^ 13 := by
    have := abs_sub_abs_le_abs_sub (value (evalF loE u).toBits) (evalR loE (value u.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 14 + 1 / 2 ^ 65 ≤ 1 / 2 ^ 13)]
  obtain ⟨ht1f, ht2f, htsum, ht2le, ht2b⟩ := fastTwoSum_spec (entry asymTable 20) (evalF loE u) h20f
    hfl.1 (by rw [h20v, abs_of_neg (by linarith only [hc20hi] : c20 < 0)]
              linarith [(by norm_num : (1 : ℝ) / 2 ^ 13 ≤ 1 / 512)])
    (by rw [h20v, abs_of_neg (by linarith only [hc20hi] : c20 < 0)]
        linarith [(by norm_num : (1 : ℝ) / 256 < 2 ^ 900)])
  rw [h20v] at htsum
  -- the code
  unfold BranchOK loBranch
  dsimp only
  rw [← lfl_eq u]
  generalize fastSum Ph Pl (entry asymTable 16) (entry asymTable 17) = s at hs1f hs2f hse hs2b ⊢
  obtain ⟨s1, s2⟩ := s
  dsimp only at hs1f hs2f hse hs2b ⊢
  generalize fastTwoSum (entry asymTable 20) (evalF loE u) = t at ht1f ht2f htsum ht2le ht2b ⊢
  obtain ⟨t1, t2⟩ := t
  dsimp only at ht1f ht2f htsum ht2le ht2b ⊢
  -- `s1` and `s2`
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  obtain ⟨hPl1, hPl2⟩ := abs_le.mp hPl
  have hs1b : |value s1.toBits| ≤ 800 := by
    obtain ⟨he1, he2⟩ := abs_le.mp hse
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2b
    rcases abs_cases (value s1.toBits) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at he1 he2 hl1 hl2 ⊢ <;>
      linarith only [he1, he2, hl1, hl2, hPh1, hPh2, hPl1, hPl2, hc16lo, hc16hi, hc171, hc172]
  have hs2 : |value s2.toBits| ≤ 3 / 4 / 2 ^ 14 := by
    have : |value s1.toBits| / 2 ^ 51 ≤ 800 / 2 ^ 51 := div_le_div_of_nonneg_right hs1b (by norm_num)
    linarith only [hs2b, this, (by norm_num : ((73 : ℝ) / 100 / 2 ^ 14 + 1 / 2 ^ 55) *
      (1 + 1 / 2 ^ 51) + 800 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 3 / 4 / 2 ^ 14)]
  have hse' : |value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c16 + c17))| ≤
      1 / 2 ^ 65 := by
    have : |value s1.toBits| / 2 ^ 52 ≤ 800 / 2 ^ 52 := div_le_div_of_nonneg_right hs1b (by norm_num)
    have h2 : (3 * (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55) + |value s1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤ (3 * (73 / 100 / 2 ^ 14 + 1 / 2 ^ 55) + 800 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith only [this]) (by norm_num)
    linarith only [hse, h2, (by norm_num : (3 * ((73 : ℝ) / 100 / 2 ^ 14 + 1 / 2 ^ 55) +
      800 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤ 1 / 2 ^ 65)]
  -- `t1`, `t2`, and `f2 = t2 + c21`
  have ht1b : |value t1.toBits| ≤ 1 / 200 := by
    have h1 := abs_add_le (value t1.toBits + value t2.toBits) (-value t2.toBits)
    rw [add_neg_cancel_right, abs_neg, htsum] at h1
    have h2 := abs_add_le c20 (value (evalF loE u).toBits)
    rw [abs_of_neg (by linarith only [hc20hi] : c20 < 0)] at h2
    linarith only [h1, h2, ht2le, hflb, hc20lo,
      (by norm_num : (1 : ℝ) / 256 + 1 / 2 ^ 13 + 1 / 2 ^ 13 ≤ 1 / 200)]
  have ht2 : |value t2.toBits| ≤ 1 / 200 / 2 ^ 52 + 1 / 2 ^ 1074 := by
    have : |value t1.toBits| / 2 ^ 52 ≤ 1 / 200 / 2 ^ 52 :=
      div_le_div_of_nonneg_right ht1b (by norm_num)
    linarith only [ht2b, this]
  have hf2 := fapprox_add (fapprox_self t2 ht2f) (fapprox_self _ h21f)
    (1 / 200 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 63)
    (by rw [h21v, add_zero, add_zero]; linarith only [abs_add_le (value t2.toBits) c21, ht2, hc21b])
    (by norm_num)
  rw [h21v] at hf2
  have hf2e : |value (t2 + entry asymTable 21).toBits - (value t2.toBits + c21)| ≤ 1 / 2 ^ 110 := by
    have := hf2.2
    linarith only [this, (by norm_num : (0 : ℝ) + 0 + (1 / 200 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 63) /
      2 ^ 53 ≤ 1 / 2 ^ 110)]
  have hf2b : |value (t2 + entry asymTable 21).toBits| ≤ 1 / 2 ^ 59 := by
    have := abs_sub_abs_le_abs_sub (value (t2 + entry asymTable 21).toBits) (value t2.toBits + c21)
    linarith only [this, hf2e, ht2, hc21b, abs_add_le (value t2.toBits) c21,
      (by norm_num : (1 : ℝ) / 200 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 63 + 1 / 2 ^ 110 ≤ 1 / 2 ^ 59)]
  -- `g = mulDD u ul t1 f2`
  have hu0 := abs_nonneg (value u.toBits)
  have hul0 := abs_nonneg (value ul.toBits)
  obtain ⟨hg1f, hg2f, hge, hg2b, hg1b⟩ := mulDD_spec hF u ul t1 (t2 + entry asymTable 21) huf hulf
    ht1f hf2.1 (1 / 200 * (1 / 15)) (1 / 200 * (1 / 16 / 2 ^ 42)) (1 / 2 ^ 59 * (1 / 15))
    (1 / 2 ^ 59 * (1 / 16 / 2 ^ 42))
    (mul_le_mul ht1b hub hu0 (by norm_num)) (mul_le_mul ht1b hulb hul0 (by norm_num))
    (mul_le_mul hf2b hub hu0 (by norm_num)) (mul_le_mul hf2b hulb hul0 (by norm_num))
    (by norm_num) (by norm_num)
  generalize mulDD u ul t1 (t2 + entry asymTable 21) = g at hg1f hg2f hge hg2b hg1b ⊢
  obtain ⟨g1, g2⟩ := g
  dsimp only at hg1f hg2f hge hg2b hg1b ⊢
  have hg2 : |value g2.toBits| ≤ 1 / 2 ^ 53 := by
    refine hg2b.trans ?_
    norm_num
  have hg1 : |value g1.toBits| ≤ 1 / 2999 := by
    refine hg1b.trans ?_
    norm_num
  have hge' : |value g1.toBits + value g2.toBits -
      (value u.toBits + value ul.toBits) * (value t1.toBits + value (t2 + entry asymTable 21).toBits)| ≤
      1 / 2 ^ 100 := by
    refine hge.trans ?_
    norm_num
  -- `v = fastSum c18 c19 g1 g2`
  obtain ⟨hv1f, hv2f, hve, hv2b⟩ := fastSum_spec (entry asymTable 18) (entry asymTable 19) g1 g2
    h18f h19f hg1f hg2f
    (by rw [h18v, abs_of_pos (by linarith only [hc18lo] : (0 : ℝ) < c18)]
        linarith only [hg1, hc18lo, (by norm_num : (1 : ℝ) / 2999 ≤ 1 / 13)])
    (by rw [h18v, abs_of_pos (by linarith only [hc18lo] : (0 : ℝ) < c18)]
        linarith only [hc18hi, (by norm_num : (1 : ℝ) / 11 < 2 ^ 898)])
    (1 / 2 ^ 57 + 1 / 2 ^ 53) (by rw [h19v]; linarith only [hc19b, hg2]) (by norm_num)
  rw [h18v, h19v] at hve
  generalize fastSum (entry asymTable 18) (entry asymTable 19) g1 g2 = v at hv1f hv2f hve hv2b ⊢
  obtain ⟨v1, v2⟩ := v
  dsimp only at hv1f hv2f hve hv2b ⊢
  have hv1b : |value v1.toBits| ≤ 1 / 10 := by
    obtain ⟨he1, he2⟩ := abs_le.mp hve
    obtain ⟨hl1, hl2⟩ := abs_le.mp hv2b
    obtain ⟨hg11, hg12⟩ := abs_le.mp hg1
    obtain ⟨hg21, hg22⟩ := abs_le.mp hg2
    rcases abs_cases (value v1.toBits) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at he1 he2 hl1 hl2 ⊢ <;>
      linarith only [he1, he2, hl1, hl2, hg11, hg12, hg21, hg22, hc18lo, hc18hi, hc191, hc192]
  have hv2 : |value v2.toBits| ≤ 1 / 2 ^ 50 := by
    have : |value v1.toBits| / 2 ^ 51 ≤ 1 / 10 / 2 ^ 51 := div_le_div_of_nonneg_right hv1b (by norm_num)
    linarith only [hv2b, this, (by norm_num : ((1 : ℝ) / 2 ^ 57 + 1 / 2 ^ 53) * (1 + 1 / 2 ^ 51) +
      1 / 10 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 1 / 2 ^ 50)]
  have hve' : |value v1.toBits + value v2.toBits - (c18 + c19 + (value g1.toBits + value g2.toBits))| ≤
      1 / 2 ^ 100 := by
    have : |value v1.toBits| / 2 ^ 52 ≤ 1 / 10 / 2 ^ 52 := div_le_div_of_nonneg_right hv1b (by norm_num)
    have h2 : (3 * (1 / 2 ^ 57 + 1 / 2 ^ 53) + |value v1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
        (3 * (1 / 2 ^ 57 + 1 / 2 ^ 53) + 1 / 10 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith only [this]) (by norm_num)
    linarith only [hve, h2, (by norm_num : (3 * ((1 : ℝ) / 2 ^ 57 + 1 / 2 ^ 53) + 1 / 10 / 2 ^ 52 +
      1 / 2 ^ 1074) / 2 ^ 53 ≤ 1 / 2 ^ 100)]
  refine ⟨hs1f, hs2f, hv1f, hv2f, ?_, ?_, ?_, hs2, hv1b, hv2⟩
  · -- the error of the series
    have hlip := eval_lip Ulo (by rw [Ulo]; norm_num) (value u.toBits) (Z ^ 2) hu'
      (by rw [show ((Ulo : ℚ) : ℝ) = 1 / 15 by rw [Ulo]; norm_num, abs_of_nonneg hW0]
          linarith only [hW, (by norm_num : (1 : ℝ) / 16 ≤ 1 / 15)]) Glo
    have hlq : ((lipQ Ulo Glo : ℚ) : ℝ) ≤ 1 / 1024 := by
      have : ((lipQ Ulo Glo : ℚ) : ℝ) ≤ ((1 / 1024 : ℚ) : ℝ) := by exact_mod_cast lip_lo
      push_cast at this; exact this
    have hlip' : |PolyBound.eval Glo (value u.toBits) - PolyBound.eval Glo (Z ^ 2)| ≤
        1 / 1024 * (1 / 16 / 2 ^ 44) := by
      refine hlip.trans (mul_le_mul hlq ?_ (abs_nonneg _) (by norm_num))
      rw [abs_le]; constructor <;> linarith only [hu1, hu2, hW]
    rw [eval_lo (value u.toBits)] at hlip'
    have hq16 : ((TgammaApprox.q asymTable 16 + TgammaApprox.q asymTable 17 : ℚ) : ℝ) = c16 + c17 := by
      rw [hc16, hc17, TgammaApprox.q, TgammaApprox.q, Rat.cast_add]
    have hq18 : ((TgammaApprox.q asymTable 18 + TgammaApprox.q asymTable 19 : ℚ) : ℝ) = c18 + c19 := by
      rw [hc18, hc19, TgammaApprox.q, TgammaApprox.q, Rat.cast_add]
    have hq20 : ((TgammaApprox.q asymTable 20 + TgammaApprox.q asymTable 21 : ℚ) : ℝ) = c20 + c21 := by
      rw [hc20, hc21, TgammaApprox.q, TgammaApprox.q, Rat.cast_add]
    have hst : TgammaApprox.stirLo X = (X - 1 / 2) * (Real.log X - 1) + (c16 + c17) +
        Z * ((c18 + c19) + Z ^ 2 * ((c20 + c21) + PolyBound.eval Glo (Z ^ 2))) := by
      rw [TgammaApprox.stirLo, stirLo_eval, hq16, hq18, hq20, hZ, one_div_pow]
    have hSX := hS X hX1 (by linarith only [hX2, (by norm_num : (23 : ℝ) / 2 + 1 / 2 ^ 44 ≤ 12)])
    rw [abs_sub_comm] at hSX
    rw [← hZ]
    -- the series part
    have hD : value v1.toBits + value v2.toBits -
        ((c18 + c19) + Z ^ 2 * ((c20 + c21) + PolyBound.eval Glo (Z ^ 2))) =
        (value v1.toBits + value v2.toBits - (c18 + c19 + (value g1.toBits + value g2.toBits))) +
        (value g1.toBits + value g2.toBits - (value u.toBits + value ul.toBits) *
          (value t1.toBits + value (t2 + entry asymTable 21).toBits)) +
        (value u.toBits + value ul.toBits) *
          ((value (t2 + entry asymTable 21).toBits - (value t2.toBits + c21)) +
            (value (evalF loE u).toBits - evalR loE (value u.toBits))) +
        (value u.toBits + value ul.toBits - Z ^ 2) * (c20 + c21 + evalR loE (value u.toBits)) +
        Z ^ 2 * (evalR loE (value u.toBits) - PolyBound.eval Glo (Z ^ 2)) := by
      linear_combination (value u.toBits + value ul.toBits) * htsum
    have huub : |value u.toBits + value ul.toBits| ≤ 1 / 15 := by
      rw [abs_le]; constructor <;>
        linarith only [huu1, huu2, hW, hW0, (by norm_num : (1 : ℝ) / 16 * (1 + 1 / 2 ^ 76) ≤ 1 / 15)]
    have f1 : |(value u.toBits + value ul.toBits) *
        ((value (t2 + entry asymTable 21).toBits - (value t2.toBits + c21)) +
          (value (evalF loE u).toBits - evalR loE (value u.toBits)))| ≤
        1 / 15 * (1 / 2 ^ 110 + 1 / 2 ^ 65) := by
      rw [abs_mul]
      refine mul_le_mul huub ?_ (abs_nonneg _) (by norm_num)
      linarith only [hf2e, hfle, abs_add_le (value (t2 + entry asymTable 21).toBits -
        (value t2.toBits + c21)) (value (evalF loE u).toBits - evalR loE (value u.toBits))]
    have f2 : |(value u.toBits + value ul.toBits - Z ^ 2) * (c20 + c21 + evalR loE (value u.toBits))| ≤
        1 / 16 / 2 ^ 76 * (1 / 200) := by
      have hW76 : Z ^ 2 / 2 ^ 76 ≤ 1 / 16 / 2 ^ 76 := div_le_div_of_nonneg_right hW (by norm_num)
      rw [abs_mul]
      refine mul_le_mul (by linarith only [huu, hW76]) ?_ (abs_nonneg _) (by norm_num)
      have h1 := abs_add_le (c20 + c21) (evalR loE (value u.toBits))
      have h2 := abs_add_le c20 c21
      rw [abs_of_neg (by linarith only [hc20hi] : c20 < 0)] at h2
      linarith only [h1, h2, hc20lo, hc21b, hRb,
        (by norm_num : (1 : ℝ) / 256 + 1 / 2 ^ 63 + 1 / 2 ^ 14 ≤ 1 / 200)]
    have f3 : |Z ^ 2 * (evalR loE (value u.toBits) - PolyBound.eval Glo (Z ^ 2))| ≤
        1 / 16 * (1 / 1024 * (1 / 16 / 2 ^ 44)) := by
      rw [abs_mul, abs_of_nonneg hW0]
      exact mul_le_mul hW hlip' (abs_nonneg _) (by norm_num)
    have hDb : |value v1.toBits + value v2.toBits -
        ((c18 + c19) + Z ^ 2 * ((c20 + c21) + PolyBound.eval Glo (Z ^ 2)))| ≤
        1 / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 15 * (1 / 2 ^ 110 + 1 / 2 ^ 65) + 1 / 16 / 2 ^ 76 * (1 / 200) +
          1 / 16 * (1 / 1024 * (1 / 16 / 2 ^ 44)) := by
      rw [hD]
      exact abs5 hve' hge' f1 f2 f3
    have hZD : |Z * (value v1.toBits + value v2.toBits -
        ((c18 + c19) + Z ^ 2 * ((c20 + c21) + PolyBound.eval Glo (Z ^ 2))))| ≤
        1 / 4 * (1 / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 15 * (1 / 2 ^ 110 + 1 / 2 ^ 65) +
          1 / 16 / 2 ^ 76 * (1 / 200) + 1 / 16 * (1 / 1024 * (1 / 16 / 2 ^ 44))) := by
      rw [abs_mul, abs_of_pos hZ0]
      exact mul_le_mul hZle hDb (abs_nonneg _) (by norm_num)
    have hsplit : value s1.toBits + value s2.toBits + Z * (value v1.toBits + value v2.toBits) -
        Real.log (Real.Gamma X) =
        (value s1.toBits + value s2.toBits - (value Ph.toBits + value Pl.toBits + (c16 + c17))) +
        (value Ph.toBits + value Pl.toBits - (X - 1 / 2) * (Real.log X - 1)) +
        Z * (value v1.toBits + value v2.toBits -
          ((c18 + c19) + Z ^ 2 * ((c20 + c21) + PolyBound.eval Glo (Z ^ 2)))) +
        (TgammaApprox.stirLo X - Real.log (Real.Gamma X)) := by
      linear_combination -hst
    rw [hsplit]
    refine (abs4 hse' hP hZD hSX).trans ?_
    norm_num
  · obtain ⟨he1, he2⟩ := abs_le.mp hse'
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2
    linarith only [he1, he2, hl1, hl2, hPh1, hPl1, hc16lo, hc171,
      (by norm_num : (1 : ℝ) / 2 ^ 65 ≤ 1 / 1000), (by norm_num : (3 : ℝ) / 4 / 2 ^ 14 ≤ 1 / 1000),
      (by norm_num : (73 : ℝ) / 100 / 2 ^ 14 ≤ 1 / 1000), (by norm_num : (1 : ℝ) / 2 ^ 55 ≤ 1 / 1000)]
  · obtain ⟨he1, he2⟩ := abs_le.mp hse'
    obtain ⟨hl1, hl2⟩ := abs_le.mp hs2
    linarith only [he1, he2, hl1, hl2, hPh2, hPl2, hc16hi, hc172,
      (by norm_num : (1 : ℝ) / 2 ^ 65 ≤ 1 / 1000), (by norm_num : (3 : ℝ) / 4 / 2 ^ 14 ≤ 1 / 1000),
      (by norm_num : (73 : ℝ) / 100 / 2 ^ 14 ≤ 1 / 1000), (by norm_num : (1 : ℝ) / 2 ^ 55 ≤ 1 / 1000)]

#print axioms asym_lo

end Verified.Examples.TgammaAsym5
