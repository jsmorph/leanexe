import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Project.ProofKit.CompensatedSumBounds

private noncomputable abbrev u : ℝ := 1/2^53

theorem correction_bounds (s p y d l h a c : ℝ)
    (hs : 0 < s ∧ s ≤ 2) (hp : |p| ≤ s/200)
    (hy : 0 < y ∧ y ≤ 1-u)
    (hey : |y-(s+p)| ≤ u*|s+p|)
    (hd : |d-(s-y)| ≤ u*|s-y|)
    (hl : |l-(d+p)| ≤ u*|d+p|)
    (hh : 1 ≤ h ∧ h ≤ 1+2*y ∧ |h-(1+y)| ≤ u)
    (ha : |a-(1-h+y)| ≤ u*|1-h+y|)
    (hc : |c-(a+l)| ≤ u*|a+l|) :
    1 ≤ h+c ∧ h+c ≤ 2+u ∧
    |h+c-(1+s+p)| ≤ 3/1000000000000000000 := by
  have hu : 0 < u := by norm_num [u]
  have hP := abs_le.mp hp
  have hT : 0 < s+p ∧ s+p ≤ (201/200)*s := by constructor <;> linarith
  rw [abs_of_pos hT.1] at hey
  have hYe : |y-(s+p)| ≤ (101/100)*u*s := by
    calc
      _ ≤ u*(s+p) := hey
      _ ≤ _ := by dsimp [u]; linarith
  have hYabs := abs_le.mp hYe
  have hY : y ≤ (101/100)*s := by dsimp [u] at hYabs ⊢; linarith
  have hT1 : s+p ≤ 1 := by
    have h := (abs_le.mp hey).1
    dsimp [u] at h hy
    linarith
  have hDm : |s-y| ≤ s/100 := by
    apply abs_le.mpr
    dsimp [u] at hYabs
    constructor <;> linarith
  have hDe : |d-(s-y)| ≤ u*s/100 :=
    hd.trans (by nlinarith only [hDm, hu])
  have hDabs := abs_le.mp hDe
  have hDP : |d+p| ≤ 2*u*s := by
    apply abs_le.mpr
    dsimp [u] at hDabs hYabs ⊢
    constructor <;> linarith
  have hLe : |l-(d+p)| ≤ 2*u^2*s := by
    apply hl.trans
    nlinarith only [hDP, hu]
  have hLabs := abs_le.mp hLe
  have hL : |l| ≤ 3*u*s := by
    have hDPabs := abs_le.mp hDP
    apply abs_le.mpr
    dsimp [u] at hLabs hDPabs ⊢
    constructor <;> linarith
  have hAm : |1-h+y| ≤ u := by
    have hbound := hh.2.2
    rw [show 1-h+y = -(h-(1+y)) by ring, abs_neg]
    exact hbound
  have hAmY : |1-h+y| ≤ y := by
    apply abs_le.mpr
    constructor <;> linarith [hh.1, hh.2.1]
  have hAe : |a-(1-h+y)| ≤ u^2 := ha.trans (by nlinarith only [hAm, hu])
  have hAeS : |a-(1-h+y)| ≤ (101/100)*u*s := by
    apply ha.trans
    nlinarith only [hAmY, hY, hu]
  have hAabs := abs_le.mp hAe
  have hA : |a| ≤ 2*u := by
    have h := abs_le.mp hAm
    apply abs_le.mpr
    dsimp [u] at hAabs h ⊢
    constructor <;> linarith
  have hAS : |a| ≤ 2*s := by
    have h := abs_le.mp hAmY
    have he := abs_le.mp hAeS
    apply abs_le.mpr
    dsimp [u] at he ⊢
    constructor <;> linarith
  have hCm : |a+l| ≤ 8*u := by
    apply (abs_add_le _ _).trans
    have hL' : |l| ≤ 6*u := hL.trans (by nlinarith only [hs.2, hu])
    linarith
  have hCmS : |a+l| ≤ 3*s := by
    apply (abs_add_le _ _).trans
    dsimp [u] at hL
    linarith
  have hCe : |c-(a+l)| ≤ 8*u^2 := hc.trans (by nlinarith only [hCm, hu])
  have hCeS : |c-(a+l)| ≤ 3*u*s := hc.trans (by nlinarith only [hCmS, hu])
  have hTotal : |h+c-(1+s+p)| ≤
      |d-(s-y)|+|l-(d+p)|+|a-(1-h+y)|+|c-(a+l)| := by
    calc
      _ = |((d-(s-y))+(l-(d+p)))+(a-(1-h+y))+(c-(a+l))| := by congr 1; ring
      _ ≤ |(d-(s-y))+(l-(d+p))|+|a-(1-h+y)|+|c-(a+l)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith [abs_add_le (d-(s-y)) (l-(d+p))]
  have hSmall : |h+c-(1+s+p)| ≤ 3/1000000000000000000 := by
    have h1 : u*s/100 ≤ 2*u/100 := by nlinarith only [hs.2, hu]
    have h2 : 2*u^2*s ≤ 4*u^2 := by nlinarith only [hs.2, sq_nonneg u]
    dsimp [u] at hTotal hDe hLe hAe hCe h1 h2
    linarith
  have hRelative : |h+c-(1+s+p)| ≤ s/100 := by
    dsimp [u] at hTotal hDe hLe hAeS hCeS
    linarith
  have hR := abs_le.mp hRelative
  have hB := abs_le.mp hSmall
  refine ⟨by linarith, ?_, hSmall⟩
  dsimp [u]
  linarith

#print axioms correction_bounds
end Project.ProofKit.CompensatedSumBounds
