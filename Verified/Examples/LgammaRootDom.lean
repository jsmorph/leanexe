import Verified.Examples.LgammaRootA0
import Verified.Examples.LgammaRootA1
import Verified.Examples.LgammaRootA2
import Verified.Examples.LgammaRootB0
import Verified.Examples.LgammaRootB1
import Verified.Examples.LgammaRootB2
import Verified.Examples.LgammaRootC
import Verified.Examples.LgammaRootD0
import Verified.Examples.LgammaRootD1
import Verified.Examples.LgammaRootD2
import Verified.Examples.LgammaRootE
import Verified.Examples.LgammaRootF

/-!
The domains of the 17 polynomials of `Lgamma.accurate` about the negative zeros: an argument of a
range where `|log |Γ x|| ≤ (1 + 2^-40) afh` lies in the interval `[A, B]` that the proof of
`RootFact` certifies with the point values `pA`, `pB`, and `pE` and the convexity of `log |Γ|`
(`GammaRoot.root_domain_inc`, `root_domain_dec`).  The lemmas repeat that part of each proof, so
that the floating-point evaluation (`LgammaRootSpec.root_spec`) can use the interval.
-/

namespace Verified.Examples.LgammaRootDom

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaReflect GammaRoot
  LgammaRootBase LgammaRootA LgammaRootB LgammaRootC LgammaRootD LgammaRootE LgammaRootF

set_option exponentiation.threshold 4096

/-- The domain of range 0: the argument lies in `[A, B]`. -/
theorem dom0 : ∀ x : ℝ, ((ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < x → x < ((-2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) →
    (-((2 : ℕ) : ℝ) - (((9959195835710406687 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((2 : ℕ) : ℝ) - (((7467555474278035609 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FB7400000000000 = (93 / 1024) := by decide +kernel
  rw [hw] at hxc
  have hl : ratOfWord 0xC004E147AE147AE1 = (-5877197513718497 / 2 ^ 51) := by decide +kernel
  rw [hl] at hx1
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pA0
  have fB := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pB0
  have fE := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pE0
  obtain ⟨hA, hB⟩ := root_domain_inc 2
    (lo := (-((2 : ℕ) : ℝ) - (((1373597886348001 / 2 ^ 51) : ℚ) : ℝ)))
    (hi := (-2 : ℝ))
    (A := (-((2 : ℕ) : ℝ) - (((9959195835710406687 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((2 : ℕ) : ℝ) - (((7467555474278035609 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((93 : ℝ) / 1024))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 1: the argument lies in `[A, B]`. -/
theorem dom1 : ∀ x : ℝ, ((-3 : ℚ) : ℝ) < x → x < ((ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) →
    (-((2 : ℕ) : ℝ) - (((7182594465582330641 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((2 : ℕ) : ℝ) - (((12946287394540346601 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FB1680000000000 = (557 / 2 ^ 13) := by decide +kernel
  rw [hw] at hxc
  have hh : ratOfWord 0xC004E147AE147AE1 = (-5877197513718497 / 2 ^ 51) := by decide +kernel
  rw [hh] at hx2
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pA1
  have fB := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pB1
  have fE := negPointOk_sound cfgP 2 _ _ _ _ _ _ 0 cfgP_pi pE1
  obtain ⟨hA, hB⟩ := root_domain_dec 2
    (lo := (-3 : ℝ))
    (hi := (-((2 : ℕ) : ℝ) - (((1373597886348001 / 2 ^ 51) : ℚ) : ℝ)))
    (A := (-((2 : ℕ) : ℝ) - (((7182594465582330641 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((2 : ℕ) : ℝ) - (((12946287394540346601 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((557 : ℝ) / 2 ^ 13))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 2: the argument lies in `[A, B]`. -/
theorem dom2 : ∀ x : ℝ, ((-7 / 2 : ℚ) : ℝ) < x → x < ((-3 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) →
    (-((3 : ℕ) : ℝ) - (((2832248124529656927 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((3 : ℕ) : ℝ) - (((309542334993196613 / 2 ^ 61) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FB2D40000000000 = (1205 / 2 ^ 14) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pA2
  have fB := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pB2
  have fE := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pE2
  obtain ⟨hA, hB⟩ := root_domain_inc 3
    (lo := (-((3 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-3 : ℝ))
    (A := (-((3 : ℕ) : ℝ) - (((2832248124529656927 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((3 : ℕ) : ℝ) - (((309542334993196613 / 2 ^ 61) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((1205 : ℝ) / 2 ^ 14))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 3: the argument lies in `[A, B]`. -/
theorem dom3 : ∀ x : ℝ, ((-4 : ℚ) : ℝ) < x → x < ((-7 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) →
    (-((3 : ℕ) : ℝ) - (((8837500021878364233 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((3 : ℕ) : ℝ) - (((8782586256590532433 / 2 ^ 63) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FAEF00000000000 = (495 / 2 ^ 13) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pA3
  have fB := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pB3
  have fE := negPointOk_sound cfgP 3 _ _ _ _ _ _ 0 cfgP_pi pE3
  obtain ⟨hA, hB⟩ := root_domain_dec 3
    (lo := (-4 : ℝ))
    (hi := (-((3 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((3 : ℕ) : ℝ) - (((8837500021878364233 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((3 : ℕ) : ℝ) - (((8782586256590532433 / 2 ^ 63) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((495 : ℝ) / 2 ^ 13))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 4: the argument lies in `[A, B]`. -/
theorem dom4 : ∀ x : ℝ, ((-9 / 2 : ℚ) : ℝ) < x → x < ((-4 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) →
    (-((4 : ℕ) : ℝ) - (((409563185869273943 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((4 : ℕ) : ℝ) - (((643190715599055509 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC0000000000000 = (1 / 8) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pA4
  have fB := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pB4
  have fE := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pE4
  obtain ⟨hA, hB⟩ := root_domain_inc 4
    (lo := (-((4 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-4 : ℝ))
    (A := (-((4 : ℕ) : ℝ) - (((409563185869273943 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((4 : ℕ) : ℝ) - (((643190715599055509 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((1 : ℝ) / 8))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 5: the argument lies in `[A, B]`. -/
theorem dom5 : ∀ x : ℝ, ((-5 : ℚ) : ℝ) < x → x < ((-9 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) →
    (-((4 : ℕ) : ℝ) - (((18300832368894797875 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((4 : ℕ) : ℝ) - (((2285000372254301329 / 2 ^ 61) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FB0800000000000 = (33 / 512) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pA5
  have fB := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pB5
  have fE := negPointOk_sound cfgP 4 _ _ _ _ _ _ 0 cfgP_pi pE5
  obtain ⟨hA, hB⟩ := root_domain_dec 4
    (lo := (-5 : ℝ))
    (hi := (-((4 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((4 : ℕ) : ℝ) - (((18300832368894797875 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((4 : ℕ) : ℝ) - (((2285000372254301329 / 2 ^ 61) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((33 : ℝ) / 512))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 6: the argument lies in `[A, B]`. -/
theorem dom6 : ∀ x : ℝ, ((-11 / 2 : ℚ) : ℝ) < x → x < ((-5 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) →
    (-((5 : ℕ) : ℝ) - (((40517011728281333 / 2 ^ 62) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((5 : ℕ) : ℝ) - (((141796690668325141 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FB1000000000000 = (17 / 256) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pA6
  have fB := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pB6
  have fE := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pE6
  obtain ⟨hA, hB⟩ := root_domain_inc 5
    (lo := (-((5 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-5 : ℝ))
    (A := (-((5 : ℕ) : ℝ) - (((40517011728281333 / 2 ^ 62) : ℚ) : ℝ)))
    (B := (-((5 : ℕ) : ℝ) - (((141796690668325141 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((17 : ℝ) / 256))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 7: the argument lies in `[A, B]`. -/
theorem dom7 : ∀ x : ℝ, ((-6 : ℚ) : ℝ) < x → x < ((-11 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) →
    (-((5 : ℕ) : ℝ) - (((18424352052644143055 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((5 : ℕ) : ℝ) - (((4604318681347612333 / 2 ^ 62) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC1300000000000 = (275 / 2048) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pA7
  have fB := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pB7
  have fE := negPointOk_sound cfgP 5 _ _ _ _ _ _ 0 cfgP_pi pE7
  obtain ⟨hA, hB⟩ := root_domain_dec 5
    (lo := (-6 : ℝ))
    (hi := (-((5 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((5 : ℕ) : ℝ) - (((18424352052644143055 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((5 : ℕ) : ℝ) - (((4604318681347612333 / 2 ^ 62) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((275 : ℝ) / 2048))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 8: the argument lies in `[A, B]`. -/
theorem dom8 : ∀ x : ℝ, ((-13 / 2 : ℚ) : ℝ) < x → x < ((-6 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) →
    (-((6 : ℕ) : ℝ) - (((916348977038845 / 2 ^ 59) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((6 : ℕ) : ℝ) - (((22268529823760227 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC1500000000000 = (277 / 2048) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pA8
  have fB := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pB8
  have fE := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pE8
  obtain ⟨hA, hB⟩ := root_domain_inc 6
    (lo := (-((6 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-6 : ℝ))
    (A := (-((6 : ℕ) : ℝ) - (((916348977038845 / 2 ^ 59) : ℚ) : ℝ)))
    (B := (-((6 : ℕ) : ℝ) - (((22268529823760227 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((277 : ℝ) / 2048))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 9: the argument lies in `[A, B]`. -/
theorem dom9 : ∀ x : ℝ, ((-7 : ℚ) : ℝ) < x → x < ((-13 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) →
    (-((6 : ℕ) : ℝ) - (((9221801716887439699 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((6 : ℕ) : ℝ) - (((2305309401735250467 / 2 ^ 61) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC3400000000000 = (77 / 512) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pA9
  have fB := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pB9
  have fE := negPointOk_sound cfgP 6 _ _ _ _ _ _ 0 cfgP_pi pE9
  obtain ⟨hA, hB⟩ := root_domain_dec 6
    (lo := (-7 : ℝ))
    (hi := (-((6 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((6 : ℕ) : ℝ) - (((9221801716887439699 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((6 : ℕ) : ℝ) - (((2305309401735250467 / 2 ^ 61) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((77 : ℝ) / 512))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 10: the argument lies in `[A, B]`. -/
theorem dom10 : ∀ x : ℝ, ((-15 / 2 : ℚ) : ℝ) < x → x < ((-7 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) →
    (-((7 : ℕ) : ℝ) - (((2099066151523559 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((7 : ℕ) : ℝ) - (((3188392528188741 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC1450000000000 = (4421 / 2 ^ 15) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pA10
  have fB := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pB10
  have fE := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pE10
  obtain ⟨hA, hB⟩ := root_domain_inc 7
    (lo := (-((7 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-7 : ℝ))
    (A := (-((7 : ℕ) : ℝ) - (((2099066151523559 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((7 : ℕ) : ℝ) - (((3188392528188741 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((4421 : ℝ) / 2 ^ 15))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 11: the argument lies in `[A, B]`. -/
theorem dom11 : ∀ x : ℝ, ((-8 : ℚ) : ℝ) < x → x < ((-15 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) →
    (-((7 : ℕ) : ℝ) - (((9223182216053851391 / 2 ^ 63) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((7 : ℕ) : ℝ) - (((18446192667662835873 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC76B0000000000 = (5995 / 2 ^ 15) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pA11
  have fB := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pB11
  have fE := negPointOk_sound cfgP 7 _ _ _ _ _ _ 0 cfgP_pi pE11
  obtain ⟨hA, hB⟩ := root_domain_dec 7
    (lo := (-8 : ℝ))
    (hi := (-((7 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((7 : ℕ) : ℝ) - (((9223182216053851391 / 2 ^ 63) : ℚ) : ℝ)))
    (B := (-((7 : ℕ) : ℝ) - (((18446192667662835873 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((5995 : ℝ) / 2 ^ 15))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 12: the argument lies in `[A, B]`. -/
theorem dom12 : ∀ x : ℝ, ((-17 / 2 : ℚ) : ℝ) < x → x < ((-8 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) →
    (-((8 : ℕ) : ℝ) - (((551352650560865 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((8 : ℕ) : ℝ) - (((47449542330831 / 2 ^ 61) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC76C0000000000 = (1499 / 2 ^ 13) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pA12
  have fB := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pB12
  have fE := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pE12
  obtain ⟨hA, hB⟩ := root_domain_inc 8
    (lo := (-((8 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-8 : ℝ))
    (A := (-((8 : ℕ) : ℝ) - (((551352650560865 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((8 : ℕ) : ℝ) - (((47449542330831 / 2 ^ 61) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((1499 : ℝ) / 2 ^ 13))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 13: the argument lies in `[A, B]`. -/
theorem dom13 : ∀ x : ℝ, ((-9 : ℚ) : ℝ) < x → x < ((-17 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) →
    (-((8 : ℕ) : ℝ) - (((18446702607666622313 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((8 : ℕ) : ℝ) - (((9223340876937742331 / 2 ^ 63) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC9900000000000 = (409 / 2048) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pA13
  have fB := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pB13
  have fE := negPointOk_sound cfgP 8 _ _ _ _ _ _ 0 cfgP_pi pE13
  obtain ⟨hA, hB⟩ := root_domain_dec 8
    (lo := (-9 : ℝ))
    (hi := (-((8 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((8 : ℕ) : ℝ) - (((18446702607666622313 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((8 : ℕ) : ℝ) - (((9223340876937742331 / 2 ^ 63) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((409 : ℝ) / 2048))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 14: the argument lies in `[A, B]`. -/
theorem dom14 : ∀ x : ℝ, ((-19 / 2 : ℚ) : ℝ) < x → x < ((-9 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) →
    (-((9 : ℕ) : ℝ) - (((62318885917251 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((9 : ℕ) : ℝ) - (((20732811579489 / 2 ^ 63) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC9900000000000 = (409 / 2048) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pA14
  have fB := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pB14
  have fE := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pE14
  obtain ⟨hA, hB⟩ := root_domain_inc 9
    (lo := (-((9 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-9 : ℝ))
    (A := (-((9 : ℕ) : ℝ) - (((62318885917251 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((9 : ℕ) : ℝ) - (((20732811579489 / 2 ^ 63) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((409 : ℝ) / 2048))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 15: the argument lies in `[A, B]`. -/
theorem dom15 : ∀ x : ℝ, ((-10 : ℚ) : ℝ) < x → x < ((-19 / 2 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) →
    (-((9 : ℕ) : ℝ) - (((18446739855653097299 / 2 ^ 64) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((9 : ℕ) : ℝ) - (((18446737947362945355 / 2 ^ 64) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC76B0000000000 = (5995 / 2 ^ 15) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pA15
  have fB := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pB15
  have fE := negPointOk_sound cfgP 9 _ _ _ _ _ _ 0 cfgP_pi pE15
  obtain ⟨hA, hB⟩ := root_domain_dec 9
    (lo := (-10 : ℝ))
    (hi := (-((9 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (A := (-((9 : ℕ) : ℝ) - (((18446739855653097299 / 2 ^ 64) : ℚ) : ℝ)))
    (B := (-((9 : ℕ) : ℝ) - (((18446737947362945355 / 2 ^ 64) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((5995 : ℝ) / 2 ^ 15))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) fA.1) (lt_of_le_of_lt fB.2 (by norm_num))
    (lt_of_le_of_lt fE.2 (by norm_num)) (by linarith) (by norm_num at hx2 ⊢; linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

/-- The domain of range 16: the argument lies in `[A, B]`. -/
theorem dom16 : ∀ x : ℝ, ((-21 / 2 : ℚ) : ℝ) < x → x < ((-10 : ℚ) : ℝ) →
    |lgamma x| ≤ (1 + 1 / 2 ^ 40) * ((ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) →
    (-((10 : ℕ) : ℝ) - (((1531584259107 / 2 ^ 62) : ℚ) : ℝ)) ≤ x ∧ x ≤ (-((10 : ℕ) : ℝ) - (((2109025958881 / 2 ^ 63) : ℚ) : ℝ)) := by
  intro x hx1 hx2 hxc
  have hw : ratOfWord 0x3FC76B0000000000 = (5995 / 2 ^ 15) := by decide +kernel
  rw [hw] at hxc
  push_cast at hx1 hx2 hxc
  have fA := negPointOk_sound cfgP 10 _ _ _ _ _ _ 0 cfgP_pi pA16
  have fB := negPointOk_sound cfgP 10 _ _ _ _ _ _ 0 cfgP_pi pB16
  have fE := negPointOk_sound cfgP 10 _ _ _ _ _ _ 0 cfgP_pi pE16
  obtain ⟨hA, hB⟩ := root_domain_inc 10
    (lo := (-((10 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ)))
    (hi := (-10 : ℝ))
    (A := (-((10 : ℕ) : ℝ) - (((1531584259107 / 2 ^ 62) : ℚ) : ℝ)))
    (B := (-((10 : ℕ) : ℝ) - (((2109025958881 / 2 ^ 63) : ℚ) : ℝ)))
    (c := ((1 + 1 / 2 ^ 40) * ((5995 : ℝ) / 2 ^ 15))) (x := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt fA.2 (by norm_num)) (lt_of_lt_of_le (by norm_num) fB.1)
    (lt_of_le_of_lt fE.2 (by norm_num)) (by norm_num at hx1 ⊢; linarith) (by linarith)
    (hxc.trans (le_of_eq (by norm_num)))
  exact ⟨hA, hB⟩

#print axioms dom0
#print axioms dom1
#print axioms dom2
#print axioms dom3
#print axioms dom4
#print axioms dom5
#print axioms dom6
#print axioms dom7
#print axioms dom8
#print axioms dom9
#print axioms dom10
#print axioms dom11
#print axioms dom12
#print axioms dom13
#print axioms dom14
#print axioms dom15
#print axioms dom16

end Verified.Examples.LgammaRootDom
