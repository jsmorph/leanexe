import Library.Numerics.Float64.Erfc.ErfcRound
import Library.Numerics.Float64.Erfc.Compiled
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The row indices of the asymptotic paths of `Erfc`.  `Erfc.asymptIndex yh` is the first `i` with
`yh ≤ threshold[i]`, and `Erfc.asymptAccIndex yh` likewise for the ten rows of `Tacc`
(`fast_index`, `acc_index`).  When `yh` lies within `u/x + 2^-1075` of `1/x`, a bound `T` on `yh`
gives a lower bound on `x`, and a lower bound on `yh` an upper bound on `x` (`dom_lo`, `dom_hi`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymIdx

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound PolyBound

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- The thresholds of `Erfc.asymptIndex` that the code compares. -/
def thrT : List UInt64 :=
  [0x3FBD500000000000, 0x3FC59DA6CA291BA6, 0x3FCBC00000000000, 0x3FD0C00000000000,
    0x3FD3800000000000]

/-- The thresholds of `Erfc.asymptAccIndex` that the code compares. -/
def thrA : List UInt64 :=
  [0x3FB4500000000000, 0x3FBE000000000000, 0x3FC3F00000000000, 0x3FC9500000000000,
    0x3FCF500000000000, 0x3FD3100000000000, 0x3FD7100000000000, 0x3FDBC00000000000,
    0x3FE0B00000000000]

theorem thr_vals (w : UInt64) (hw : Finite w) :
    ff (Float.ofBits w) ∧ fv (Float.ofBits w) = ratOfWord w := ofBits_ff w hw

theorem le_thr {yh : Float} (hy : ff yh) {w : UInt64} (hw : Finite w)
    (h : yh ≤ Float.ofBits w) : fv yh ≤ ratOfWord w := by
  obtain ⟨f, v⟩ := thr_vals w hw
  rw [← v]; exact (fle_iff _ _ hy f).mp h

theorem gt_thr {yh : Float} (hy : ff yh) {w : UInt64} (hw : Finite w)
    (h : ¬ yh ≤ Float.ofBits w) : (ratOfWord w : ℝ) < fv yh := by
  obtain ⟨f, v⟩ := thr_vals w hw
  rw [← v]; exact lt_of_not_ge (fun h' => h ((fle_iff _ _ hy f).mpr h'))

theorem thrT_fin : ∀ i < 5, Finite (thrT.getD i 0) := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

theorem thrA_fin : ∀ i < 9, Finite (thrA.getD i 0) := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

/-- The index of `Erfc.asymptIndex`. -/
theorem fast_index (yh : Float) (hy : ff yh) :
    ∃ i : ℕ, i < 6 ∧ Erfc.asymptIndex yh = UInt64.ofNat i ∧
      (i < 5 → fv yh ≤ ratOfWord (thrT.getD i 0)) ∧
      (0 < i → (ratOfWord (thrT.getD (i - 1) 0) : ℝ) < fv yh) := by
  have f := thrT_fin
  unfold Erfc.asymptIndex
  split_ifs with h0 h1 h2 h3 h4
  · exact ⟨0, by norm_num, rfl, fun _ => le_thr hy (f 0 (by norm_num)) h0, fun h => absurd h (by norm_num)⟩
  · exact ⟨1, by norm_num, rfl, fun _ => le_thr hy (f 1 (by norm_num)) h1,
      fun _ => gt_thr hy (f 0 (by norm_num)) h0⟩
  · exact ⟨2, by norm_num, rfl, fun _ => le_thr hy (f 2 (by norm_num)) h2,
      fun _ => gt_thr hy (f 1 (by norm_num)) h1⟩
  · exact ⟨3, by norm_num, rfl, fun _ => le_thr hy (f 3 (by norm_num)) h3,
      fun _ => gt_thr hy (f 2 (by norm_num)) h2⟩
  · exact ⟨4, by norm_num, rfl, fun _ => le_thr hy (f 4 (by norm_num)) h4,
      fun _ => gt_thr hy (f 3 (by norm_num)) h3⟩
  · exact ⟨5, by norm_num, rfl, fun h => absurd h (by norm_num),
      fun _ => gt_thr hy (f 4 (by norm_num)) h4⟩

/-- The index of `Erfc.asymptAccIndex`. -/
theorem acc_index (yh : Float) (hy : ff yh) :
    ∃ i : ℕ, i < 10 ∧ Erfc.asymptAccIndex yh = UInt64.ofNat i ∧
      (i < 9 → fv yh ≤ ratOfWord (thrA.getD i 0)) ∧
      (0 < i → (ratOfWord (thrA.getD (i - 1) 0) : ℝ) < fv yh) := by
  have f := thrA_fin
  unfold Erfc.asymptAccIndex
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 h8
  · exact ⟨0, by norm_num, rfl, fun _ => le_thr hy (f 0 (by norm_num)) h0, fun h => absurd h (by norm_num)⟩
  · exact ⟨1, by norm_num, rfl, fun _ => le_thr hy (f 1 (by norm_num)) h1,
      fun _ => gt_thr hy (f 0 (by norm_num)) h0⟩
  · exact ⟨2, by norm_num, rfl, fun _ => le_thr hy (f 2 (by norm_num)) h2,
      fun _ => gt_thr hy (f 1 (by norm_num)) h1⟩
  · exact ⟨3, by norm_num, rfl, fun _ => le_thr hy (f 3 (by norm_num)) h3,
      fun _ => gt_thr hy (f 2 (by norm_num)) h2⟩
  · exact ⟨4, by norm_num, rfl, fun _ => le_thr hy (f 4 (by norm_num)) h4,
      fun _ => gt_thr hy (f 3 (by norm_num)) h3⟩
  · exact ⟨5, by norm_num, rfl, fun _ => le_thr hy (f 5 (by norm_num)) h5,
      fun _ => gt_thr hy (f 4 (by norm_num)) h4⟩
  · exact ⟨6, by norm_num, rfl, fun _ => le_thr hy (f 6 (by norm_num)) h6,
      fun _ => gt_thr hy (f 5 (by norm_num)) h5⟩
  · exact ⟨7, by norm_num, rfl, fun _ => le_thr hy (f 7 (by norm_num)) h7,
      fun _ => gt_thr hy (f 6 (by norm_num)) h6⟩
  · exact ⟨8, by norm_num, rfl, fun _ => le_thr hy (f 8 (by norm_num)) h8,
      fun _ => gt_thr hy (f 7 (by norm_num)) h7⟩
  · exact ⟨9, by norm_num, rfl, fun h => absurd h (by norm_num),
      fun _ => gt_thr hy (f 8 (by norm_num)) h8⟩

/-- A bound `T` on `yh ≈ 1/x` gives a lower bound `L` on `x`. -/
theorem dom_lo {x yh : ℝ} (hx : 0 < x) (hy : |yh - 1 / x| ≤ u / x + η) (T L : ℚ)
    (hT : yh ≤ T) (hL : L * (T + 1 / 2 ^ 1075) ≤ 1 - 1 / 2 ^ 53) (hT0 : 0 ≤ T) : (L : ℝ) ≤ x := by
  have hL' : (L : ℝ) * (T + η) ≤ 1 - u := by qc hL
  have hT' : (0 : ℝ) < T + η := by
    have : (0 : ℝ) ≤ T := by qc hT0
    positivity
  have h1 : (1 - u) / x ≤ T + η := by
    have := (abs_le.mp hy).1
    have e : (1 - u) / x = 1 / x - u / x := by ring
    rw [e]; linarith
  rw [div_le_iff₀ hx] at h1
  have h3 : (L : ℝ) * (T + η) ≤ x * (T + η) := by linarith
  exact le_of_mul_le_mul_right h3 hT'

/-- A lower bound `T` on `yh ≈ 1/x` gives an upper bound `H` on `x`. -/
theorem dom_hi {x yh : ℝ} (hx : 0 < x) (hy : |yh - 1 / x| ≤ u / x + η) (T H : ℚ)
    (hT : (T : ℝ) < yh) (hH : 1 + 1 / 2 ^ 53 ≤ H * (T - 1 / 2 ^ 1075))
    (hT0 : 1 / 2 ^ 1075 < T) : x ≤ H := by
  have hH' : 1 + u ≤ (H : ℝ) * (T - η) := by qc hH
  have hT' : (0 : ℝ) < T - η := by
    have : (1 / 2 ^ 1075 : ℝ) < T := by qc hT0
    linarith
  have h1 : (T : ℝ) - η < (1 + u) / x := by
    have := (abs_le.mp hy).2
    have e : (1 + u) / x = 1 / x + u / x := by ring
    rw [e]; linarith
  rw [lt_div_iff₀ hx] at h1
  have h3 : x * (T - η) < (H : ℝ) * (T - η) := by linarith
  exact (lt_of_mul_lt_mul_right h3 hT'.le).le

#print axioms fast_index
#print axioms acc_index
#print axioms dom_lo
#print axioms dom_hi

end Library.Numerics.Float64.Erfc.ErfcAsymIdx
