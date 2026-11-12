import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
The squared Mahalanobis distance and its computation by symmetric Gaussian elimination.
`mahalanobis S ν` is `ν ⬝ᵥ (S⁻¹ *ᵥ ν)`.  For a matrix `S` and a vector `ν` given as functions of
natural indices, `elimA S k` and `elimR S ν k` are the matrix and the right-hand side after `k`
steps of elimination, whose pivots are `elimA S m m m`, and `quad S ν k` is the sum of
`r_m² / p_m` over the first `k` steps.  `posDef_of_pivots` states that a symmetric `S` whose `d`
pivots are positive is positive definite on its leading `d × d` block, and `mahalanobis_eq` that
the squared Mahalanobis distance is then `quad S ν d`.
-/

namespace Demos.Gate.Model

open Matrix Finset

/-- The squared Mahalanobis distance `ν' S⁻¹ ν`. -/
noncomputable def mahalanobis {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (ν : Fin d → ℝ) : ℝ :=
  ν ⬝ᵥ (S⁻¹ *ᵥ ν)

/-- A symmetric function of two indices. -/
def Symm (A : ℕ → ℕ → ℝ) : Prop := ∀ i j, A i j = A j i

/-- The matrix after `k` steps of elimination: step `k` subtracts, from each entry `(i, j)` with
`i, j > k`, the entry `(i, k)` divided by the pivot times the entry `(j, k)`. -/
noncomputable def elimA (S : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => S
  | k + 1 => fun i j =>
    if k < i ∧ k < j then elimA S k i j - elimA S k i k / elimA S k k k * elimA S k j k
    else elimA S k i j

/-- The right-hand side after `k` steps of elimination. -/
noncomputable def elimR (S : ℕ → ℕ → ℝ) (ν : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => ν
  | k + 1 => fun i =>
    if k < i then elimR S ν k i - elimA S k i k / elimA S k k k * elimR S ν k k
    else elimR S ν k i

/-- The sum of `r_m² / p_m` over the first `k` steps. -/
noncomputable def quad (S : ℕ → ℕ → ℝ) (ν : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => quad S ν k + elimR S ν k k * elimR S ν k k / elimA S k k k

theorem symm_elimA {S : ℕ → ℕ → ℝ} (hS : Symm S) : ∀ k, Symm (elimA S k)
  | 0 => hS
  | k + 1 => fun i j => by
    have h := symm_elimA hS k
    simp only [elimA]
    by_cases hij : k < i ∧ k < j
    · rw [if_pos hij, if_pos ⟨hij.2, hij.1⟩, h i j]
      ring
    · rw [if_neg hij, if_neg (fun h' => hij ⟨h'.2, h'.1⟩), h i j]

theorem elimA_succ {S : ℕ → ℕ → ℝ} {k i j : ℕ} (hi : k < i) (hj : k < j) :
    elimA S (k + 1) i j = elimA S k i j - elimA S k i k / elimA S k k k * elimA S k j k := by
  simp only [elimA, if_pos (And.intro hi hj)]

theorem elimR_succ {S : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {k i : ℕ} (hi : k < i) :
    elimR S ν (k + 1) i = elimR S ν k i - elimA S k i k / elimA S k k k * elimR S ν k k := by
  simp only [elimR, if_pos hi]

/-! ### Solutions of `S x = ν` -/

/-- One step of elimination keeps the reduced equations of a solution. -/
theorem solve_step {S : ℕ → ℕ → ℝ} {ν x : ℕ → ℝ} {d k : ℕ} (hS : Symm S) (hk : k < d)
    (hp : elimA S k k k ≠ 0)
    (ha : ∀ i, k ≤ i → i < d → ∑ j ∈ Ico k d, elimA S k i j * x j = elimR S ν k i) :
    ∀ i, k + 1 ≤ i → i < d →
      ∑ j ∈ Ico (k + 1) d, elimA S (k + 1) i j * x j = elimR S ν (k + 1) i := by
  intro i hi1 hi2
  have hsym := symm_elimA hS k
  have hrow := ha i (by omega) hi2
  have hpiv := ha k le_rfl hk
  rw [sum_eq_sum_Ico_succ_bot hk] at hrow hpiv
  have hcol : ∑ j ∈ Ico (k + 1) d, elimA S k j k * x j =
      ∑ j ∈ Ico (k + 1) d, elimA S k k j * x j :=
    sum_congr rfl fun j _ => by rw [hsym j k]
  have e1 : ∑ j ∈ Ico (k + 1) d, elimA S (k + 1) i j * x j =
      ∑ j ∈ Ico (k + 1) d, elimA S k i j * x j -
        elimA S k i k / elimA S k k k * ∑ j ∈ Ico (k + 1) d, elimA S k j k * x j := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [elimA_succ (by omega) (mem_Ico.mp hj).1]
    ring
  rw [e1, hcol, elimR_succ (by omega)]
  have h1 : ∑ j ∈ Ico (k + 1) d, elimA S k i j * x j = elimR S ν k i - elimA S k i k * x k := by
    linarith
  have h2 : ∑ j ∈ Ico (k + 1) d, elimA S k k j * x j = elimR S ν k k - elimA S k k k * x k := by
    linarith
  rw [h1, h2]
  field_simp
  ring

/-- One step of elimination moves `r_k² / p_k` from the remaining sum to `quad`. -/
theorem dot_step {S : ℕ → ℕ → ℝ} {ν x : ℕ → ℝ} {d k : ℕ} (hS : Symm S) (hk : k < d)
    (hp : elimA S k k k ≠ 0)
    (ha : ∀ i, k ≤ i → i < d → ∑ j ∈ Ico k d, elimA S k i j * x j = elimR S ν k i) :
    quad S ν k + ∑ j ∈ Ico k d, elimR S ν k j * x j =
      quad S ν (k + 1) + ∑ j ∈ Ico (k + 1) d, elimR S ν (k + 1) j * x j := by
  have hsym := symm_elimA hS k
  have hpiv := ha k le_rfl hk
  rw [sum_eq_sum_Ico_succ_bot hk] at hpiv
  rw [sum_eq_sum_Ico_succ_bot hk]
  have e1 : ∑ j ∈ Ico (k + 1) d, elimR S ν (k + 1) j * x j =
      ∑ j ∈ Ico (k + 1) d, elimR S ν k j * x j -
        elimR S ν k k / elimA S k k k * ∑ j ∈ Ico (k + 1) d, elimA S k k j * x j := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [elimR_succ (mem_Ico.mp hj).1, hsym j k]
    ring
  rw [e1]
  have h2 : ∑ j ∈ Ico (k + 1) d, elimA S k k j * x j = elimR S ν k k - elimA S k k k * x k := by
    linarith
  rw [h2]
  simp only [quad]
  field_simp
  ring

/-- For a solution of `S x = ν` on the first `d` indices and nonzero pivots, `Σ ν_i x_i` is
`quad S ν d`. -/
theorem dot_eq_quad {S : ℕ → ℕ → ℝ} {ν x : ℕ → ℝ} {d : ℕ} (hS : Symm S)
    (hp : ∀ m < d, elimA S m m m ≠ 0)
    (hx : ∀ i < d, ∑ j ∈ range d, S i j * x j = ν i) :
    ∑ i ∈ range d, ν i * x i = quad S ν d := by
  have key : ∀ k ≤ d, (∀ i, k ≤ i → i < d → ∑ j ∈ Ico k d, elimA S k i j * x j = elimR S ν k i) ∧
      ∑ i ∈ range d, ν i * x i = quad S ν k + ∑ j ∈ Ico k d, elimR S ν k j * x j := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i _ hi => ?_, ?_⟩
      · rw [← range_eq_Ico]
        exact hx i hi
      · rw [← range_eq_Ico]
        simp [quad, elimR]
    | succ k ih =>
      intro hk
      obtain ⟨ha, hb⟩ := ih (by omega)
      exact ⟨solve_step hS (by omega) (hp k (by omega)) ha,
        hb.trans (dot_step hS (by omega) (hp k (by omega)) ha)⟩
  have := (key d le_rfl).2
  simpa using this

/-! ### The quadratic form -/

/-- `y_m` plus the multipliers of step `m` times the later entries of `y`. -/
noncomputable def lead (S : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (d m : ℕ) : ℝ :=
  y m + ∑ j ∈ Ico (m + 1) d, elimA S m j m / elimA S m m m * y j

/-- The quadratic form of `A` on the indices from `k` to `d - 1`. -/
noncomputable def qform (A : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (k d : ℕ) : ℝ :=
  ∑ i ∈ Ico k d, ∑ j ∈ Ico k d, y i * A i j * y j

theorem qform_step {S : ℕ → ℕ → ℝ} {y : ℕ → ℝ} {d k : ℕ} (hS : Symm S) (hk : k < d)
    (hp : elimA S k k k ≠ 0) :
    qform (elimA S k) y k d =
      elimA S k k k * lead S y d k ^ 2 + qform (elimA S (k + 1)) y (k + 1) d := by
  have hsym := symm_elimA hS k
  set p := elimA S k k k
  set L := ∑ j ∈ Ico (k + 1) d, elimA S k j k * y j
  have hL : ∑ i ∈ Ico (k + 1) d, y i * elimA S k i k = L :=
    sum_congr rfl fun i _ => by ring
  have hL' : ∑ j ∈ Ico (k + 1) d, y k * elimA S k k j * y j = y k * L := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [hsym k j]; ring
  have hrest : qform (elimA S (k + 1)) y (k + 1) d =
      ∑ i ∈ Ico (k + 1) d, ∑ j ∈ Ico (k + 1) d, y i * elimA S k i j * y j - L * L / p := by
    unfold qform
    have : L * L / p = ∑ i ∈ Ico (k + 1) d, ∑ j ∈ Ico (k + 1) d,
        y i * (elimA S k i k / p * elimA S k j k) * y j := by
      rw [← hL]
      simp only [sum_mul, mul_sum, div_eq_mul_inv]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [elimA_succ (mem_Ico.mp hi).1 (mem_Ico.mp hj).1]
    ring
  have hlead : lead S y d k = y k + L / p := by
    unfold lead
    rw [div_eq_mul_inv L, sum_mul]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  unfold qform
  rw [sum_eq_sum_Ico_succ_bot hk, sum_eq_sum_Ico_succ_bot hk, hL']
  have hcol : ∑ i ∈ Ico (k + 1) d, ∑ j ∈ Ico k d, y i * elimA S k i j * y j =
      L * y k + ∑ i ∈ Ico (k + 1) d, ∑ j ∈ Ico (k + 1) d, y i * elimA S k i j * y j := by
    rw [← hL, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_Ico_succ_bot hk]
  rw [hcol, hlead]
  unfold qform at hrest
  rw [hrest]
  field_simp
  ring

theorem qform_eq {S : ℕ → ℕ → ℝ} {y : ℕ → ℝ} {d : ℕ} (hS : Symm S)
    (hp : ∀ m < d, elimA S m m m ≠ 0) :
    qform S y 0 d = ∑ m ∈ range d, elimA S m m m * lead S y d m ^ 2 := by
  have key : ∀ k ≤ d, qform S y 0 d =
      ∑ m ∈ range k, elimA S m m m * lead S y d m ^ 2 + qform (elimA S k) y k d := by
    intro k
    induction k with
    | zero => intro _; simp [elimA]
    | succ k ih =>
      intro hk
      rw [ih (by omega), qform_step hS (by omega) (hp k (by omega)), sum_range_succ]
      ring
  rw [key d le_rfl]
  simp [qform]

/-- The quadratic form is positive at every `y` that is not zero on the first `d` indices, when
the pivots are positive. -/
theorem qform_pos {S : ℕ → ℕ → ℝ} {y : ℕ → ℝ} {d : ℕ} (hS : Symm S)
    (hp : ∀ m < d, 0 < elimA S m m m) (hy : ∃ i < d, y i ≠ 0) : 0 < qform S y 0 d := by
  rw [qform_eq hS fun m hm => (hp m hm).ne']
  classical
  set T := (range d).filter fun i => y i ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨i, hi, hyi⟩ := hy
    exact ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hyi⟩⟩
  set m := T.max' hT
  have hm : m ∈ T := T.max'_mem hT
  have hmd : m < d := mem_range.mp (mem_filter.mp hm).1
  have hym : y m ≠ 0 := (mem_filter.mp hm).2
  have hzero : ∀ j, m < j → j < d → y j = 0 := by
    intro j hj1 hj2
    by_contra h
    have := T.le_max' j (mem_filter.mpr ⟨mem_range.mpr hj2, h⟩)
    omega
  have hlead : lead S y d m = y m := by
    unfold lead
    rw [sum_eq_zero fun j hj => by
      rw [hzero j (by have := (mem_Ico.mp hj).1; omega) (mem_Ico.mp hj).2, mul_zero], add_zero]
  apply sum_pos' (fun i hi => mul_nonneg (hp i (mem_range.mp hi)).le (sq_nonneg _))
  refine ⟨m, mem_range.mpr hmd, ?_⟩
  rw [hlead]
  exact mul_pos (hp m hmd) (by positivity)

/-! ### Matrices -/

/-- The `d × d` matrix of the first `d` indices of `S`. -/
def toMatrix (d : ℕ) (S : ℕ → ℕ → ℝ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => S i j

/-- A symmetric `S` whose first `d` pivots are positive is positive definite on the first `d`
indices. -/
theorem posDef_of_pivots {S : ℕ → ℕ → ℝ} {d : ℕ} (hS : Symm S)
    (hp : ∀ m < d, 0 < elimA S m m m) : (toMatrix d S).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [toMatrix, conjTranspose_apply, hS j i]
  · let y : ℕ → ℝ := fun n => if h : n < d then x ⟨n, h⟩ else 0
    have hy : ∃ i < d, y i ≠ 0 := by
      by_contra h
      have h' : ∀ i < d, y i = 0 := fun i hi => by
        by_contra hne
        exact h ⟨i, hi, hne⟩
      exact hx (funext fun i => by simpa [y, i.isLt] using h' i i.isLt)
    have hq := qform_pos hS hp hy
    have heq : star x ⬝ᵥ (toMatrix d S *ᵥ x) = qform S y 0 d := by
      unfold qform
      rw [← range_eq_Ico, sum_range]
      simp only [dotProduct, mulVec, toMatrix, of_apply, star_trivial]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_range, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp [y]
      ring
    rw [heq]
    exact hq

/-- For a symmetric `S` whose first `d` pivots are positive, the squared Mahalanobis distance of
the first `d` entries of `ν` under the first `d × d` block of `S` is `quad S ν d`. -/
theorem mahalanobis_eq {S : ℕ → ℕ → ℝ} {d : ℕ} (hS : Symm S) (hp : ∀ m < d, 0 < elimA S m m m)
    (ν : ℕ → ℝ) : mahalanobis (toMatrix d S) (fun i : Fin d => ν i) = quad S ν d := by
  have hpd := posDef_of_pivots hS hp
  have hu : IsUnit (toMatrix d S).det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  set x := (toMatrix d S)⁻¹ *ᵥ (fun i : Fin d => ν i)
  have hsol : toMatrix d S *ᵥ x = fun i : Fin d => ν i := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  let xN : ℕ → ℝ := fun n => if h : n < d then x ⟨n, h⟩ else 0
  have hx : ∀ i < d, ∑ j ∈ range d, S i j * xN j = ν i := by
    intro i hi
    have := congrFun hsol ⟨i, hi⟩
    simp only [mulVec, dotProduct, toMatrix, of_apply] at this
    rw [sum_range]
    simpa [xN] using this
  have hq := dot_eq_quad hS (fun m hm => (hp m hm).ne') hx
  rw [← hq]
  unfold mahalanobis
  rw [sum_range]
  simp [dotProduct, xN, x]

#print axioms posDef_of_pivots
#print axioms mahalanobis_eq

end Demos.Gate.Model
