import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

namespace Project.Beck.Rounding

open Finset

variable {Job Category : Type*} [DecidableEq Job] [Fintype Category]

def protectedCategories (members : Category → Finset Job) (live : Finset Job) (t : ℕ) : Finset Category :=
  univ.filter fun category => t < (live.filter fun job => job ∈ members category).card

theorem protected_card_lt (members : Category → Finset Job) (live : Finset Job) (t : ℕ)
    (overlap : ∀ job, (univ.filter fun category => job ∈ members category).card ≤ t)
    (nonempty : live.Nonempty) :
    (protectedCategories members live t).card < live.card := by
  by_cases hp : (protectedCategories members live t).Nonempty
  · have h := Finset.card_nsmul_lt_card_nsmul_of_lt_of_le
      (R := ℕ) (fun category job => job ∈ members category)
      (s := protectedCategories members live t) (t := live) (m := t) (n := t) hp
      (fun category hc => (Finset.mem_filter.mp hc).2)
      (fun job _ => (Finset.card_le_card (by
        intro category hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hc).2⟩)).trans (overlap job))
    simp only [nsmul_eq_mul] at h
    exact Nat.lt_of_mul_lt_mul_right h
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp, Finset.card_empty]
    exact nonempty.card_pos

def incidence (members : Category → Finset Job) (live : Finset Job) (t : ℕ) :
    Matrix (protectedCategories members live t) live ℚ :=
  fun category job => if job.val ∈ members category.val then 1 else 0

theorem preserving_direction_exists (members : Category → Finset Job)
    (live : Finset Job) (t : ℕ)
    (overlap : ∀ job, (univ.filter fun category => job ∈ members category).card ≤ t)
    (nonempty : live.Nonempty) :
    ∃ d : live → ℚ, d ≠ 0 ∧ (incidence members live t).mulVec d = 0 := by
  have dimensions : Module.finrank ℚ ((protectedCategories members live t) → ℚ) <
      Module.finrank ℚ (live → ℚ) := by
    simpa using protected_card_lt members live t overlap nonempty
  obtain ⟨d, hd, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := (incidence members live t).mulVecLin) dimensions)
  exact ⟨d, hn, hd⟩

theorem changed_coordinate_lt_two (x y : ℚ) (hx : -1 < x ∧ x < 1)
    (hy : y = -1 ∨ y = 1) : |y - x| < 2 := by
  rcases hy with rfl | rfl <;> rw [abs_lt] <;> constructor <;> linarith

omit [DecidableEq Job] in
theorem released_category_bound (category live : Finset Job) (t : ℕ)
    (positive : 0 < t) (subset : live ⊆ category) (small : live.card ≤ t)
    (x : Job → ℚ) (y : Job → ℤ)
    (interior : ∀ job ∈ live, -1 < x job ∧ x job < 1)
    (assigned : ∀ job ∈ category, y job = -1 ∨ y job = 1)
    (fixed : ∀ job ∈ category, job ∉ live → (y job : ℚ) = x job)
    (preserved : ∑ job ∈ category, x job = 0) :
    |∑ job ∈ category, y job| ≤ 2 * (t : ℤ) - 1 := by
  have difference : (∑ job ∈ category, (y job : ℚ)) =
      ∑ job ∈ live, ((y job : ℚ) - x job) := by
    have h := Finset.sum_subset subset (f := fun job => (y job : ℚ) - x job)
      (by intro job hj hn; simp [fixed job hj hn])
    calc
      _ = ∑ job ∈ category, ((y job : ℚ) - x job) := by
        rw [Finset.sum_sub_distrib, preserved, sub_zero]
      _ = _ := h.symm
  have strict : |∑ job ∈ category, (y job : ℚ)| < 2 * (t : ℚ) := by
    rw [difference]
    by_cases nonempty : live.Nonempty
    · calc
        _ ≤ ∑ job ∈ live, |(y job : ℚ) - x job| := Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _job ∈ live, (2 : ℚ) :=
          Finset.sum_lt_sum_of_nonempty nonempty (fun job hj =>
            changed_coordinate_lt_two (x job) (y job) (interior job hj)
              (by rcases assigned job (subset hj) with h | h <;> simp [h]))
        _ = 2 * (live.card : ℚ) := by simp [mul_comm]
        _ ≤ 2 * (t : ℚ) := by exact_mod_cast Nat.mul_le_mul_left 2 small
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
      simp only [Finset.sum_empty, abs_zero]
      positivity
  have integer : |∑ job ∈ category, y job| < 2 * (t : ℤ) := by
    exact_mod_cast strict
  omega

def boundaryTime (x d : ℚ) : ℚ := if d < 0 then (-1 - x) / d else (1 - x) / d

theorem boundaryTime_positive (x d : ℚ) (interior : -1 < x ∧ x < 1) (nonzero : d ≠ 0) :
    0 < boundaryTime x d := by
  unfold boundaryTime
  split_ifs with negative
  · exact div_pos_of_neg_of_neg (by linarith [interior.1]) negative
  · exact div_pos (by linarith [interior.2]) (by rcases lt_or_gt_of_ne nonzero with h | h <;> linarith)

theorem before_boundary (x d step : ℚ) (interior : -1 < x ∧ x < 1)
    (positive : 0 < step) (limit : d ≠ 0 → step ≤ boundaryTime x d) :
    -1 ≤ x + step * d ∧ x + step * d ≤ 1 := by
  rcases lt_trichotomy d 0 with negative | zero | positiveDirection
  · have bound := limit (ne_of_lt negative)
    simp only [boundaryTime, negative, ↓reduceIte] at bound
    have lower := (le_div_iff_of_neg negative).mp bound
    have upper := mul_nonpos_of_nonneg_of_nonpos (le_of_lt positive) (le_of_lt negative)
    constructor <;> linarith [interior.2]
  · subst d
    simpa using And.intro (le_of_lt interior.1) (le_of_lt interior.2)
  · have bound := limit (ne_of_gt positiveDirection)
    simp only [boundaryTime, not_lt_of_gt positiveDirection, ↓reduceIte] at bound
    have upper := (le_div_iff₀ positiveDirection).mp bound
    have lower := mul_nonneg (le_of_lt positive) (le_of_lt positiveDirection)
    constructor <;> linarith [interior.1]

theorem at_boundary (x d : ℚ) (nonzero : d ≠ 0) :
    x + boundaryTime x d * d = -1 ∨ x + boundaryTime x d * d = 1 := by
  unfold boundaryTime
  split_ifs
  · left
    rw [div_mul_cancel₀ _ nonzero]
    ring
  · right
    rw [div_mul_cancel₀ _ nonzero]
    ring

omit [DecidableEq Job] in
theorem boundary_progress (live : Finset Job) (x d : Job → ℚ)
    (interior : ∀ job ∈ live, -1 < x job ∧ x job < 1)
    (nonzero : ∃ job ∈ live, d job ≠ 0) :
    ∃ step : ℚ, 0 < step ∧
      (∀ job ∈ live, -1 ≤ x job + step * d job ∧ x job + step * d job ≤ 1) ∧
      ∃ job ∈ live, x job + step * d job = -1 ∨ x job + step * d job = 1 := by
  let moving := live.filter fun job => d job ≠ 0
  have nonempty : moving.Nonempty := by
    obtain ⟨job, member, nonzero⟩ := nonzero
    exact ⟨job, Finset.mem_filter.mpr ⟨member, nonzero⟩⟩
  obtain ⟨first, member, least⟩ := moving.exists_min_image
    (fun job => boundaryTime (x job) (d job)) nonempty
  have firstLive := (Finset.mem_filter.mp member).1
  have firstNonzero := (Finset.mem_filter.mp member).2
  have positive := boundaryTime_positive (x first) (d first) (interior first firstLive) firstNonzero
  refine ⟨boundaryTime (x first) (d first), positive, ?_, first, firstLive,
    at_boundary (x first) (d first) firstNonzero⟩
  intro job hj
  exact before_boundary (x job) (d job) _ (interior job hj) positive
    (fun hn => least job (Finset.mem_filter.mpr ⟨hj, hn⟩))

end Project.Beck.Rounding
