import Project.Beck.Rounding

namespace Project.Beck.GenericLoop

open Finset

variable {Job Category State : Type*} [Fintype Job] [DecidableEq Job]

def live (coordinate : State → Job → ℚ) (state : State) : Finset Job :=
  univ.filter fun job => |coordinate state job| < 1

structure System (Job Category State : Type*) [Fintype Job] [DecidableEq Job] where
  coordinate : State → Job → ℚ
  members : Category → Finset Job
  overlap : ℕ
  valid : State → Prop
  step : State → State
  cube : ∀ state, valid state → ∀ job, |coordinate state job| ≤ 1
  step_valid : ∀ state, valid state → (live coordinate state).Nonempty → valid (step state)
  step_fixed : ∀ state, valid state → ∀ job, job ∉ live coordinate state →
    coordinate (step state) job = coordinate state job
  step_progress : ∀ state, valid state → (live coordinate state).Nonempty →
    ∃ job ∈ live coordinate state, |coordinate (step state) job| = 1
  step_preserves : ∀ state, valid state → ∀ category,
    overlap < ((live coordinate state).filter fun job => job ∈ members category).card →
    ∑ job ∈ members category, coordinate (step state) job =
      ∑ job ∈ members category, coordinate state job

variable (system : System Job Category State)

def rounds : ℕ → State → State
  | 0, state => state
  | fuel + 1, state =>
    if (live system.coordinate state).Nonempty then rounds fuel (system.step state) else state

theorem live_step_subset (state : State) (valid : system.valid state) :
    live system.coordinate (system.step state) ⊆ live system.coordinate state := by
  intro job member
  by_contra outside
  have fixed := system.step_fixed state valid job outside
  simp only [live, mem_filter, mem_univ, true_and] at member outside ⊢
  exact outside (fixed ▸ member)

theorem live_step_lt (state : State) (valid : system.valid state)
    (nonempty : (live system.coordinate state).Nonempty) :
    (live system.coordinate (system.step state)).card < (live system.coordinate state).card := by
  obtain ⟨job, member, boundary⟩ := system.step_progress state valid nonempty
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨live_step_subset system state valid, ?_⟩
  intro same
  have next : job ∈ live system.coordinate (system.step state) := same.symm ▸ member
  simp [live, boundary] at next

theorem rounds_valid (fuel : ℕ) (state : State) (valid : system.valid state) :
    system.valid (rounds system fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    rw [rounds]
    split
    · rename_i nonempty
      exact ih _ (system.step_valid state valid nonempty)
    · exact valid

theorem rounds_finish (fuel : ℕ) (state : State) (valid : system.valid state)
    (enough : (live system.coordinate state).card ≤ fuel) :
    live system.coordinate (rounds system fuel state) = ∅ := by
  induction fuel generalizing state with
  | zero =>
    change live system.coordinate state = ∅
    exact card_eq_zero.mp (Nat.eq_zero_of_le_zero enough)
  | succ fuel ih =>
    rw [rounds]
    split
    · rename_i nonempty
      have fewer := live_step_lt system state valid nonempty
      exact ih _ (system.step_valid state valid nonempty) (by omega)
    · rename_i empty
      exact not_nonempty_iff_eq_empty.mp empty

theorem rounds_fixed (fuel : ℕ) (state : State) (valid : system.valid state)
    (job : Job) (outside : job ∉ live system.coordinate state) :
    system.coordinate (rounds system fuel state) job = system.coordinate state job := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [rounds]
    split
    · rename_i nonempty
      rw [ih _ (system.step_valid state valid nonempty)
        (fun member => outside (live_step_subset system state valid member))]
      exact system.step_fixed state valid job outside
    · rfl

def sign (state : State) (job : Job) : ℤ := if system.coordinate state job < 0 then -1 else 1

theorem sign_assigned (state : State) (job : Job) :
    sign system state job = -1 ∨ sign system state job = 1 := by
  unfold sign
  split <;> simp

theorem frozen_sign (state : State) (valid : system.valid state)
    (job : Job) (outside : job ∉ live system.coordinate state) :
    (sign system state job : ℚ) = system.coordinate state job := by
  have cube := system.cube state valid job
  have boundary : |system.coordinate state job| = 1 := by
    simp only [live, mem_filter, mem_univ, true_and, not_lt] at outside
    exact le_antisymm cube outside
  unfold sign
  split
  · rename_i negative
    rw [abs_of_neg negative] at boundary
    norm_num
    linarith
  · rename_i nonnegative
    rw [abs_of_nonneg (le_of_not_gt nonnegative)] at boundary
    simpa using boundary.symm

theorem released_bound (fuel : ℕ) (state : State) (valid : system.valid state)
    (enough : (live system.coordinate state).card ≤ fuel)
    (positive : 0 < system.overlap) (category : Category)
    (small : ((live system.coordinate state).filter fun job => job ∈ system.members category).card ≤ system.overlap)
    (zero : ∑ job ∈ system.members category, system.coordinate state job = 0) :
    |∑ job ∈ system.members category, sign system (rounds system fuel state) job| ≤
      2 * (system.overlap : ℤ) - 1 := by
  apply Rounding.released_category_bound (system.members category)
    ((live system.coordinate state).filter fun job => job ∈ system.members category)
    system.overlap positive (by intro job member; exact (mem_filter.mp member).2) small
    (system.coordinate state) (sign system (rounds system fuel state))
  · intro job member
    exact abs_lt.mp (mem_filter.mp (mem_filter.mp member).1).2
  · intro job _
    exact sign_assigned system _ job
  · intro job member outside
    have fixed : job ∉ live system.coordinate state := by
      intro liveMember
      exact outside (mem_filter.mpr ⟨liveMember, member⟩)
    rw [frozen_sign system _ (rounds_valid system fuel state valid) job
      (by rw [rounds_finish system fuel state valid enough]; simp)]
    exact rounds_fixed system fuel state valid job fixed
  · exact zero

theorem category_bound (fuel : ℕ) (state : State) (valid : system.valid state)
    (enough : (live system.coordinate state).card ≤ fuel)
    (positive : 0 < system.overlap) (category : Category)
    (zero : ∑ job ∈ system.members category, system.coordinate state job = 0) :
    |∑ job ∈ system.members category, sign system (rounds system fuel state) job| ≤
      2 * (system.overlap : ℤ) - 1 := by
  induction fuel generalizing state with
  | zero =>
    apply released_bound system 0 state valid enough positive category _ zero
    have bound := card_filter_le (live system.coordinate state) (fun job => job ∈ system.members category)
    omega
  | succ fuel ih =>
    by_cases small : ((live system.coordinate state).filter fun job => job ∈ system.members category).card ≤ system.overlap
    · exact released_bound system (fuel + 1) state valid enough positive category small zero
    · have protectedCount := Nat.lt_of_not_ge small
      have nonempty : (live system.coordinate state).Nonempty := by
        apply card_pos.mp
        have bound := card_filter_le (live system.coordinate state) (fun job => job ∈ system.members category)
        omega
      have fewer := live_step_lt system state valid nonempty
      rw [rounds, ite_eq_left nonempty]
      exact ih _ (system.step_valid state valid nonempty) (by omega)
        ((system.step_preserves state valid category protectedCount).trans zero)

variable [Fintype Category]

theorem initial_correct (state : State) (valid : system.valid state)
    (zero : ∀ job, system.coordinate state job = 0)
    (overlap : ∀ job, (univ.filter fun category => job ∈ system.members category).card ≤ system.overlap) :
    let result := rounds system (Fintype.card Job) state
    (∀ job, system.coordinate result job = -1 ∨ system.coordinate result job = 1) ∧
    ∀ category, |∑ job ∈ system.members category, sign system result job| ≤
      max 0 (2 * (system.overlap : ℤ) - 1) := by
  let result := rounds system (Fintype.card Job) state
  have enough : (live system.coordinate state).card ≤ Fintype.card Job := card_le_univ _
  have finished := rounds_finish system (Fintype.card Job) state valid enough
  have resultValid := rounds_valid system (Fintype.card Job) state valid
  constructor
  · intro job
    have frozen := frozen_sign system result resultValid job (by rw [finished]; simp)
    rcases sign_assigned system result job with h | h <;> rw [h] at frozen
    · exact Or.inl (by simpa using frozen.symm)
    · exact Or.inr (by simpa using frozen.symm)
  · intro category
    by_cases positive : 0 < system.overlap
    · apply (category_bound system (Fintype.card Job) state valid enough positive category ?_).trans (le_max_right _ _)
      exact sum_eq_zero (fun job _ => zero job)
    · have empty : system.members category = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro job member
        have bound := overlap job
        have counted : category ∈ univ.filter (fun category => job ∈ system.members category) := by simp [member]
        have card := card_pos.mpr ⟨category, counted⟩
        omega
      simp [empty]

#print axioms rounds_finish
#print axioms initial_correct

end Project.Beck.GenericLoop
