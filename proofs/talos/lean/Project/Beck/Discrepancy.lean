import Project.Beck.Loop

namespace Project.Beck.Discrepancy

open LeanExe.Examples.Beck

def sign (x : Point) (job : Nat) : ℤ := if negative x.numerators[job]! then -1 else 1

theorem sign_assigned (x : Point) (job : Nat) : sign x job = -1 ∨ sign x job = 1 := by
  unfold sign
  split <;> simp

theorem frozen_coordinate (input : Input) (x : Point) (r : Nat)
    (state : State.Valid input.jobs x r) (job : Nat) (frozen : frozen x job = true) :
    State.coordinate x job = (sign x job : ℚ) := by
  have h := (State.frozen_iff x job).mp frozen
  have positive : (0 : ℚ) < x.denominator.toNat := by exact_mod_cast state.positive
  unfold sign
  split
  · rename_i negative
    have hp := (Arithmetic.negative_iff _).mp negative
    rw [abs_of_neg hp] at h
    have value : Arithmetic.value x.numerators[job]! = -(x.denominator.toNat : ℤ) := by omega
    simp [State.coordinate, value, ne_of_gt positive]
  · rename_i nonnegative
    have hp : 0 ≤ Arithmetic.value x.numerators[job]! := by
      have := mt (Arithmetic.negative_iff _).mpr nonnegative
      omega
    rw [abs_of_nonneg hp] at h
    simp [State.coordinate, h, ne_of_gt positive]

theorem live_interior (input : Input) (x : Point) (r : Nat)
    (state : State.Valid input.jobs x r) (job : Fin input.jobs) (live : job ∈ Counting.live input x) :
    -1 < State.coordinate x job.val ∧ State.coordinate x job.val < 1 := by
  have notFrozen : frozen x job.val = false := (Finset.mem_filter.mp live).2
  have strict : |Arithmetic.value x.numerators[job.val]!| < (x.denominator.toNat : ℤ) := by
    have different : |Arithmetic.value x.numerators[job.val]!| ≠ (x.denominator.toNat : ℤ) := by
      intro equal
      have := (State.frozen_iff x job.val).mpr equal
      simp [notFrozen] at this
    have cube := state.cube job.val job.isLt
    omega
  have bounds : -(x.denominator.toNat : ℚ) < (Arithmetic.value x.numerators[job.val]! : ℚ) ∧
      (Arithmetic.value x.numerators[job.val]! : ℚ) < x.denominator.toNat := by
    exact_mod_cast abs_lt.mp strict
  have positive : (0 : ℚ) < x.denominator.toNat := by exact_mod_cast state.positive
  unfold State.coordinate
  constructor
  · apply (lt_div_iff₀ positive).mpr
    simpa using bounds.1
  · exact (div_lt_one positive).mpr bounds.2

theorem rounds_fixed (input : Input) (x : Point) (r fuel : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r)
    (budget : r + fuel ≤ 6) (enough : (Counting.live input x).card ≤ fuel)
    (job : Nat) (hj : job < input.jobs) (frozen : frozen x job = true) :
    State.coordinate (rounds fuel input x) job = State.coordinate x job := by
  induction fuel generalizing r x with
  | zero =>
    cases h : allFrozen x
    · have nonempty := (Loop.live_nonempty input x state.size).mpr h
      have := nonempty.card_pos
      omega
    · simp [rounds, h]
  | succ fuel ih =>
    by_cases done : allFrozen x = true
    · simp [rounds, done]
    · have running : allFrozen x = false := Bool.eq_false_iff.mpr done
      have nonempty := (Loop.live_nonempty input x state.size).mpr running
      have limit : r ≤ 5 := by omega
      have step := SourceRound.round_valid_progress input x r supported state limit nonempty
      have fewer := Loop.live_decreases input x r supported state limit nonempty
      have nonzero : (LeanExe.Examples.Beck.round input x).denominator ≠ 0 := by
        intro zero
        have positive := step.1.positive
        simp [zero] at positive
      have fixed := ih (LeanExe.Examples.Beck.round input x) (r + 1) step.1 (by omega) (by omega)
        (step.2.1 job hj frozen)
      rw [rounds]
      simp only [done, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, nonzero]
      rw [fixed, SourceRound.round_eq input x
        (Direction.direction_size_nonzero input x supported.capacity supported.overlap nonempty).1
        (SourceRound.step_valid input x r supported state limit nonempty).speedPositive]
      exact SourceRound.updated_fixed input x r supported state limit nonempty job hj frozen

theorem released_bound (input : Input) (x : Point) (r fuel : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r)
    (budget : r + fuel ≤ 6) (enough : (Counting.live input x).card ≤ fuel)
    (positive : 0 < input.overlap) (category : Fin input.categories)
    (small : liveCount input x category.val ≤ input.overlap)
    (zero : ∑ job ∈ Counting.members input category, State.coordinate x job.val = 0) :
    |∑ job ∈ Counting.members input category, sign (rounds fuel input x) job.val| ≤
      2 * (input.overlap : ℤ) - 1 := by
  obtain ⟨finalRound, _, finalState, finished⟩ := Loop.rounds_finish input x r fuel supported state budget enough
  apply Rounding.released_category_bound (Counting.members input category)
    ((Counting.live input x).filter fun job => job ∈ Counting.members input category) input.overlap positive
    (by intro job member; exact (Finset.mem_filter.mp member).2)
    ((Counting.liveCount_card input x category).symm ▸ small)
    (fun job => State.coordinate x job.val) (fun job => sign (rounds fuel input x) job.val)
  · intro job member
    exact live_interior input x r state job (Finset.mem_filter.mp member).1
  · intro job _
    exact sign_assigned _ _
  · intro job member outside
    have frozen : frozen x job.val = true := by
      cases h : frozen x job.val
      · exfalso
        apply outside
        simp [Counting.live, h, member]
      · rfl
    have finalFrozen : LeanExe.Examples.Beck.frozen (rounds fuel input x) job.val = true :=
      (Loop.allFrozen_iff _).mp finished job.val (by rw [finalState.size]; exact job.isLt)
    rw [← frozen_coordinate input _ finalRound finalState job.val finalFrozen,
      rounds_fixed input x r fuel supported state budget enough job.val job.isLt frozen]
  · exact zero

theorem category_bound (input : Input) (x : Point) (r fuel : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r)
    (budget : r + fuel ≤ 6) (enough : (Counting.live input x).card ≤ fuel)
    (positive : 0 < input.overlap) (category : Fin input.categories)
    (zero : ∑ job ∈ Counting.members input category, State.coordinate x job.val = 0) :
    |∑ job ∈ Counting.members input category, sign (rounds fuel input x) job.val| ≤
      2 * (input.overlap : ℤ) - 1 := by
  induction fuel generalizing r x with
  | zero =>
    apply released_bound input x r 0 supported state budget enough positive category _ zero
    rw [Counting.liveCount_card]
    have bound := Finset.card_filter_le (Counting.live input x) (fun job => job ∈ Counting.members input category)
    omega
  | succ fuel ih =>
    by_cases small : liveCount input x category.val ≤ input.overlap
    · exact released_bound input x r (fuel + 1) supported state budget enough positive category small zero
    · have protectedCount : input.overlap < liveCount input x category.val := by omega
      have nonempty : (Counting.live input x).Nonempty := by
        apply Finset.card_pos.mp
        have bound := Finset.card_filter_le (Counting.live input x) (fun job => job ∈ Counting.members input category)
        rw [← Counting.liveCount_card input x category] at bound
        omega
      have running := (Loop.live_nonempty input x state.size).mp nonempty
      have limit : r ≤ 5 := by omega
      have step := SourceRound.round_valid_progress input x r supported state limit nonempty
      have fewer := Loop.live_decreases input x r supported state limit nonempty
      have nonzero : (LeanExe.Examples.Beck.round input x).denominator ≠ 0 := by
        intro empty
        have positive := step.1.positive
        simp [empty] at positive
      have preserved : ∑ job ∈ Counting.members input category,
          State.coordinate (LeanExe.Examples.Beck.round input x) job.val = 0 := by
        rw [SourceRound.round_eq input x
          (Direction.direction_size_nonzero input x supported.capacity supported.overlap nonempty).1
          (SourceRound.step_valid input x r supported state limit nonempty).speedPositive,
          SourceRound.updated_preserves_category input x r supported state limit nonempty category protectedCount]
        exact zero
      have result := ih (LeanExe.Examples.Beck.round input x) (r + 1) step.1 (by omega) (by omega) preserved
      simpa [rounds, running, nonzero] using result

theorem initial_bound (input : Input) (supported : State.Supported input)
    (positive : 0 < input.overlap) (category : Fin input.categories) :
    |∑ job ∈ Counting.members input category,
      sign (rounds input.jobs input ⟨1, Array.replicate input.jobs 0⟩) job.val| ≤
      2 * (input.overlap : ℤ) - 1 := by
  apply category_bound input _ 0 input.jobs supported (State.initial input.jobs)
    (by simpa using supported.capacity)
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)) positive category
  apply Finset.sum_eq_zero
  intro job _
  simp [State.coordinate, Arithmetic.value]

theorem zero_overlap_empty (input : Input) (supported : State.Supported input)
    (zero : input.overlap = 0) (category : Fin input.categories) : Counting.members input category = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro job member
  have bound := supported.overlap job
  rw [zero, Nat.le_zero, Finset.card_eq_zero] at bound
  have counted : category ∈ Finset.univ.filter (fun category => job ∈ Counting.members input category) := by
    simp [member]
  simp [bound] at counted

theorem initial_discrepancy (input : Input) (supported : State.Supported input)
    (category : Fin input.categories) :
    |∑ job ∈ Counting.members input category,
      sign (rounds input.jobs input ⟨1, Array.replicate input.jobs 0⟩) job.val| ≤
      max 0 (2 * (input.overlap : ℤ) - 1) := by
  by_cases zero : input.overlap = 0
  · simp [zero_overlap_empty input supported zero category, zero]
  · exact (initial_bound input supported (Nat.pos_of_ne_zero zero) category).trans (le_max_right _ _)

end Project.Beck.Discrepancy
