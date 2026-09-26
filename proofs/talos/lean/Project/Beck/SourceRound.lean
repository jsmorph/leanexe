import Project.Beck.Move

namespace Project.Beck.SourceRound

open LeanExe.Examples.Beck

abbrev chosen (input : Input) (x : Point) := boundaryStep input x (direction input x)

structure StepValid (input : Input) (x : Point) : Prop where
  speedPositive : 0 < (chosen input x).2.toNat
  speedBound : (chosen input x).2.toNat ≤ 120
  distancePositive : 0 < (chosen input x).1.toNat
  distanceBound : (chosen input x).1.toNat ≤ 2 * x.denominator.toNat
  least : ∀ job < input.jobs, (direction input x)[job]! ≠ 0 →
    (chosen input x).1.toNat * (magnitude (direction input x)[job]!).toNat ≤
      (gap x.denominator x.numerators[job]! (direction input x)[job]!).toNat * (chosen input x).2.toNat
  hit : ∃ job < input.jobs, (direction input x)[job]! ≠ 0 ∧
    chosen input x = Boundary.candidate x (direction input x) job

theorem step_valid (input : Input) (x : Point) (round : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x round) (fuel : round ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) : StepValid input x := by
  have denominator : x.denominator.toNat ≤ 120 ^ 5 :=
    state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)
  have speeds (job : Nat) (hj : job < input.jobs) :
      (magnitude (direction input x)[job]!).toNat ≤ 120 := by
    have bound := Direction.direction_bound input x supported.capacity supported.binary supported.overlap nonempty job hj
    rw [← Arithmetic.magnitude_exact] at bound
    exact_mod_cast bound
  have gaps (job : Nat) (hj : job < input.jobs) :
      (gap x.denominator x.numerators[job]! (direction input x)[job]!).toNat ≤ 2 * x.denominator.toNat :=
    State.gap_bounds _ _ _ denominator (state.cube job hj)
  have specification := Boundary.boundaryStep_spec input x (direction input x)
    (fun job hj => (gaps job hj).trans (Nat.mul_le_mul_left 2 denominator)) speeds
    (Direction.direction_size_nonzero input x supported.capacity supported.overlap nonempty).2
  obtain ⟨first, hf, hn, he, least⟩ := specification
  change chosen input x = Boundary.candidate x (direction input x) first at he
  have live : frozen x first = false := by
    apply Bool.eq_false_iff.mpr
    intro frozen
    exact hn (Direction.direction_frozen_zero input x supported.capacity supported.overlap nonempty first hf frozen)
  constructor
  · rw [he]
    apply Nat.pos_of_ne_zero
    intro zero
    exact hn ((Arithmetic.magnitude_zero _).mp (UInt64.toNat_inj.mp zero))
  · rw [he]
    exact speeds first hf
  · rw [he]
    exact State.gap_positive x first _ denominator (state.cube first hf) live
  · rw [he]
    exact gaps first hf
  · exact least
  · exact ⟨first, hf, hn, he⟩

def updated (input : Input) (x : Point) : Point :=
  ⟨x.denominator * (chosen input x).2,
    ((List.range input.jobs).map fun job =>
      x.numerators[job]! * (chosen input x).2 + (chosen input x).1 * (direction input x)[job]!).toArray⟩

theorem round_eq (input : Input) (x : Point)
    (size : (direction input x).size = input.jobs) (positive : 0 < (chosen input x).2.toNat) :
    LeanExe.Examples.Beck.round input x = updated input x := by
  have nonzero : (chosen input x).2 ≠ 0 := by intro h; simp [h] at positive
  simp only [LeanExe.Examples.Beck.round, size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change (if (chosen input x).2 == 0 then _ else _) = _
  rw [show ((chosen input x).2 == 0) = false by simpa using nonzero]
  simp only [Bool.false_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind, pure]
  congr 1
  let f := fun (job : Nat) => x.numerators[job]! * (chosen input x).2 + (chosen input x).1 * (direction input x)[job]!
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range input.jobs)
    (fun job (acc : Array UInt64) => acc.push (f job)) #[]
  exact loop.trans (by simp [f, pure])

theorem updated_size (input : Input) (x : Point) : (updated input x).numerators.size = input.jobs := by
  simp [updated]

theorem updated_get (input : Input) (x : Point) (job : Nat) (hj : job < input.jobs) :
    (updated input x).numerators[job]! =
      x.numerators[job]! * (chosen input x).2 + (chosen input x).1 * (direction input x)[job]! := by
  simp [updated, getElem!_pos, hj]

theorem updated_denominator (input : Input) (x : Point)
    (denominator : x.denominator.toNat ≤ 120 ^ 5) (step : StepValid input x) :
    (updated input x).denominator.toNat = x.denominator.toNat * (chosen input x).2.toNat :=
  Boundary.product_exact _ _ (by omega) step.speedBound

theorem updated_value (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) (step : StepValid input x)
    (job : Nat) (hj : job < input.jobs) :
    Arithmetic.value (updated input x).numerators[job]! =
      Arithmetic.value x.numerators[job]! * (chosen input x).2.toNat +
        (chosen input x).1.toNat * Arithmetic.value (direction input x)[job]! := by
  rw [updated_get input x job hj]
  exact (State.update_exact _ _ _ _ _
    ⟨state.positive, state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)⟩ (state.cube job hj)
    (Direction.direction_bound input x supported.capacity supported.binary supported.overlap nonempty job hj)
    ⟨step.speedPositive, step.speedBound⟩ step.distanceBound).2

theorem updated_valid (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) : State.Valid input.jobs (updated input x) (r + 1) := by
  have step := step_valid input x r supported state fuel nonempty
  have denominator : x.denominator.toNat ≤ 120 ^ 5 :=
    state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)
  have den := updated_denominator input x denominator step
  constructor
  · exact updated_size input x
  · rw [den]
    exact Nat.mul_pos state.positive step.speedPositive
  · rw [den, pow_succ]
    exact Nat.mul_le_mul state.denominator step.speedBound
  · intro job hj
    rw [updated_value input x r supported state fuel nonempty step job hj, den, Nat.cast_mul]
    apply Move.bounds _ _ _ _ _ (state.cube job hj) (by exact_mod_cast step.speedPositive) (by positivity)
    intro moving
    have wordNonzero := (Determinant.value_ne_zero _).mp moving
    have least := step.least job hj wordNonzero
    have integer : ((chosen input x).1.toNat : ℤ) * (magnitude (direction input x)[job]!).toNat ≤
        (gap x.denominator x.numerators[job]! (direction input x)[job]!).toNat * (chosen input x).2.toNat := by
      exact_mod_cast least
    rw [Arithmetic.magnitude_exact, State.gap_exact _ _ _ denominator (state.cube job hj)] at integer
    simpa only [Move.distance, Arithmetic.negative_iff] using integer

theorem updated_hits (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) :
    ∃ job < input.jobs, frozen x job = false ∧ frozen (updated input x) job = true := by
  have step := step_valid input x r supported state fuel nonempty
  have denominator : x.denominator.toNat ≤ 120 ^ 5 :=
    state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)
  obtain ⟨job, hj, moving, selected⟩ := step.hit
  refine ⟨job, hj, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro frozen
    exact moving (Direction.direction_frozen_zero input x supported.capacity supported.overlap nonempty job hj frozen)
  · rw [State.frozen_iff, updated_value input x r supported state fuel nonempty step job hj,
      updated_denominator input x denominator step, Nat.cast_mul, selected]
    simp only [Boundary.candidate]
    rw [Arithmetic.magnitude_exact, State.gap_exact _ _ _ denominator (state.cube job hj)]
    simp only [Arithmetic.negative_iff]
    exact Move.hits _ _ _ (by positivity)

theorem updated_frozen (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty)
    (job : Nat) (hj : job < input.jobs) (frozen : frozen x job = true) :
    LeanExe.Examples.Beck.frozen (updated input x) job = true := by
  have step := step_valid input x r supported state fuel nonempty
  have denominator : x.denominator.toNat ≤ 120 ^ 5 :=
    state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)
  rw [State.frozen_iff, updated_value input x r supported state fuel nonempty step job hj,
    updated_denominator input x denominator step, Nat.cast_mul,
    Direction.direction_frozen_zero input x supported.capacity supported.overlap nonempty job hj frozen]
  simp only [show Arithmetic.value (0 : UInt64) = 0 from rfl, mul_zero, add_zero, abs_mul,
    (State.frozen_iff x job).mp frozen]
  simp

def scale (input : Input) (x : Point) : ℚ :=
  (chosen input x).1.toNat / ((x.denominator.toNat : ℚ) * (chosen input x).2.toNat)

theorem updated_coordinate (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) (job : Nat) (hj : job < input.jobs) :
    State.coordinate (updated input x) job = State.coordinate x job +
      scale input x * (Arithmetic.value (direction input x)[job]! : ℚ) := by
  have step := step_valid input x r supported state fuel nonempty
  have denominator : x.denominator.toNat ≤ 120 ^ 5 :=
    state.denominator.trans (Nat.pow_le_pow_right (by decide) fuel)
  rw [State.coordinate, updated_value input x r supported state fuel nonempty step job hj,
    updated_denominator input x denominator step]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  exact Arithmetic.shared_denominator_update _ _ _ _ _
    (by exact_mod_cast Nat.ne_of_gt state.positive) (by exact_mod_cast Nat.ne_of_gt step.speedPositive)

theorem updated_fixed (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty)
    (job : Nat) (hj : job < input.jobs) (frozen : frozen x job = true) :
    State.coordinate (updated input x) job = State.coordinate x job := by
  rw [updated_coordinate input x r supported state fuel nonempty job hj,
    Direction.direction_frozen_zero input x supported.capacity supported.overlap nonempty job hj frozen]
  simp [Arithmetic.value]

theorem updated_preserves_category (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty)
    (category : Fin input.categories) (protectedCount : input.overlap < liveCount input x category.val) :
    (∑ job ∈ Counting.members input category, State.coordinate (updated input x) job.val) =
      ∑ job ∈ Counting.members input category, State.coordinate x job.val := by
  simp_rw [updated_coordinate input x r supported state fuel nonempty _ (Fin.isLt _)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    Preservation.direction_preserves_category input x supported.capacity supported.binary supported.overlap
      nonempty category protectedCount, mul_zero, add_zero]

theorem round_valid_progress (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) :
    let next := LeanExe.Examples.Beck.round input x
    State.Valid input.jobs next (r + 1) ∧
      (∀ job < input.jobs, frozen x job = true → frozen next job = true) ∧
      (∃ job < input.jobs, frozen x job = false ∧ frozen next job = true) := by
  have step := step_valid input x r supported state fuel nonempty
  dsimp only
  rw [round_eq input x (Direction.direction_size_nonzero input x supported.capacity supported.overlap nonempty).1
    step.speedPositive]
  exact ⟨updated_valid input x r supported state fuel nonempty,
    updated_frozen input x r supported state fuel nonempty,
    updated_hits input x r supported state fuel nonempty⟩

end Project.Beck.SourceRound
