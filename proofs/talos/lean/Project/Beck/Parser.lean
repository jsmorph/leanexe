import Project.Beck.Memberships

namespace Project.Beck.Parser

open LeanExe.Examples.Beck

def degree (categories : Nat) (incidence : Array UInt64) (job : Nat) : Nat :=
  (Finset.univ.filter fun category : Fin categories => incidence[job * categories + category.val]! = 1).card

structure Valid (jobs categories : Nat) (state : ParseState) : Prop where
  size : state.incidence.size = jobs * categories
  binary : ∀ job < jobs, ∀ category < categories,
    state.incidence[job * categories + category]! = 0 ∨ state.incidence[job * categories + category]! = 1
  overlap : ∀ job < jobs, degree categories state.incidence job ≤ state.overlap
  maximum : state.overlap = 0 ∨ ∃ job < jobs, degree categories state.incidence job = state.overlap

theorem initial (categories : Nat) : Valid 0 categories ⟨2, 0, #[]⟩ := by
  constructor <;> simp

theorem append_old (jobs categories : Nat) (state : ParseState) (valid : Valid jobs categories state)
    (row : Array UInt64) (job : Nat) (hj : job < jobs) (category : Nat) (hc : category < categories) :
    (state.incidence ++ row)[job * categories + category]! = state.incidence[job * categories + category]! := by
  have bound : job * categories + category < state.incidence.size := by
    rw [valid.size]
    nlinarith
  rw [getElem!_pos (state.incidence ++ row) _ (by simp; omega),
    Array.getElem_append_left bound, getElem!_pos state.incidence _ bound]

theorem append_new (jobs categories : Nat) (state : ParseState) (valid : Valid jobs categories state)
    (row : Array UInt64) (rowValid : Memberships.Valid categories row)
    (category : Nat) (hc : category < categories) :
    (state.incidence ++ row)[jobs * categories + category]! = row[category]! := by
  rw [getElem!_pos (state.incidence ++ row) _ (by simp [valid.size, rowValid.size]; omega)]
  rw [Array.getElem_append_right (by rw [valid.size]; omega)]
  simp [valid.size, getElem!_pos row category (by rw [rowValid.size]; exact hc)]

theorem degree_old (jobs categories : Nat) (state : ParseState) (valid : Valid jobs categories state)
    (row : Array UInt64) (job : Nat) (hj : job < jobs) :
    degree categories (state.incidence ++ row) job = degree categories state.incidence job := by
  simp only [degree]
  congr 1
  ext category
  simp [append_old jobs categories state valid row job hj category.val category.isLt]

theorem degree_new (jobs categories : Nat) (state : ParseState) (valid : Valid jobs categories state)
    (row : Array UInt64) (rowValid : Memberships.Valid categories row) :
    degree categories (state.incidence ++ row) jobs = (Memberships.selected categories row).card := by
  simp only [degree, Memberships.selected]
  congr 1
  ext category
  simp [append_new jobs categories state valid row rowValid category.val category.isLt]

theorem append_valid (jobs categories : Nat) (state : ParseState) (valid : Valid jobs categories state)
    (row : Array UInt64) (rowValid : Memberships.Valid categories row) (count position : Nat)
    (card : (Memberships.selected categories row).card = count) :
    Valid (jobs + 1) categories ⟨position, max state.overlap count, state.incidence ++ row⟩ := by
  constructor
  · simp [valid.size, rowValid.size, Nat.add_mul]
  · intro job hj category hc
    by_cases old : job < jobs
    · rw [append_old jobs categories state valid row job old category hc]
      exact valid.binary job old category hc
    · have equal : job = jobs := by omega
      subst job
      rw [append_new jobs categories state valid row rowValid category hc]
      exact rowValid.binary category hc
  · intro job hj
    change degree categories (state.incidence ++ row) job ≤ max state.overlap count
    by_cases old : job < jobs
    · rw [degree_old jobs categories state valid row job old]
      exact (valid.overlap job old).trans (le_max_left _ _)
    · have equal : job = jobs := by omega
      subst job
      rw [degree_new jobs categories state valid row rowValid, card]
      exact le_max_right _ _
  · change max state.overlap count = 0 ∨ ∃ job < jobs + 1,
      degree categories (state.incidence ++ row) job = max state.overlap count
    by_cases larger : state.overlap ≤ count
    · right
      exact ⟨jobs, by omega, by rw [degree_new jobs categories state valid row rowValid, card, max_eq_right larger]⟩
    · rw [max_eq_left (by omega : count ≤ state.overlap)]
      rcases valid.maximum with zero | ⟨job, hj, attained⟩
      · exact Or.inl zero
      · exact Or.inr ⟨job, by omega, by rw [degree_old jobs categories state valid row job hj]; exact attained⟩

theorem readJobs_valid (fuel jobs categories : Nat) (words : Array UInt64) (state out : ParseState)
    (valid : Valid jobs categories state) (accepted : readJobs fuel words categories state = some out) :
    Valid (jobs + fuel) categories out := by
  induction fuel generalizing jobs state with
  | zero =>
    simp only [readJobs, Option.some.injEq] at accepted
    subst out
    simpa using valid
  | succ fuel ih =>
    simp only [readJobs] at accepted
    split at accepted
    · contradiction
    split at accepted
    · contradiction
    split at accepted
    · contradiction
    rename_i row readRow
    have rowSpec := Memberships.read_spec _ _ _ _ _ row (Memberships.initial categories) readRow
    have card : (Memberships.selected categories row).card = words[state.position]!.toNat := by
      simpa [Memberships.initial_selected] using rowSpec.2.1
    have nextValid := append_valid jobs categories state valid row rowSpec.1 _ (state.position + 1 + words[state.position]!.toNat) card
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (jobs + 1) _ nextValid accepted

theorem accepted_data (words : Array UInt64) (accepted : (readInput words).status = 0) :
    ∃ out : ParseState, readJobs words[0]!.toNat words words[1]!.toNat ⟨2, 0, #[]⟩ = some out ∧
      out.position = words.size ∧ words[0]!.toNat ≤ 6 ∧ words[1]!.toNat ≤ 8 ∧
      readInput words = ⟨0, words[0]!.toNat, words[1]!.toNat, out.overlap, out.incidence⟩ := by
  unfold readInput at accepted
  split at accepted
  · exact absurd accepted (by decide)
  rename_i header
  split at accepted
  · exact absurd accepted (by decide)
  rename_i capacity
  dsimp only at accepted
  split at accepted
  · exact absurd accepted (by decide)
  rename_i out parsed
  split at accepted
  · exact absurd accepted (by decide)
  rename_i terminal
  have capacities : words[0]!.toNat ≤ 6 ∧ words[1]!.toNat ≤ 8 := by
    simpa [UInt64.lt_iff_toNat_lt] using capacity
  refine ⟨out, parsed, ?_, capacities.1, capacities.2, ?_⟩
  · simpa using terminal
  · simp [readInput, header, capacity, parsed, terminal]

theorem accepted_valid (words : Array UInt64) (accepted : (readInput words).status = 0) :
    Valid (readInput words).jobs (readInput words).categories
      ⟨words.size, (readInput words).overlap, (readInput words).incidence⟩ ∧
      (readInput words).jobs ≤ 6 ∧ (readInput words).categories ≤ 8 := by
  obtain ⟨out, parsed, terminal, jobs, categories, result⟩ := accepted_data words accepted
  rw [result]
  have valid := readJobs_valid words[0]!.toNat 0 words[1]!.toNat words _ out
    (initial words[1]!.toNat) parsed
  have state : ParseState.mk words.size out.overlap out.incidence = out := by
    rw [← terminal]
  exact ⟨by simpa [state] using valid, jobs, categories⟩

theorem accepted_supported (words : Array UInt64) (accepted : (readInput words).status = 0) :
    State.Supported (readInput words) := by
  have valid := accepted_valid words accepted
  refine ⟨valid.2.1, valid.1.binary, ?_⟩
  intro job
  simpa [degree, Counting.members] using valid.1.overlap job.val job.isLt

end Project.Beck.Parser
