import Project.Beck.Names
import Project.Beck.Parser

namespace Project.Beck.Encoding

open LeanExe.Examples.Beck

structure Job (words : Array UInt64) (categories pos : Nat) (ids : List Nat) : Prop where
  header : pos < words.size
  count : words[pos]!.toNat = ids.length
  fits : pos + 1 + ids.length ≤ words.size
  identifiers : Names.names words (pos + 1) ids.length = ids
  distinct : ids.Nodup
  bounded : ∀ category ∈ ids, category < categories

inductive Records (words : Array UInt64) (categories : Nat) : Nat → Nat → List (List Nat) → Prop
  | nil (pos : Nat) : Records words categories pos pos []
  | cons {pos stop : Nat} {ids : List Nat} {rest : List (List Nat)} :
      Job words categories pos ids → Records words categories (pos + 1 + ids.length) stop rest →
      Records words categories pos stop (ids :: rest)

structure Input (words : Array UInt64) (categories : Nat) (jobs : List (List Nat)) : Prop where
  header : 2 ≤ words.size
  jobsWord : words[0]!.toNat = jobs.length
  categoriesWord : words[1]!.toNat = categories
  jobsBound : jobs.length ≤ 6
  categoriesBound : categories ≤ 8
  records : Records words categories 2 words.size jobs

def row (categories : Nat) (ids : List Nat) : Array UInt64 :=
  (List.ofFn fun category : Fin categories => if category.val ∈ ids then (1 : UInt64) else 0).toArray

def matrix (categories : Nat) : List (List Nat) → Array UInt64
  | [] => #[]
  | ids :: rest => row categories ids ++ matrix categories rest

theorem row_size (categories : Nat) (ids : List Nat) : (row categories ids).size = categories := by
  simp [row]

theorem row_get (categories : Nat) (ids : List Nat) (category : Nat) (bounded : category < categories) :
    (row categories ids)[category]! = if category ∈ ids then 1 else 0 := by
  rw [getElem!_pos (row categories ids) category (by rw [row_size]; exact bounded)]
  simp [row]

theorem matrix_size (categories : Nat) (jobs : List (List Nat)) :
    (matrix categories jobs).size = jobs.length * categories := by
  induction jobs with
  | nil => simp [matrix]
  | cons ids jobs ih => simp [matrix, row_size, ih, Nat.add_mul, Nat.add_comm]

theorem matrix_get (categories : Nat) (jobs : List (List Nat))
    (job : Nat) (hj : job < jobs.length) (category : Nat) (hc : category < categories) :
    (matrix categories jobs)[job * categories + category]! = if category ∈ jobs[job]! then 1 else 0 := by
  induction jobs generalizing job with
  | nil => simp at hj
  | cons ids jobs ih =>
    have bound : job * categories + category < (matrix categories (ids :: jobs)).size := by
      rw [matrix_size]
      nlinarith
    rw [getElem!_pos (matrix categories (ids :: jobs)) _ bound]
    cases job with
    | zero =>
      simp only [matrix, Nat.zero_mul, Nat.zero_add]
      rw [Array.getElem_append_left (by rw [row_size]; exact hc)]
      rw [← getElem!_pos (row categories ids) category (by rw [row_size]; exact hc), row_get _ _ _ hc]
      simp
    | succ job =>
      simp only [matrix]
      rw [Array.getElem_append_right (by rw [row_size]; nlinarith)]
      have index : (job + 1) * categories + category - (row categories ids).size = job * categories + category := by
        rw [row_size, Nat.add_mul]
        omega
      simp only [index]
      rw [← getElem!_pos (matrix categories jobs) (job * categories + category) (by rw [matrix_size]; simp at hj; nlinarith)]
      rw [ih job (by simpa using hj)]
      simp

theorem read_row (count : Nat) (words : Array UInt64) (pos categories : Nat) (out : Array UInt64)
    (accepted : readMemberships count words pos categories (Array.replicate categories 0) = some out) :
    out = row categories (Names.names words pos count) := by
  have spec := Memberships.read_spec count words pos categories _ out (Memberships.initial categories) accepted
  apply Array.ext
  · rw [spec.1.size, row_size]
  · intro category hc hr
    have bound : category < categories := by simpa [spec.1.size] using hc
    rw [← getElem!_pos out category hc, ← getElem!_pos (row categories (Names.names words pos count)) category hr,
      row_get categories _ category bound]
    have member : out[category]! = 1 ↔ category ∈ Names.names words pos count := by
      have result := spec.2.2 ⟨category, bound⟩
      simpa [Memberships.selected, Memberships.initial_selected, Names.mem] using result
    split
    · exact member.mpr ‹_›
    · rename_i absent
      rcases spec.1.binary category bound with zero | one
      · exact zero
      · exact False.elim (absent (member.mp one))

theorem readJobs_sound (fuel : Nat) (words : Array UInt64) (categories : Nat) (state out : ParseState)
    (accepted : readJobs fuel words categories state = some out) :
    ∃ jobs : List (List Nat), jobs.length = fuel ∧
      Records words categories state.position out.position jobs ∧
      out.incidence = state.incidence ++ matrix categories jobs := by
  induction fuel generalizing state with
  | zero =>
    simp only [readJobs, Option.some.injEq] at accepted
    subst out
    exact ⟨[], rfl, .nil _, by simp [matrix]⟩
  | succ fuel ih =>
    simp only [readJobs] at accepted
    split at accepted
    · contradiction
    rename_i header
    split at accepted
    · contradiction
    rename_i fits
    split at accepted
    · contradiction
    rename_i parsedRow parsed
    let ids := Names.names words (state.position + 1) words[state.position]!.toNat
    have sound := Names.read_sound _ _ _ _ _ parsedRow (Memberships.initial categories) parsed
    obtain ⟨jobs, length, records, incidence⟩ := ih _ accepted
    refine ⟨ids :: jobs, by simp [ids, length], .cons ?_ ?_, ?_⟩
    · refine ⟨by omega, by simp [ids, Names.length], ?_, by simp [ids, Names.length], sound.1, ?_⟩
      · have bounds : words[state.position]!.toNat ≤ categories ∧
            state.position + 1 + words[state.position]!.toNat ≤ words.size := by simpa using fits
        simpa [ids, Names.length] using bounds.2
      · intro category member
        exact (sound.2 category member).1
    · simpa [ids, Names.length] using records
    · rw [incidence]
      simp only [matrix, ← Array.append_assoc]
      rw [read_row _ _ _ _ parsedRow parsed]

theorem records_complete (words : Array UInt64) (categories start stop : Nat) (jobs : List (List Nat))
    (records : Records words categories start stop jobs) (state : ParseState) (position : state.position = start) :
    ∃ out, readJobs jobs.length words categories state = some out ∧ out.position = stop ∧
      out.incidence = state.incidence ++ matrix categories jobs ∧
      out.overlap = jobs.foldl (fun t ids => max t ids.length) state.overlap := by
  induction records generalizing state with
  | nil pos => exact ⟨state, rfl, position, by simp [matrix], rfl⟩
  | @cons pos stop ids rest job records ih =>
    have countBound : ids.length ≤ categories := by
      apply Names.count_le words (pos + 1)
      · simpa [job.identifiers] using job.distinct
      · simpa [job.identifiers] using job.bounded
    obtain ⟨parsedRow, parsed⟩ := Names.read_complete ids.length words (pos + 1) categories
      (Array.replicate categories 0) (Memberships.initial categories)
      (by simpa [job.identifiers] using job.distinct) (by
        intro category member
        have bounded := job.bounded category (by simpa [job.identifiers] using member)
        refine ⟨bounded, ?_⟩
        simp [getElem!_pos (Array.replicate categories (0 : UInt64)) category (by simpa)])
    obtain ⟨out, accepted, terminal, incidence, overlap⟩ := ih
      ⟨pos + 1 + ids.length, max state.overlap ids.length, state.incidence ++ parsedRow⟩ rfl
    refine ⟨out, ?_, terminal, ?_, overlap⟩
    · simpa [readJobs, position, Nat.not_le.mpr job.header, job.count,
        Nat.not_lt.mpr countBound, Nat.not_lt.mpr job.fits, parsed] using accepted
    · rw [incidence]
      simp only [matrix, ← Array.append_assoc]
      rw [read_row _ _ _ _ parsedRow parsed, job.identifiers]

theorem accepted_header (words : Array UInt64) (accepted : (readInput words).status = 0) :
    2 ≤ words.size := by
  by_contra small
  have short : words.size < 2 := by omega
  have equal : readInput words = reject 1 := by simp [readInput, short]
  rw [equal] at accepted
  exact absurd accepted (by decide)

theorem input_sound (words : Array UInt64) (accepted : (readInput words).status = 0) :
    ∃ jobs : List (List Nat), Input words (readInput words).categories jobs ∧
      jobs.length = (readInput words).jobs ∧
      (readInput words).incidence = matrix (readInput words).categories jobs := by
  obtain ⟨out, parsed, terminal, jobsBound, categoriesBound, result⟩ := Parser.accepted_data words accepted
  obtain ⟨jobs, length, records, incidence⟩ := readJobs_sound _ _ _ _ out parsed
  rw [result]
  refine ⟨jobs, ⟨accepted_header words accepted, length.symm, rfl, ?_, categoriesBound, ?_⟩, length, ?_⟩
  · omega
  · simpa [terminal] using records
  · simpa using incidence

theorem input_complete (words : Array UInt64) (categories : Nat) (jobs : List (List Nat))
    (encoded : Input words categories jobs) :
    (readInput words).status = 0 ∧ (readInput words).jobs = jobs.length ∧
      (readInput words).categories = categories ∧ (readInput words).incidence = matrix categories jobs ∧
      (readInput words).overlap = jobs.foldl (fun t ids => max t ids.length) 0 := by
  obtain ⟨out, parsed, terminal, incidence, overlap⟩ := records_complete words categories 2 words.size jobs
    encoded.records ⟨2, 0, #[]⟩ rfl
  have header : ¬words.size < 2 := Nat.not_lt.mpr encoded.header
  have capacity : ¬(decide (words[0]! > 6) || decide (words[1]! > 8)) = true := by
    simpa [UInt64.lt_iff_toNat_lt, encoded.jobsWord, encoded.categoriesWord] using
      And.intro encoded.jobsBound encoded.categoriesBound
  simp [readInput, header, capacity, encoded.jobsWord, encoded.categoriesWord, parsed, terminal, incidence, overlap]

theorem accepted_iff (words : Array UInt64) :
    (readInput words).status = 0 ↔ ∃ categories jobs, Input words categories jobs := by
  constructor
  · intro accepted
    obtain ⟨jobs, encoded, _⟩ := input_sound words accepted
    exact ⟨_, jobs, encoded⟩
  · rintro ⟨categories, jobs, encoded⟩
    exact (input_complete words categories jobs encoded).1

theorem input_eq (words : Array UInt64) (categories : Nat) (jobs : List (List Nat))
    (encoded : Input words categories jobs) :
    readInput words = LeanExe.Examples.Beck.Input.mk 0 jobs.length categories
      (jobs.foldl (fun t ids => max t ids.length) 0) (matrix categories jobs) := by
  have properties := input_complete words categories jobs encoded
  calc
    readInput words = LeanExe.Examples.Beck.Input.mk (readInput words).status (readInput words).jobs
      (readInput words).categories (readInput words).overlap (readInput words).incidence := rfl
    _ = _ := by rw [properties.1, properties.2.1, properties.2.2.1, properties.2.2.2.1, properties.2.2.2.2]

theorem Job.length_le {words : Array UInt64} {categories pos : Nat} {ids : List Nat}
    (job : Job words categories pos ids) : ids.length ≤ categories := by
  apply Names.count_le words (pos + 1)
  · simpa [job.identifiers] using job.distinct
  · simpa [job.identifiers] using job.bounded

theorem records_size_bound (words : Array UInt64) (categories start stop : Nat) (jobs : List (List Nat))
    (records : Records words categories start stop jobs) : stop ≤ start + jobs.length * (categories + 1) := by
  induction records with
  | nil => simp
  | @cons pos stop ids rest job records ih =>
    have bound := job.length_le
    simp only [List.length_cons]
    nlinarith

theorem input_size_bound (words : Array UInt64) (categories : Nat) (jobs : List (List Nat))
    (encoded : Input words categories jobs) : words.size ≤ 56 := by
  have bound := records_size_bound words categories 2 words.size jobs encoded.records
  have jobsBound := encoded.jobsBound
  have categoriesBound := encoded.categoriesBound
  nlinarith

end Project.Beck.Encoding
