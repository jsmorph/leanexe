import Project.Beck.Encoding
import Project.Beck.ExactParser

namespace Project.Beck.ExactEncoding

open LeanExe.Examples.BeckExact
open LeanExe.Examples.Beck (ParseState)

structure Input (words : Array UInt64) (categories : ℕ) (jobs : List (List ℕ)) : Prop where
  header : 2 ≤ words.size
  jobsWord : words[0]!.toNat = jobs.length
  categoriesWord : words[1]!.toNat = categories
  address : jobs.length = 0 ∨ categories ≤ ((4294967296 - 4096) / 8) / jobs.length
  records : Encoding.Records words categories 2 words.size jobs

theorem records_min_size (words : Array UInt64) (categories start stop : ℕ) (jobs : List (List ℕ))
    (records : Encoding.Records words categories start stop jobs) : start + jobs.length ≤ stop := by
  induction records with
  | nil => simp
  | @cons pos stop ids rest job records ih => simp only [List.length_cons]; omega

theorem input_complete (words : Array UInt64) (categories : ℕ) (jobs : List (List ℕ))
    (encoded : Input words categories jobs) :
    readInput words = LeanExe.Examples.Beck.Input.mk 0 jobs.length categories
      (jobs.foldl (fun t ids => max t ids.length) 0) (Encoding.matrix categories jobs) := by
  obtain ⟨out, parsed, terminal, incidence, overlap⟩ := Encoding.records_complete words categories 2 words.size jobs
    encoded.records ⟨2, 0, #[]⟩ rfl
  have header : ¬ words.size < 2 := by have := encoded.header; omega
  have count : ¬ jobs.length > words.size - 2 := by
    have bound := records_min_size words categories 2 words.size jobs encoded.records
    omega
  have address : ¬ (jobs.length != 0 && decide (categories > ((4294967296 - 4096) / 8) / jobs.length)) = true := by
    rcases encoded.address with empty | bound
    · simp [empty]
    · simp [Nat.not_lt.mpr bound]
  simp [readInput, header, encoded.jobsWord, encoded.categoriesWord, count, address, parsed,
    terminal, incidence, overlap]

theorem accepted_limits (words : Array UInt64) (accepted : (readInput words).status = 0) :
    2 ≤ words.size ∧ (words[0]!.toNat = 0 ∨
      words[1]!.toNat ≤ ((4294967296 - 4096) / 8) / words[0]!.toNat) := by
  unfold readInput at accepted
  split at accepted
  · exact absurd accepted (by decide)
  rename_i header
  dsimp only at accepted
  split at accepted
  · exact absurd accepted (by decide)
  split at accepted
  · exact absurd accepted (by decide)
  rename_i address
  refine ⟨by omega, ?_⟩
  by_cases empty : words[0]!.toNat = 0
  · exact Or.inl empty
  · exact Or.inr (by simpa [empty] using address)

theorem input_sound (words : Array UInt64) (accepted : (readInput words).status = 0) :
    ∃ categories jobs, Input words categories jobs := by
  obtain ⟨out, parsed, terminal, result⟩ := ExactParser.accepted_data words accepted
  obtain ⟨jobs, length, records, _⟩ := Encoding.readJobs_sound _ _ _ _ out parsed
  have limits := accepted_limits words accepted
  refine ⟨words[1]!.toNat, jobs, limits.1, length.symm, rfl, ?_, ?_⟩
  · simpa [length] using limits.2
  · simpa [terminal] using records

theorem accepted_iff (words : Array UInt64) :
    (readInput words).status = 0 ↔ ∃ categories jobs, Input words categories jobs := by
  constructor
  · exact input_sound words
  · rintro ⟨categories, jobs, encoded⟩
    rw [input_complete words categories jobs encoded]

#print axioms accepted_iff

end Project.Beck.ExactEncoding
