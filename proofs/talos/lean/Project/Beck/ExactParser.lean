import Project.Beck.ExactLoop
import Project.Beck.Parser

namespace Project.Beck.ExactParser

open LeanExe.Examples.BeckExact
open LeanExe.Examples.Beck (Input ParseState readJobs)

theorem accepted_data (words : Array UInt64) (accepted : (readInput words).status = 0) :
    ∃ out : ParseState, readJobs words[0]!.toNat words words[1]!.toNat ⟨2, 0, #[]⟩ = some out ∧
      out.position = words.size ∧
      readInput words = ⟨0, words[0]!.toNat, words[1]!.toNat, out.overlap, out.incidence⟩ := by
  unfold readInput at accepted
  split at accepted
  · exact absurd accepted (by decide)
  rename_i header
  dsimp only at accepted
  split at accepted
  · exact absurd accepted (by decide)
  rename_i jobs
  split at accepted
  · exact absurd accepted (by decide)
  rename_i address
  split at accepted
  · exact absurd accepted (by decide)
  rename_i out parsed
  split at accepted
  · exact absurd accepted (by decide)
  rename_i terminal
  refine ⟨out, parsed, by simpa using terminal, ?_⟩
  simp [readInput, header, jobs, address, parsed, terminal]

theorem accepted_valid (words : Array UInt64) (accepted : (readInput words).status = 0) :
    Parser.Valid (readInput words).jobs (readInput words).categories
      ⟨words.size, (readInput words).overlap, (readInput words).incidence⟩ := by
  obtain ⟨out, parsed, terminal, result⟩ := accepted_data words accepted
  rw [result]
  have valid := Parser.readJobs_valid words[0]!.toNat 0 words[1]!.toNat words _ out
    (Parser.initial words[1]!.toNat) parsed
  have state : ParseState.mk words.size out.overlap out.incidence = out := by rw [← terminal]
  simpa [state] using valid

theorem accepted_input (words : Array UInt64) (accepted : (readInput words).status = 0) :
    ExactLoop.InputValid (readInput words) := by
  have valid := accepted_valid words accepted
  refine ⟨?_, fun job category => valid.binary job.val job.isLt category.val category.isLt, ?_⟩
  · obtain ⟨out, _, _, result⟩ := accepted_data words accepted
    rw [result]
    exact (UInt64.toNat_lt_size words[0]!).le
  · intro job
    simpa [Parser.degree, ExactCounting.members] using valid.overlap job.val job.isLt

#print axioms accepted_input

end Project.Beck.ExactParser
