import Project.Beck.ExecutionJobRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem readJobs_some_step (count categories : Nat) (words : Array UInt64) (state out : ParseState)
    (accepted : readJobs (count + 1) words categories state = some out) :
    state.position < words.size ∧ words[state.position]!.toNat ≤ categories ∧
    state.position + 1 + words[state.position]!.toNat ≤ words.size ∧
    ∃ row, readMemberships words[state.position]!.toNat words (state.position + 1) categories (Array.replicate categories 0) = some row ∧
      readJobs count words categories
        ⟨state.position + 1 + words[state.position]!.toNat, max state.overlap words[state.position]!.toNat, state.incidence ++ row⟩ = some out := by
  simp only [readJobs] at accepted
  split at accepted
  · contradiction
  rename_i positionBound
  split at accepted
  · contradiction
  rename_i valid
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at valid
  split at accepted
  · contradiction
  rename_i row rowRead
  exact ⟨by omega, valid.1, valid.2, row, rowRead, accepted⟩

abbrev JobTail := Fin 17 → UInt64

def jobParams (count categories : Nat) (wordsPointer rowPointer : UInt64) (state : ParseState) (rowOwner : UInt64 := rowPointer) : List Value :=
  [.i64 count.toUInt64, .i64 wordsPointer, .i64 wordsPointer, .i64 categories.toUInt64,
    .i64 state.position.toUInt64, .i64 state.overlap.toUInt64, .i64 rowOwner, .i64 rowPointer]

def jobSaved (internal : UInt64) (saved : JobSaved) (index : Fin 43) : Value :=
  if index.val = 0 then .i64 internal else if index.val = 1 ∨ index.val = 7 then .i64 0 else saved index

def jobTail (tail : JobTail) : List Value :=
  [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3), .i64 (tail 4), .i64 (tail 5),
    .i64 (tail 6), .i64 (tail 7), .i64 (tail 8), .i64 (tail 9), .i64 (tail 10), .i64 (tail 11),
    .i64 (tail 12), .i64 (tail 13), .i64 (tail 14), .i64 (tail 15), .i64 (tail 16)]

def jobFrame (count categories : Nat) (wordsPointer rowPointer internal : UInt64)
    (state : ParseState) (saved : JobSaved) (tail : JobTail) (rowOwner : UInt64 := rowPointer) : Locals :=
  { params := jobParams (rowOwner := rowOwner) count categories wordsPointer rowPointer state
    locals := jobPrefix (jobSaved internal saved) ++ jobTail tail }

def jobFrameLocal (internal : UInt64) (saved : JobSaved) (tail : JobTail) (index : Fin 60) : Value :=
  if h : index.val < 43 then jobSaved internal saved ⟨index.val, h⟩
  else .i64 (tail ⟨index.val - 43, by omega⟩)

theorem jobFrame_locals {rowOwner : UInt64} (count categories : Nat) (wordsPointer rowPointer internal : UInt64)
    (state : ParseState) (saved : JobSaved) (tail : JobTail) :
    (jobFrame (rowOwner := rowOwner) count categories wordsPointer rowPointer internal state saved tail).locals =
      List.ofFn (jobFrameLocal internal saved tail) := rfl

theorem job_local_read (frame : Locals) (index : Nat) (value : Value)
    (params : frame.params.length = 8) (locals : frame.locals.length = 60)
    (inside : index < 60) (read : frame.get (index + 8) = some value) : frame.locals[index]! = value := by
  have indexBound : index < frame.locals.length := by omega
  have read' : frame.locals[index]? = some value := by
    simpa [Locals.get, params, locals, show ¬index + 8 < 8 by omega,
      show index + 8 < 8 + 60 by omega, Nat.add_sub_cancel] using read
  simpa only [getElem?_pos frame.locals index indexBound, getElem!_pos frame.locals index indexBound,
    Option.some.injEq] using read'

theorem jobFrame_reconstruct {rowOwner : UInt64} (frame : Locals) (count categories : Nat)
    (wordsPointer rowPointer internal : UInt64) (state : ParseState) (tail : JobTail)
    (params : frame.params = jobParams (rowOwner := rowOwner) count categories wordsPointer rowPointer state)
    (locals : frame.locals.length = 60) (values : frame.values = [])
    (r8 : frame.get 8 = some (.i64 internal)) (r9 : frame.get 9 = some (.i64 0)) (r15 : frame.get 15 = some (.i64 0))
    (tailReads : ∀ index : Fin 17, frame.get (index.val + 51) = some (.i64 (tail index))) :
    frame = jobFrame (rowOwner := rowOwner) count categories wordsPointer rowPointer internal state (fun k => frame.locals[k.val]!) tail := by
  have paramsLength : frame.params.length = 8 := by simp [params, jobParams]
  have a := job_local_read frame 0 (.i64 internal) paramsLength locals (by decide) r8
  have b := job_local_read frame 1 (.i64 0) paramsLength locals (by decide) r9
  have c := job_local_read frame 7 (.i64 0) paramsLength locals (by decide) r15
  apply Frame.ext frame _ params _ values
  rw [jobFrame_locals]
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [jobFrameLocal]
    split_ifs with lower
    · simp only [jobSaved]
      split_ifs with zero small
      · have equal : i = 0 := zero
        subst i
        simpa only [getElem!_pos frame.locals 0 hi] using a
      · rcases small with one | seven
        · have equal : i = 1 := one
          subst i
          simpa only [getElem!_pos frame.locals 1 hi] using b
        · have equal : i = 7 := seven
          subst i
          simpa only [getElem!_pos frame.locals 7 hi] using c
      · simp [getElem!_pos frame.locals i hi]
    · have upper : i < 60 := by omega
      have read := tailReads ⟨i - 43, by omega⟩
      have address : i - 43 + 51 = i + 8 := by omega
      simp only [address] at read
      simpa only [getElem!_pos frame.locals i hi] using job_local_read frame i _ paramsLength locals upper read

#print axioms readJobs_some_step
#print axioms jobFrame_reconstruct

end Project.Beck.Execution
