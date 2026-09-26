import Project.Beck.ExecutionJobFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobReadSaved (members position : Nat) (rowPointer : UInt64) (saved : JobSaved) (index : Fin 43) : Value :=
  match index.val with
  | 8 => .i64 members.toUInt64
  | 9 => .i64 position.toUInt64
  | 21 => .i64 rowPointer
  | _ => saved index

def jobReadFrame (count categories members : Nat) (wordsPointer incidencePointer rowPointer internal : UInt64)
    (state : ParseState) (saved : JobSaved) (tail : JobTail) : Locals :=
  jobFrame count categories wordsPointer incidencePointer internal state
    (jobReadSaved members (state.position + 1) rowPointer saved) tail

def jobNextState (state : ParseState) (members : Nat) (row : Array UInt64) : ParseState :=
  ⟨state.position + 1 + members, max state.overlap members, state.incidence ++ row⟩

def jobAppendSaved (state : ParseState) (members : Nat) (rowPointer : UInt64) (saved : JobSaved) (index : Fin 43) : Value :=
  if index.val = 23 then .i64 (state.position + 1 + members).toUInt64
  else if index.val = 24 then .i64 (max state.overlap members).toUInt64
  else jobReadSaved members (state.position + 1) rowPointer saved index

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem jobPrepareAppend_exact (env : HostEnv Unit) (initial : Store Unit) (count categories members : Nat)
    (wordsPointer incidencePointer rowPointer internal : UInt64) (state : ParseState) (row : Array UInt64)
    (saved : JobSaved) (tail : JobTail)
    (incidenceAt : UInt64Array.At initial incidencePointer state.incidence) (rowAt : UInt64Array.At initial rowPointer row)
    (positionFit : state.position + 1 + members < UInt64.size) (overlapFit : state.overlap < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (jobAppendFrame (jobParams count categories wordsPointer incidencePointer state)
        (jobSaved internal (jobAppendSaved state members rowPointer saved)) incidencePointer rowPointer state.incidence.size row.size
        (tail 7) (tail 8) (tail 9) (tail 10) (tail 11) (tail 12) (tail 13) (tail 14) (tail 15) (tail 16)) env) :
    wp Project.Beck.«module» (jobAccepted.take 41 ++ rest) Q initial
      (jobReadFrame count categories members wordsPointer incidencePointer rowPointer internal state saved tail) env := by
  have memberFit : members < UInt64.size := by omega
  have guard : ¬(state.position + 1).toUInt64 + members.toUInt64 < (state.position + 1).toUInt64 :=
    CheckedNatAdd.guard_of_fits (state.position + 1) members positionFit
  have addition : (state.position + 1).toUInt64 + members.toUInt64 = (state.position + 1 + members).toUInt64 :=
    (UInt64.ofNat_add _ _).symm
  have sumGuard : ¬(state.position + 1 + members).toUInt64 < (state.position + 1).toUInt64 := by
    rw [← addition]
    exact guard
  have leftBound : incidencePointer.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [incidenceAt.pointerAddress_toNat]
    have := incidenceAt.2.1
    omega
  have rightBound : rowPointer.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [rowAt.pointerAddress_toNat]
    have := rowAt.2.1
    omega
  by_cases smaller : state.overlap ≤ members
  all_goals
    have wordOrder : (state.overlap.toUInt64 ≤ members.toUInt64) = (state.overlap ≤ members) := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' overlapFit, UInt64.toNat_ofNat_of_lt' memberFit]
    simp only [jobAccepted, jobEligible, jobInBounds, jobBody, func5, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.take, List.cons_append, List.nil_append,
      jobReadFrame, jobFrame, jobParams, jobReadSaved, jobPrefix, jobSaved, jobTail,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
    repeat' ((try wp_fixed_frame [guard, addition, sumGuard, wordOrder, smaller, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [guard, addition, sumGuard, wordOrder, smaller, List.take, List.drop, List.append_nil]
    rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
    simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr leftBound, reduceIte, incidenceAt.lengthRead]
    rw [← Memory.toUInt32_eq_ofNat]
    simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr rightBound, reduceIte, rowAt.lengthRead]
    wp_fixed_frame [UInt64.mul_one, ← UInt64.ofNat_add]
    simpa only [jobAppendFrame, jobParams, jobPrefix, jobSaved, jobAppendSaved, jobReadSaved,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
      List.cons_append, List.nil_append, max_def, smaller, Nat.toUInt64] using next

#print axioms jobPrepareAppend_exact

end Project.Beck.Execution
