import Project.Beck.ExecutionJobEligible

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobOutOfBounds : Wasm.Program :=
  match (jobBody[14]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def jobCountInvalid : Wasm.Program :=
  match (jobInBounds[34]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 2048 in
theorem job_validate_shape : jobBody.drop 7 =
    [.localGet 2, .localSet 51, .localGet 51, .wrapI64, .load64 0, .localGet 4, .leUI64,
      .iff 0 0 jobOutOfBounds jobInBounds, .br 0] := rfl

set_option maxRecDepth 2048 in
theorem job_count_shape : jobInBounds = jobInBounds.take 34 ++ [.iff 0 0 jobCountInvalid jobEligible] := rfl

def jobValidatedTail (position members : Nat) (tail : JobTail) (index : Fin 17) : UInt64 :=
  match index.val with
  | 0 => (position + 1).toUInt64
  | 1 => members.toUInt64
  | 2 => (position + 1 + members).toUInt64
  | _ => tail index

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem jobValidate_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count categories members : Nat) (wordsPointer internal : UInt64) (oldNode : FreeNode)
    (state : ParseState) (words row : Array UInt64) (saved : JobSaved) (tail : JobTail) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode state.incidence)
    (wordsAt : UInt64Array.At middle wordsPointer words)
    (wordsProtected : current.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (memberBound : members ≤ categories) (categoryBound : categories ≤ 8)
    (positionInside : state.position < words.size) (countAt : words[state.position]! = members.toUInt64)
    (inputBound : state.position + 1 + members ≤ words.size) (overlapFit : state.overlap < UInt64.size)
    (accepted : readMemberships members words (state.position + 1) categories (Array.replicate categories 0) = some row)
    (bound : state.incidence.size + row.size ≤ 56)
    (budget : OutputBudget middle current (jobStepBytes members categories state.incidence.size row.size + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (state.incidence ++ row) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Break 0 final
        (jobFrame count categories wordsPointer node.root node.root (jobNextState state members row) saved tail))) :
    wp Project.Beck.«module» (jobBody.drop 7) Q middle
      (jobFrame (rowOwner := rowOwner) (count + 1) categories wordsPointer oldNode.root internal state saved tail) env := by
  have sizeFit := wordsAt.size_lt
  have positionFit : state.position < UInt64.size := positionInside.trans sizeFit
  have nextFit : state.position + 1 < UInt64.size := by omega
  have endFit : state.position + 1 + members < UInt64.size := inputBound.trans_lt sizeFit
  have categoryFit : categories < UInt64.size := by change categories < 18446744073709551616; omega
  have memberFit : members < UInt64.size := memberBound.trans_lt categoryFit
  have positionGuard : ¬words.size.toUInt64 ≤ state.position.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' sizeFit, UInt64.toNat_ofNat_of_lt' positionFit]
    omega
  have memberGuard : ¬categories.toUInt64 < members.toUInt64 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' categoryFit, UInt64.toNat_ofNat_of_lt' memberFit]
    omega
  have inputGuard : ¬UInt64.ofNat words.size < (state.position + 1 + members).toUInt64 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' sizeFit, UInt64.toNat_ofNat_of_lt' endFit]
    omega
  have increment : state.position.toUInt64 + 1 = (state.position + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  have incrementGuard : ¬(state.position + 1).toUInt64 < state.position.toUInt64 := by
    rw [← increment]
    exact CheckedNatAdd.guard_of_fits state.position 1 nextFit
  have addition : (state.position + 1).toUInt64 + members.toUInt64 = (state.position + 1 + members).toUInt64 :=
    (UInt64.ofNat_add _ _).symm
  have additionGuard : ¬(state.position + 1 + members).toUInt64 < (state.position + 1).toUInt64 := by
    rw [← addition]
    exact CheckedNatAdd.guard_of_fits (state.position + 1) members endFit
  have readCount : words[state.position] = members.toUInt64 := by simpa only [getElem!_pos words state.position positionInside] using countAt
  have headerBound : wordsPointer.toUInt32.toNat + 8 ≤ middle.mem.pages * 65536 := by
    rw [wordsAt.pointerAddress_toNat]
    have := wordsAt.2.1
    omega
  rw [job_validate_shape]
  generalize inBoundsEq : jobInBounds = inBoundsCode
  simp only [jobFrame, jobParams, jobPrefix, jobSaved, jobTail, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, or_false, false_or, reduceIte, List.cons_append, List.nil_append]
  wp_fixed_frame
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr headerBound, reduceIte, wordsAt.lengthRead]
  wp_fixed_frame [positionGuard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  rw [← inBoundsEq, job_count_shape]
  generalize eligibleEq : jobEligible = eligibleCode
  simp only [jobInBounds, jobBody, func5, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 51 52 Project.Beck.«module» env middle _ wordsPointer words state.position []
    rfl rfl rfl wordsAt positionInside _ _ ?_
  repeat' ((try wp_fixed_frame [readCount, increment, incrementGuard, addition, additionGuard, memberGuard, inputGuard,
      List.take, List.drop, List.append_nil]) <;>
    (refine wp_iff_cons rfl ?_; simp only [inputGuard, memberGuard, incrementGuard, additionGuard, reduceIte, ne_eq,
      (show (0 : UInt32) ≠ 1 by decide), (show (1 : UInt32) ≠ 0 by decide),
      (show (0 : UInt64) ≠ 1 by decide), (show (1 : UInt64) ≠ 0 by decide),
      not_true_eq_false, not_false_eq_true, eq_self]))
  wp_fixed_frame [readCount, increment, incrementGuard, addition, additionGuard, memberGuard, inputGuard,
    List.take, List.drop, List.append_nil]
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr headerBound, reduceIte, wordsAt.lengthRead]
  repeat' ((try wp_fixed_frame [readCount, increment, incrementGuard, addition, additionGuard, memberGuard, inputGuard,
      List.take, List.drop, List.append_nil]) <;>
    (refine wp_iff_cons rfl ?_; simp only [inputGuard, memberGuard, incrementGuard, additionGuard, reduceIte, ne_eq,
      (show (0 : UInt32) ≠ 1 by decide), (show (1 : UInt32) ≠ 0 by decide),
      (show (0 : UInt64) ≠ 1 by decide), (show (1 : UInt64) ≠ 0 by decide),
      not_true_eq_false, not_false_eq_true, eq_self]))
  wp_fixed_frame [readCount, increment, incrementGuard, addition, additionGuard, memberGuard, inputGuard,
    List.take, List.drop, List.append_nil]
  rw [← eligibleEq]
  apply jobEligible_exact env initial middle original current count categories members wordsPointer internal oldNode state words row saved
    (jobValidatedTail state.position members tail) remaining pageLimit valid owned wordsAt wordsProtected preserved active inputDifferent
    ownerNonzero (by omega) categoryBound inputBound overlapFit accepted bound budget
  intro final finalHeap node finalValid finalOwned finalFrame fresh finalBudget finalSaved finalTail
  simpa only [jobFrame, List.take, List.drop, List.append_nil, wp_simp] using
    next final finalHeap node finalValid finalOwned finalFrame fresh finalBudget finalSaved finalTail

#print axioms jobValidate_exact

end Project.Beck.Execution
