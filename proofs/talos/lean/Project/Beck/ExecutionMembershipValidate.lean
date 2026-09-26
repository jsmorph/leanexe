import Project.Beck.ExecutionMembershipFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipBadCategory : Wasm.Program :=
  match (membershipBody[21]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def membershipDuplicate : Wasm.Program :=
  match (membershipInRange[24]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 2048 in
theorem membership_validate_shape : membershipBody.drop 7 =
    [.localGet 2, .localSet 31, .localGet 3, .localSet 32] ++ CheckedArrayGet.checkedGetCore 31 32 ++
      [.localSet 13, .localGet 4, .localGet 13, .leUI64,
        .iff 0 0 membershipBadCategory membershipInRange, .br 0] := rfl

set_option maxRecDepth 2048 in
theorem membership_range_shape : membershipInRange =
    [.localGet 6, .localSet 31, .localGet 13, .localSet 32] ++ CheckedArrayGet.checkedGetCore 31 32 ++
      [.constI64 0, .eqI64, .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
        .constI64 0, .eqI64, .eqz, .eqz, .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
        .constI64 1, .eqI64, .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
        .constI64 0, .eqI64, .eqz, .iff 0 0 membershipDuplicate membershipFresh] := rfl

def membershipReadSaved (category : UInt64) (saved : MemberSetSaved) (index : Fin 24) : Value :=
  if index.val = 6 then .i64 category else saved index

def membershipReadTail (rowPointer category : UInt64) (tail : MembershipTail) (index : Fin 15) : UInt64 :=
  if index.val = 0 then rowPointer else if index.val = 1 then category else tail index

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem membershipValidate_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count position categories : Nat) (wordsOwner wordsPointer internal : UInt64) (oldNode : FreeNode)
    (saved : MemberSetSaved) (tail : MembershipTail) (words row : Array UInt64) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode row)
    (wordsAt : UInt64Array.At middle wordsPointer words) (positionInside : position < words.size)
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsOwner) (ownerNonzero : wordsOwner ≠ 0)
    (bound : row.size ≤ 56) (rowSize : row.size = categories)
    (categoryInside : words[position]!.toNat < categories) (freshEntry : row[words[position]!.toNat]! = 0)
    (budget : OutputBudget middle current (48 + 8 * (row.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final →
      finalHeap.OwnsWords final node (row.set! words[position]!.toNat 1) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Break 0 final
        (membershipFrame count (position + 1) categories wordsOwner wordsPointer node.root node.root saved tail))) :
    wp Project.Beck.«module» (membershipBody.drop 7) Q middle
      (membershipFrame (count + 1) position categories wordsOwner wordsPointer oldNode.root internal saved tail) env := by
  have categoryInside' : words[position].toNat < row.size := by simpa only [getElem!_pos words position positionInside, rowSize] using categoryInside
  have entryZero : row[words[position].toNat] = 0 := by
    simpa only [getElem!_pos words position positionInside, getElem!_pos row words[position].toNat categoryInside'] using freshEntry
  have categoryFit : categories < UInt64.size := by rw [← rowSize]; exact owned.buffer.values.size_lt
  have guard : ¬categories.toUInt64 ≤ words[position] := by
    change ¬(UInt64.ofNat categories).toNat ≤ words[position].toNat
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt categoryFit]
    have := categoryInside'
    omega
  have positionBound : position + 1 < UInt64.size := by have := wordsAt.size_lt; omega
  rw [membership_validate_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append, membershipFrame, membershipParams,
    memberSetPrefix, membershipSaved, membershipTail, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, or_false, false_or, reduceIte]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 31 32 Project.Beck.«module» env middle _ wordsPointer words position []
    rfl rfl rfl wordsAt positionInside _ _ ?_
  wp_fixed_frame [guard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  rw [membership_range_shape]
  generalize freshCodeEq : membershipFresh = freshCode
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 31 32 Project.Beck.«module» env middle _ oldNode.root row words[position].toNat []
    rfl (by simp [Nat.toUInt64]) rfl owned.buffer.values categoryInside' _ _ ?_
  repeat' ((try wp_fixed_frame [entryZero, List.take, List.drop, List.append_nil]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  wp_fixed_frame [entryZero, List.take, List.drop, List.append_nil]
  rw [← freshCodeEq]
  apply membershipFresh_exact env initial middle original current count position categories words[position].toNat
    wordsOwner wordsPointer internal oldNode (membershipReadSaved words[position] saved)
    (membershipReadTail oldNode.root words[position] tail) row remaining pageLimit
    valid owned preserved active inputDifferent ownerNonzero bound categoryInside' positionBound
    (by simp [membershipReadSaved, Nat.toUInt64]) budget
  intro final finalHeap node finalValid finalOwned finalFrame fresh finalBudget saved' tail'
  simp only [membershipFrame, wp_simp, List.take, List.drop, List.append_nil]
  simpa only [getElem!_pos words position positionInside, membershipFrame] using
    next final finalHeap node finalValid (by simpa only [getElem!_pos words position positionInside] using finalOwned)
      finalFrame fresh finalBudget saved' tail'

#print axioms membershipValidate_exact

end Project.Beck.Execution
