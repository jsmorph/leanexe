import Project.Beck.ExecutionMembershipValidate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def membershipMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 0 with
  | some (.i64 count) => count.toNat
  | _ => 0

def membershipInv (initial : Store Unit) (heap : Heap) (count position categories : Nat)
    (wordsPointer : UInt64) (words out : Array UInt64) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap left cursor node row internal saved tail,
    currentHeap.At store ∧ currentHeap.OwnsWords store node row ∧ heap.Frame initial currentHeap store ∧
    (internal = 0 ∨ internal = node.root ∧ FreshFor heap node) ∧ node.root ≠ wordsPointer ∧
    row.size = categories ∧ readMemberships left words cursor categories row = some out ∧
    left ≤ count ∧ cursor + left = position + count ∧
    OutputBudget store currentHeap (membershipBytes left categories + remaining) pageLimit Project.Beck.«module» ∧
    frame = membershipFrame left cursor categories wordsPointer wordsPointer node.root internal saved tail

def membershipDone (initial : Store Unit) (heap : Heap) (position categories : Nat)
    (wordsPointer : UInt64) (out : Array UInt64) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap node internal saved tail,
    currentHeap.At store ∧ currentHeap.OwnsWords store node out ∧ heap.Frame initial currentHeap store ∧
    OutputBudget store currentHeap remaining pageLimit Project.Beck.«module» ∧
    frame = membershipFrame 0 position categories wordsPointer wordsPointer node.root internal saved tail

set_option maxRecDepth 2048 in
theorem membership_guard_shape : membershipBody =
    [.localGet 0, .constI64 0, .eqI64, .eqz,
      .iff 0 1 [.localGet 12, .constI64 0, .eqI64] [.const 0] [] [.i32], .eqz, .br_if 1] ++
      membershipBody.drop 7 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem membershipLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (count position categories : Nat) (wordsPointer : UInt64) (node : FreeNode)
    (saved : MemberSetSaved) (tail : MembershipTail) (words row out : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node row)
    (wordsAt : UInt64Array.At initial wordsPointer words)
    (wordsProtected : heap.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (inputDifferent : node.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (countBound : count ≤ 8) (categoryBound : categories ≤ 8)
    (rowSize : row.size = categories) (inputBound : position + count ≤ words.size)
    (accepted : readMemberships count words position categories row = some out)
    (budget : OutputBudget initial heap (membershipBytes count categories + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node out →
      heap.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ internal saved tail, wp Project.Beck.«module» rest Q final
        (membershipFrame 0 (position + count) categories wordsPointer wordsPointer node.root internal saved tail) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 membershipBody]] ++ rest) Q initial
      (membershipFrame count position categories wordsPointer wordsPointer node.root 0 saved tail) env := by
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ membershipBody
    (membershipInv initial heap count position categories wordsPointer words out remaining pageLimit)
    (membershipDone initial heap (position + count) categories wordsPointer out remaining pageLimit) membershipMeasure
  · rintro store frame ⟨currentHeap, left, cursor, currentNode, currentRow, internal, saved', tail', _, _, _, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨currentHeap, currentNode, internal, saved', tail', _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, count, position, node, row, 0, saved, tail, valid, owned, Heap.Frame.refl heap initial,
      Or.inl rfl, inputDifferent, rowSize, accepted, Nat.le_refl _, rfl, budget, rfl⟩
  · rintro store frame ⟨currentHeap, left, cursor, currentNode, currentRow, internal, saved', tail',
      currentValid, currentOwned, preserved, active, different, currentSize, currentAccepted, leftBound, cursorEq, currentBudget, rfl⟩
    rw [membership_guard_shape]
    generalize codeEq : membershipBody.drop 7 = code
    cases left with
    | zero =>
      have resultEq : currentRow = out := by simpa only [readMemberships, Option.some.injEq] using currentAccepted
      have cursorResult : cursor = position + count := by omega
      simp only [List.cons_append, List.nil_append, membershipFrame, membershipParams, memberSetPrefix,
        membershipSaved, membershipTail, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
      wp_fixed_frame
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil, BlockLoop.stepPost]
      refine ⟨currentHeap, currentNode, internal, saved', tail', currentValid, ?_, preserved, ?_, ?_⟩
      · simpa only [resultEq] using currentOwned
      · simpa only [membershipBytes, Nat.zero_mul, Nat.zero_add] using currentBudget
      · simpa only [membershipFrame, membershipParams, memberSetPrefix, membershipSaved, membershipTail,
          Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte, cursorResult,
          List.cons_append, List.nil_append]
    | succ left =>
      have leftFit : left + 1 < UInt64.size := by change left + 1 < 18446744073709551616; omega
      have nonzero : (left + 1).toUInt64 ≠ 0 := by
        intro equal
        have word := congrArg UInt64.toNat equal
        simp only [UInt64.toNat_ofNat_of_lt' leftFit, UInt64.toNat_zero] at word
        omega
      obtain ⟨categoryInside, entryZero, nextAccepted⟩ := readMemberships_some_step left words currentRow out cursor categories currentAccepted
      simp only [List.cons_append, List.nil_append, membershipFrame, membershipParams, memberSetPrefix,
        membershipSaved, membershipTail, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
      wp_fixed_frame [nonzero]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil]
      rw [← codeEq]
      apply membershipValidate_exact env initial store heap currentHeap left cursor categories wordsPointer wordsPointer internal currentNode
        saved' tail' words currentRow (membershipBytes left categories + remaining) pageLimit
        currentValid currentOwned (preserved.words wordsProtected wordsAt) (by omega) preserved active different ownerNonzero
        (by omega) currentSize categoryInside entryZero
        (by simpa only [membershipBytes_succ, currentSize, Nat.add_assoc] using currentBudget)
      intro final finalHeap finalNode finalValid finalOwned finalFrame fresh finalBudget finalSaved finalTail
      change membershipInv initial heap count position categories wordsPointer words out remaining pageLimit final _ ∧ _
      refine ⟨⟨finalHeap, left, cursor + 1, finalNode, currentRow.set! words[cursor]!.toNat 1, finalNode.root,
        finalSaved, finalTail, finalValid, finalOwned, finalFrame, Or.inr ⟨rfl, fresh⟩,
        fresh.pointer_ne wordsPointer words.size wordsProtected (by have := finalOwned.buffer.capacity; omega) finalOwned.buffer.rootBound,
        by simpa using currentSize, nextAccepted, by omega, by omega, finalBudget, rfl⟩, ?_⟩
      simp only [membershipMeasure, membershipFrame, membershipParams, Locals.get, List.length,
        List.getElem?_cons_zero, Nat.reduceAdd, Nat.reduceLT, reduceIte,
        UInt64.toNat_ofNat_of_lt' leftFit, UInt64.toNat_ofNat_of_lt' (show left < UInt64.size by omega)]
      omega
  · rintro final frame ⟨finalHeap, finalNode, internal, finalSaved, finalTail, finalValid, finalOwned, finalFrame, finalBudget, rfl⟩
    exact next final finalHeap finalNode finalValid finalOwned finalFrame finalBudget internal finalSaved finalTail

#print axioms membershipLoop_exact

end Project.Beck.Execution
