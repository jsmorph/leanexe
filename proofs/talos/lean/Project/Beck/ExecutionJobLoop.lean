import Project.Beck.ExecutionJobValidate
import Project.Beck.Memberships

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobInv (initial : Store Unit) (heap : Heap) (count categories : Nat) (wordsPointer rowOwner : UInt64)
    (words : Array UInt64) (out : ParseState) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap left node state internal owner saved tail,
    currentHeap.At store ∧ currentHeap.OwnsWords store node state.incidence ∧ heap.Frame initial currentHeap store ∧
    (internal = 0 ∨ internal = node.root ∧ FreshFor heap node) ∧ node.root ≠ wordsPointer ∧
    state.position ≤ words.size ∧ state.overlap ≤ 8 ∧ state.incidence.size + left * categories ≤ 48 ∧
    readJobs left words categories state = some out ∧ left ≤ count ∧
    OutputBudget store currentHeap (1520 * left + remaining) pageLimit Project.Beck.«module» ∧
    owner = (if left = count then rowOwner else node.root) ∧
    frame = jobFrame (rowOwner := owner) left categories wordsPointer node.root internal state saved tail

def jobDone (initial : Store Unit) (heap : Heap) (count categories : Nat) (wordsPointer rowOwner : UInt64)
    (out : ParseState) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap node internal saved tail,
    currentHeap.At store ∧ currentHeap.OwnsWords store node out.incidence ∧ heap.Frame initial currentHeap store ∧
    OutputBudget store currentHeap remaining pageLimit Project.Beck.«module» ∧
    frame = jobFrame (rowOwner := if count = 0 then rowOwner else node.root) 0 categories wordsPointer node.root internal out saved tail

set_option maxRecDepth 2048 in
theorem job_guard_shape : jobBody =
    [.localGet 0, .constI64 0, .eqI64, .eqz,
      .iff 0 1 [.localGet 15, .constI64 0, .eqI64] [.const 0] [] [.i32], .eqz, .br_if 1] ++ jobBody.drop 7 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem jobLoop_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (count categories : Nat) (wordsPointer : UInt64) (node : FreeNode)
    (state out : ParseState) (saved : JobSaved) (tail : JobTail) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node state.incidence)
    (wordsAt : UInt64Array.At initial wordsPointer words)
    (wordsProtected : heap.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (inputDifferent : node.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (countBound : count ≤ 6) (categoryBound : categories ≤ 8)
    (positionBound : state.position ≤ words.size) (overlapBound : state.overlap ≤ 8)
    (incidenceBound : state.incidence.size + count * categories ≤ 48)
    (accepted : readJobs count words categories state = some out)
    (budget : OutputBudget initial heap (1520 * count + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node out.incidence →
      heap.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ internal saved tail, wp Project.Beck.«module» rest Q final (jobFrame (rowOwner := if count = 0 then rowOwner else node.root) 0 categories wordsPointer node.root internal out saved tail) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 jobBody]] ++ rest) Q initial
      (jobFrame (rowOwner := rowOwner) count categories wordsPointer node.root 0 state saved tail) env := by
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ jobBody
    (jobInv initial heap count categories wordsPointer rowOwner words out remaining pageLimit)
    (jobDone initial heap count categories wordsPointer rowOwner out remaining pageLimit) membershipMeasure
  · rintro store frame ⟨currentHeap, left, currentNode, currentState, internal, owner, saved', tail', _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨currentHeap, currentNode, internal, saved', tail', _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, count, node, state, 0, rowOwner, saved, tail, valid, owned, Heap.Frame.refl heap initial,
      Or.inl rfl, inputDifferent, positionBound, overlapBound, incidenceBound, accepted, Nat.le_refl _, budget, by simp, rfl⟩
  · rintro store frame ⟨currentHeap, left, currentNode, currentState, internal, owner, saved', tail', currentValid, currentOwned,
      preserved, active, different, currentPosition, currentOverlap, currentSize, currentAccepted, leftBound, currentBudget, ownerEq, rfl⟩
    rw [job_guard_shape]
    generalize codeEq : jobBody.drop 7 = code
    cases left with
    | zero =>
      have resultEq : currentState = out := by simpa only [readJobs, Option.some.injEq] using currentAccepted
      simp only [List.cons_append, List.nil_append, jobFrame, jobParams, jobPrefix, jobSaved, jobTail,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
      wp_fixed_frame
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil, BlockLoop.stepPost]
      refine ⟨currentHeap, currentNode, internal, saved', tail', currentValid, ?_, preserved, ?_, ?_⟩
      · simpa only [resultEq] using currentOwned
      · simpa only [Nat.mul_zero, Nat.zero_add] using currentBudget
      · simp only [jobFrame, jobParams, jobPrefix, jobSaved, jobTail, Fin.coe_ofNat_eq_mod,
          Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte, resultEq, List.cons_append, List.nil_append, ownerEq, eq_comm]
    | succ left =>
      have leftFit : left + 1 < UInt64.size := by change left + 1 < 18446744073709551616; omega
      have nonzero : (left + 1).toUInt64 ≠ 0 := by
        intro equal
        have word := congrArg UInt64.toNat equal
        simp only [UInt64.toNat_ofNat_of_lt' leftFit, UInt64.toNat_zero] at word
        omega
      obtain ⟨positionInside, membersBound, inputBound, row, rowAccepted, nextAccepted⟩ :=
        readJobs_some_step left categories words currentState out currentAccepted
      have rowSize := (Memberships.read_spec words[currentState.position]!.toNat words (currentState.position + 1) categories
        (Array.replicate categories 0) row (Memberships.initial categories) rowAccepted).1.size
      have appendBound : currentState.incidence.size + row.size ≤ 48 := by
        rw [rowSize]
        have := Nat.mul_le_mul_right categories (show 1 ≤ left + 1 by omega)
        omega
      have stepBound := jobStepBytes_bound words[currentState.position]!.toNat categories currentState.incidence.size row.size
        (membersBound.trans categoryBound) categoryBound appendBound
      simp only [List.cons_append, List.nil_append, jobFrame, jobParams, jobPrefix, jobSaved, jobTail,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte]
      wp_fixed_frame [nonzero]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil]
      rw [← codeEq]
      apply jobValidate_exact env initial store heap currentHeap left categories words[currentState.position]!.toNat wordsPointer internal currentNode
        currentState words row saved' tail' (1520 * left + remaining) pageLimit currentValid currentOwned
        (preserved.words wordsProtected wordsAt) (preserved.protects _ _ wordsProtected) preserved active different ownerNonzero
        membersBound categoryBound positionInside (by simp [Nat.toUInt64]) inputBound
        (by change currentState.overlap < 18446744073709551616; omega) rowAccepted (by omega)
        (currentBudget.mono (by omega))
      intro final finalHeap finalNode finalValid finalOwned finalFrame fresh finalBudget finalSaved finalTail
      change jobInv initial heap count categories wordsPointer rowOwner words out remaining pageLimit final _ ∧ _
      refine ⟨⟨finalHeap, left, finalNode, jobNextState currentState words[currentState.position]!.toNat row,
        finalNode.root, finalNode.root, finalSaved, finalTail, finalValid, finalOwned, finalFrame, Or.inr ⟨rfl, fresh⟩,
        fresh.pointer_ne wordsPointer words.size wordsProtected (by have := finalOwned.buffer.capacity; omega) finalOwned.buffer.rootBound,
        inputBound, ?_, ?_, nextAccepted, by omega, finalBudget, by simp [show left ≠ count by omega], rfl⟩, ?_⟩
      · exact max_le currentOverlap (membersBound.trans categoryBound)
      · simp only [jobNextState, Array.size_append, rowSize]
        simp only [Nat.add_mul, Nat.one_mul] at currentSize
        omega
      · simp only [membershipMeasure, jobFrame, jobParams, Locals.get, List.length,
          List.getElem?_cons_zero, Nat.reduceAdd, Nat.reduceLT, reduceIte,
          UInt64.toNat_ofNat_of_lt' leftFit, UInt64.toNat_ofNat_of_lt' (show left < UInt64.size by omega)]
        omega
  · rintro final frame ⟨finalHeap, finalNode, internal, finalSaved, finalTail, finalValid, finalOwned, finalFrame, finalBudget, rfl⟩
    exact next final finalHeap finalNode finalValid finalOwned finalFrame finalBudget internal finalSaved finalTail

#print axioms jobLoop_exact

end Project.Beck.Execution
