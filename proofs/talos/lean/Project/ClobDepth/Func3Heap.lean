import Project.ClobDepth.FoundHeap
import Project.ClobDepth.Func3

namespace Project.ClobDepth.Func3Heap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Properties Project.ClobDepth.Representation
  Project.ClobDepth.HeapProof Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem func3_spec (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (owner price qty : UInt64) (source : FreeNode) (levels : List LevelL)
    (hLength : levels.length < 4294967296) (hHeap : heap.At st)
    (hOwner : OwnsLevels heap st source levels)
    (hFit32 : heap.top.toNat + 48 + fixedArrayBytes (levels.length + 1) 2 < 4294967296)
    (hFit : heap.top.toNat + 48 + fixedArrayBytes (levels.length + 1) 2 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ st1, AllocatedResult st heap (Func3.capacity levels price qty) st1
        (addLevelL levels price qty) →
      ∀ final, Func3.ResultAt final (allocatedRoot heap.top (Func3.capacity levels price qty) heap.nodes) →
      wp «module» rest Q st1 final env) :
    wp «module» (Project.ClobDepth.func3 ++ rest) Q st
      (Scan.entryFrame owner source.root price qty) env := by
  have hNeed (count : Nat) (hCount : count ≤ levels.length + 1) :
      (fixedArrayBytesU count 2).toNat = fixedArrayBytes count 2 := by
    apply fixedArrayBytesU_toNat
    · rw [size_eq]; omega
    · decide
    · unfold fixedArrayBytes; rw [size_eq]; omega
  have hResultProg : Entry.resultProg = [.localGet 12, .localGet 13] := rfl
  rw [Entry.func3_decomposition, hResultProg]
  simp only [List.append_assoc]
  apply Scan.scanProg_spec levels hLength hOwner.buffer.contents.2
  · intro hIndex f4 f5
    simp only [Scan.outcomeFrame, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    rw [show Entry.missingProg = Entry.missingProg ++ ([] : Program) from (List.append_nil _).symm]
    apply MissingHeap.missingProg_spec env st heap owner price qty source levels f4 f5
      hLength hHeap hOwner (by rwa [hNeed _ (le_refl _)])
      (by rwa [hNeed _ (le_refl _)]) hPages
    intro st1 hResult final hLocals
    have hAdd := addLevelL_of_priceIdx_none levels price qty hIndex
    have hCap : Func3.capacity levels price qty = fixedArrayBytesU (levels.length + 1) 2 := by
      simp [Func3.capacity, hAdd]
    rw [hCap, hAdd] at hNext
    have hL := hLocals.locals
    have hOwner' := getElem_of_some hLocals.owner
    have hPointer' := getElem_of_some hLocals.pointer
    simp (config := { maxSteps := 1000000 }) [wp_simp,
      hLocals.params, hLocals.locals, hOwner', hPointer', Locals.get, List.take, List.drop]
    exact hNext st1 hResult _ ⟨hLocals.params, hLocals.locals, rfl⟩
  · intro i hIndex
    simp only [Scan.outcomeFrame, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [show Entry.foundProg = Entry.foundProg ++ ([] : Program) from (List.append_nil _).symm]
    apply FoundHeap.foundProg_spec env st heap owner price qty source levels i hLength hIndex
      hHeap hOwner
      (by rw [hNeed _ (by omega)]; unfold fixedArrayBytes at *; omega)
      (by rw [hNeed _ (by omega)]; unfold fixedArrayBytes at *; omega) hPages
    intro st1 hResult final hLocals
    have hAdd := addLevelL_of_priceIdx_some levels price qty i hIndex
    have hCap : Func3.capacity levels price qty = fixedArrayBytesU levels.length 2 := by
      simp [Func3.capacity, hAdd]
    rw [hCap, hAdd] at hNext
    have hL := hLocals.locals
    have hOwner' := getElem_of_some hLocals.owner
    have hPointer' := getElem_of_some hLocals.pointer
    simp (config := { maxSteps := 1000000 }) [wp_simp,
      hLocals.params, hLocals.locals, hOwner', hPointer', Locals.get, List.take, List.drop]
    exact hNext st1 hResult _ ⟨hLocals.params, hLocals.locals, rfl⟩

theorem func3_terminates (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (owner price qty : UInt64) (source : FreeNode) (levels : List LevelL)
    (hLength : levels.length < 4294967296) (hHeap : heap.At st)
    (hOwner : OwnsLevels heap st source levels)
    (hFit32 : heap.top.toNat + 48 + fixedArrayBytes (levels.length + 1) 2 < 4294967296)
    (hFit : heap.top.toNat + 48 + fixedArrayBytes (levels.length + 1) 2 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) :
    TerminatesWith env «module» 3 st [.i64 qty, .i64 price, .i64 source.root, .i64 owner]
      (fun st1 vs => AllocatedResult st heap (Func3.capacity levels price qty) st1
          (addLevelL levels price qty) ∧
        vs = [.i64 (allocatedRoot heap.top (Func3.capacity levels price qty) heap.nodes),
          .i64 (allocatedRoot heap.top (Func3.capacity levels price qty) heap.nodes)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func3 _ st (Scan.entryFrame owner source.root price qty) env
    rw [show Project.ClobDepth.func3 = Project.ClobDepth.func3 ++ ([] : Program) from (List.append_nil _).symm]
    apply func3_spec env st heap owner price qty source levels hLength hHeap hOwner hFit32 hFit hPages
    intro st1 hResult final hFinal
    simp [wp_simp, func3Def, Function.numParams, hFinal.values]
    exact hResult

#print axioms func3_terminates
end Project.ClobDepth.Func3Heap
