import Project.TinyGpt2Checked.OutputAllocateExec
import Project.TinyGpt2Infer.OutputPrepare
import Project.ProofKit.ScalarFrame
import Project.ProofKit.FixedArraySearchProjection

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.Runtime Project.ProofKit ArrayPushLayout FixedArrayFold

theorem output_prepare_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (hParams : params.length = 6)
    (hStart : params.length + saved.length = 59)
    (start count : Nat) (allocations retains releases frees previous current capacity' next result : UInt64)
    (hGlobals : initial.globals.globals = OutputMemory.globals start count allocations retains releases frees)
    (hList : FreeListAt initial.mem (freed start count))
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (hLength : (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
      previous current capacity' next result).get 53 = some (.i64 (UInt64.ofNat (count + 1))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous' : UInt64, wp module rest Q
      (OutputMemory.prepare initial start (count + 1) allocations)
      (resultFrame (TinyGpt2Infer.Spec.outputAllocationFrame params saved tail start count previous') 54
        (node start (count + 1)).root) env) :
    wp module ((outputBody.drop 67).take 21 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
        previous current capacity' next result) env := by
  rw [output_prepare_shape]
  simp only [List.append_assoc]
  apply output_allocation_spec env initial params saved tail hStart start count
    allocations retains releases frees previous current capacity' next result
    hGlobals hList hFit hMemory hPages hCap
  intro previous'
  let allocatedFrame := TinyGpt2Infer.Spec.outputAllocationFrame params saved tail start count previous'
  have hRoot : allocatedFrame.get 64 = some (.i64 (node start (count + 1)).root) := by
    have h := FixedArraySearch.frame_get params saved tail (UInt64.ofNat (capacity (count + 1)))
      previous' 0 (UInt64.ofNat (top start (count + 1)))
      ((UInt64.ofNat (top start (count + 1)) - 1) / 65536 + 1)
      (node start (count + 1)).root 5 (by decide)
    simpa only [hStart, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ,
      allocatedFrame, TinyGpt2Infer.Spec.outputAllocationFrame] using h
  have hLength' : allocatedFrame.get 53 = some (.i64 (UInt64.ofNat (count + 1))) := by
    rw [FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 53 (by omega)] at hLength
    change (FixedArraySearch.frame _ _ _ _ _ _ _ _ _).get 53 = _
    rw [FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 53 (by omega)]
    exact hLength
  have hLower : allocatedFrame.params.length ≤ 54 := by simpa only [allocatedFrame, TinyGpt2Infer.Spec.outputAllocationFrame,
    FixedArraySearch.frame, hParams] using (show 6 ≤ 54 by decide)
  have hValid : allocatedFrame.validIndex 54 := by
    simp only [allocatedFrame, TinyGpt2Infer.Spec.outputAllocationFrame, FixedArraySearch.frame, Locals.validIndex,
      List.length_append, List.length_cons, List.length_nil]
    omega
  change wp module ((ScalarTransition.Stmt.assign 54 (.get 64)).program 69 ++
    FixedArrayResult.lengthStoreLocalProgram 54 53 ++ rest) Q _ allocatedFrame env
  apply ScalarTransition.Expr.assign_frame_spec (.get 64) 69 54 allocatedFrame
    (node start (count + 1)).root module env _ rfl hLower hValid
  · simp only [ScalarTransition.Expr.eval, ScalarTransition.State.ofLocals_get, hRoot]
    rfl
  apply FixedArrayResult.lengthStoreLocal_spec module env _ _ (node start (count + 1)).root
    (UInt64.ofNat (count + 1)) 54 53
    (resultFrame_get_result allocatedFrame 54 _ hLower hValid)
    ((resultFrame_get_ne allocatedFrame 54 53 _ hLower (by decide)).trans hLength')
  · have hNode := node_toNat start (count + 1) hFit
    rw [UInt64.toNat_toUInt32, hNode.1, Nat.mod_eq_of_lt
      ((Nat.le_add_right _ _).trans_lt hFit)]
    rw [OutputMemory.allocate_pages initial start (count + 1) allocations hFit hMemory]
    unfold top capacity at hMemory
    omega
  · exact hNext previous'

#print axioms output_prepare_spec
end Project.TinyGpt2Checked.Spec
