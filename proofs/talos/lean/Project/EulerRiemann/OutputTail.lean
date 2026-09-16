import Project.EulerRiemann.OutputAppendExecute
import Project.EulerRiemann.OutputReturn
import Project.EulerRiemann.OutputBudget

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputTailProgram : Wasm.Program := func99.drop 185

set_option maxRecDepth 2048 in
theorem output_tail_shape : outputTailProgram = outputHeaderProgram ++ outputAppendProgram true ++
    outputReleaseProgram 26 33 ++ outputReturnProgram := rfl

theorem output_tail_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fields : FreeNode) (words : Array UInt64) (n time status : UInt64) (spare pageLimit : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 42 57)
    (hN : frame.get 0 = some (.i64 n)) (hTime : frame.get 1 = some (.i64 time))
    (hStatus : frame.get 2 = some (.i64 status))
    (hOwnerLocal : frame.get 26 = some (.i64 fields.root)) (hPointerLocal : frame.get 27 = some (.i64 fields.root))
    (hHeap : heap.At store) (hOwner : heap.OwnsWords store fields words) (hSize : words.size ≤ 1280000)
    (hBudget : OutputBudget store heap (8 * words.size + 176 + spare) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final finalHeap target result,
      finalHeap.At final → finalHeap.OwnsWords final target (outputHeaderWords n time status ++ words) →
      OutputBudget final finalHeap spare pageLimit → result.values = [.i64 target.root, .i64 target.root] →
      wp module rest Q final result env) :
    wp module (outputTailProgram ++ rest) Q store frame env := by
  have hBumpH := hBudget.bump 40 (by change 48 + 40 ≤ 8 * words.size + 176 + spare; omega)
  let heapH := heap.allocate 40
  let header := allocatedNode heap.top 40 heap.nodes
  have hHeaderSize : (outputHeaderWords n time status).size = 4 := rfl
  let need := normalizedCapacity (UInt64.ofNat (4 + words.size)) 1
  have hNeed : need.toNat = 8 * (4 + words.size + 1) := output_word_capacity (4 + words.size) (by omega)
  rw [output_tail_shape]
  simp only [List.append_assoc]
  apply output_header_spec env store heap frame n time status hParams hLocals hValues hScratch
    hN hTime hStatus hHeap
    (by intro hNone; have h := hBumpH hNone; exact ⟨by simpa [Nat.add_assoc] using h.1, h.2⟩)
    (hBudget.pages.trans hBudget.pageLimitBound)
  intro storeH frameH hHeapH hHeaderH hWritesH hParamsEq hLocalsH hValuesH hScratchH hRootH hPresH
  have hParamsH : frameH.params.length = 5 := (congrArg List.length hParamsEq).trans hParams
  have hBudgetH : OutputBudget storeH heapH (8 * words.size + 88 + spare) pageLimit :=
    hBudget.allocated 40 1 _ (by change 48 + 40 + (8 * words.size + 88 + spare) ≤ 8 * words.size + 176 + spare; omega) hWritesH
  have hFieldsH : heapH.OwnsWords storeH fields words :=
    hOwner.arrayWritten 40 1 4 hHeap (by decide) (fun hNone => (hBumpH hNone).1.le) hWritesH
  have hFieldsPointer : frameH.get 27 = some (.i64 fields.root) := (hPresH 27 (by decide)).trans hPointerLocal
  have hFieldsOwner : frameH.get 26 = some (.i64 fields.root) := (hPresH 26 (by decide)).trans hOwnerLocal
  have hBumpR := hBudgetH.bump need (by rw [hNeed]; omega)
  have hSep := hFieldsH.allocation_disjoint need (fun hNone => (hBumpR hNone).1.le)
  let heapR := heapH.allocate need
  let target := allocatedNode heapH.top need heapH.nodes
  apply output_append_spec true env storeH heapH frameH header fields (outputHeaderWords n time status) words
    hParamsH hLocalsH hValuesH hScratchH hRootH hFieldsPointer hHeapH hHeaderH hFieldsH
    (by rw [hHeaderSize]; omega) (by simpa only [hHeaderSize] using hBumpR)
    (hBudgetH.pages.trans hBudgetH.pageLimitBound)
  dsimp only
  intro storeR frameR hHeapR hHeaderR hFieldsR hResultR hWritesR hParamsR hLocalsR hValuesR hScratchR
    hOwnerR hPointerR hPresR
  simp only [hHeaderSize] at hHeapR hHeaderR hFieldsR hResultR hWritesR hOwnerR hPointerR
  have hBudgetR : OutputBudget storeR heapR spare pageLimit :=
    hBudgetH.allocated need 1 spare (by rw [hNeed]; omega) hWritesR
  have hFieldsGet : frameR.get 26 = some (.i64 fields.root) :=
    (hPresR 26 (by decide) (by decide) (by decide)).trans hFieldsOwner
  have hRootBound := hFieldsR.buffer.rootBound
  have hRoot32 : fields.root.toNat ≤ 4294967296 := by
    have := hFieldsR.buffer.addressBound
    omega
  have hFinalOwner := hResultR.released fields hRootBound hRoot32 (regionsDisjoint_symm hSep)
  let released := resultFrame frameR 33 (heapR.frees + 1)
  have hReleasedParams : released.params.length = 5 := hParamsR
  have hReleasedLocals : released.locals.length = 52 := by
    simpa only [released, resultFrame_locals_length] using hLocalsR
  have hReturnOwner : released.get 31 = some (.i64 target.root) :=
    (resultFrame_get_ne frameR 33 31 _ (by omega) (by decide)).trans hOwnerR
  have hReturnPointer : released.get 32 = some (.i64 target.root) :=
    (resultFrame_get_ne frameR 33 32 _ (by omega) (by decide)).trans hPointerR
  apply output_release_spec env storeR heapR frameR fields words 26 33 hHeapR hFieldsR hValuesR hFieldsGet
    (by omega) (by simp [Locals.validIndex, hParamsR, hLocalsR])
  intro hFinalHeap
  apply output_return_spec env (heapR.releaseStore storeR fields) released target.root
    hReleasedParams hReleasedLocals rfl hReturnOwner hReturnPointer
  exact hNext _ _ target (outputReturnFrame released target.root) hFinalHeap hFinalOwner (hBudgetR.released fields) rfl

#print axioms output_tail_shape
#print axioms output_tail_spec

end Project.EulerRiemann.Execution
