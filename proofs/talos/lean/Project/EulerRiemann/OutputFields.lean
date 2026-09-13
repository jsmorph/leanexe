import Project.EulerRiemann.OutputMapExecute
import Project.EulerRiemann.OutputAppendExecute
import Project.EulerRiemann.OutputRelease
import Project.EulerRiemann.OutputBudget

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputFieldsProgram : Wasm.Program := func99.take 185

set_option maxRecDepth 2048 in
theorem output_fields_shape : outputFieldsProgram = outputMapProgram false ++ outputMapProgram true ++
    outputAppendProgram false ++ outputReleaseProgram 13 28 ++ outputReleaseProgram 23 29 := rfl

theorem output_fields_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (source : FreeNode) (grid : Array Traversal.Cell) (pageLimit : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 42 57)
    (hSource : frame.get 4 = some (.i64 source.root))
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid) (hSize : grid.size ≤ 640000)
    (hBudget : OutputBudget store heap (outputBytes grid.size) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final finalHeap fields result,
      finalHeap.At final →
      finalHeap.OwnsWords final fields (outputMapResult false grid ++ outputMapResult true grid) →
      OutputBudget final finalHeap (16 * grid.size + 176) pageLimit →
      result.params.length = 5 → result.locals.length = 52 → result.values = [] →
      I64LocalRange result 42 57 → result.get 26 = some (.i64 fields.root) →
      result.get 27 = some (.i64 fields.root) →
      (∀ index : Nat, index < 5 → result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputFieldsProgram ++ rest) Q store frame env := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 1
  let fieldNeed := normalizedCapacity (UInt64.ofNat (grid.size + grid.size)) 1
  have hNeed : need.toNat = 8 * (grid.size + 1) := output_word_capacity grid.size (by omega)
  have hFieldNeed : fieldNeed.toNat = 8 * (grid.size + grid.size + 1) :=
    output_word_capacity (grid.size + grid.size) (by omega)
  have hBumpD := hBudget.bump need (by rw [hNeed]; unfold outputBytes; omega)
  let heapD := heap.allocate need
  let density := allocatedNode heap.top need heap.nodes
  rw [output_fields_shape]
  simp only [List.append_assoc]
  apply output_map_spec false env store heap frame source grid hParams hLocals hValues hScratch hSource
    hHeap hOwner hSize hBumpD (hBudget.pages.trans hBudget.pageLimitBound)
  dsimp only
  intro storeD frameD hHeapD hGridD hDensityD hWritesD hParamsD hLocalsD hValuesD hScratchD hOwnerD hPointerD hPresD
  have hBudgetD : OutputBudget storeD heapD (40 * grid.size + 288) pageLimit :=
    hBudget.allocated need 1 _ (by rw [hNeed]; unfold outputBytes; omega) hWritesD
  have hSourceD : frameD.get 4 = some (.i64 source.root) :=
    (hPresD 4 (by decide) (Or.inl (by decide)) (by decide) (by decide)).trans hSource
  have hBumpP := hBudgetD.bump need (by rw [hNeed]; omega)
  have hSepDP := hDensityD.allocation_disjoint need (fun hNone => (hBumpP hNone).1.le)
  let heapP := heapD.allocate need
  let pressure := allocatedNode heapD.top need heapD.nodes
  apply output_map_spec true env storeD heapD frameD source grid hParamsD hLocalsD hValuesD hScratchD hSourceD
    hHeapD hGridD hSize hBumpP (hBudgetD.pages.trans hBudgetD.pageLimitBound)
  dsimp only
  intro storeP frameP hHeapP hGridP hPressureP hWritesP hParamsP hLocalsP hValuesP hScratchP hOwnerP hPointerP hPresP
  have hBudgetP : OutputBudget storeP heapP (32 * grid.size + 232) pageLimit :=
    hBudgetD.allocated need 1 _ (by rw [hNeed]; omega) hWritesP
  have hDensityP : heapP.OwnsWords storeP density (outputMapResult false grid) :=
    hDensityD.arrayWritten need 1 grid.size hHeapD hNeed.ge (fun hNone => (hBumpP hNone).1.le) hWritesP
  have hDensityPointer : frameP.get 14 = some (.i64 density.root) :=
    (hPresP 14 (by decide) (Or.inl (by decide)) (by decide) (by decide)).trans hPointerD
  have hDensityOwner : frameP.get 13 = some (.i64 density.root) :=
    (hPresP 13 (by decide) (Or.inl (by decide)) (by decide) (by decide)).trans hOwnerD
  have hBumpF := hBudgetP.bump fieldNeed (by rw [hFieldNeed]; omega)
  have hSepDF := hDensityP.allocation_disjoint fieldNeed (fun hNone => (hBumpF hNone).1.le)
  have hSepPF := hPressureP.allocation_disjoint fieldNeed (fun hNone => (hBumpF hNone).1.le)
  let heapF := heapP.allocate fieldNeed
  let fields := allocatedNode heapP.top fieldNeed heapP.nodes
  apply output_append_spec false env storeP heapP frameP density pressure
    (outputMapResult false grid) (outputMapResult true grid)
    hParamsP hLocalsP hValuesP hScratchP hDensityPointer hPointerP hHeapP hDensityP hPressureP
    (by simp only [outputMapResult, Array.size_map]; omega)
    (by simpa only [outputMapResult, Array.size_map] using hBumpF)
    (hBudgetP.pages.trans hBudgetP.pageLimitBound)
  dsimp only
  intro storeF frameF hHeapF hDensityF hPressureF hFieldsF hWritesF hParamsF hLocalsF hValuesF hScratchF
    hOwnerF hPointerF hPresF
  simp only [outputMapResult, Array.size_map] at hHeapF hDensityF hPressureF hFieldsF hWritesF hOwnerF hPointerF
  have hBudgetF : OutputBudget storeF heapF (16 * grid.size + 176) pageLimit :=
    hBudgetP.allocated fieldNeed 1 _ (by rw [hFieldNeed]; omega) hWritesF
  have hDensityGet : frameF.get 13 = some (.i64 density.root) :=
    (hPresF 13 (by decide) (by decide) (by decide)).trans hDensityOwner
  have hPressureGet : frameF.get 23 = some (.i64 pressure.root) :=
    (hPresF 23 (by decide) (by decide) (by decide)).trans hOwnerP
  have hValidF (index : Nat) (hi : index < 57) : frameF.validIndex index := by
    simpa only [Locals.validIndex, hParamsF, hLocalsF] using hi
  have hDensityRoot := hDensityF.buffer.rootBound
  have hDensity32 : density.root.toNat ≤ 4294967296 := by
    have := hDensityF.buffer.addressBound
    change density.root.toNat + density.capacity.toNat < 4294967296 at this
    omega
  have hPressureAfterD := hPressureF.released density hDensityRoot hDensity32 (regionsDisjoint_symm hSepDP)
  have hFieldsAfterD := hFieldsF.released density hDensityRoot hDensity32 (regionsDisjoint_symm hSepDF)
  let frameAfterD := resultFrame frameF 28 (heapF.frees + 1)
  have hAfterDParams : frameAfterD.params.length = 5 := hParamsF
  have hAfterDLocals : frameAfterD.locals.length = 52 := by
    simpa only [frameAfterD, resultFrame_locals_length] using hLocalsF
  have hAfterDPressure : frameAfterD.get 23 = some (.i64 pressure.root) :=
    (resultFrame_get_ne frameF 28 23 _ (by omega) (by decide)).trans hPressureGet
  apply output_release_spec env storeF heapF frameF density (outputMapResult false grid) 13 28
    hHeapF hDensityF hValuesF hDensityGet (by omega) (hValidF 28 (by decide))
  intro hHeapAfterD
  apply output_release_spec env (heapF.releaseStore storeF density) (heapF.release density) frameAfterD pressure
    (outputMapResult true grid) 23 29 hHeapAfterD hPressureAfterD rfl hAfterDPressure (by omega)
    (by simp [Locals.validIndex, hAfterDParams, hAfterDLocals])
  intro hHeapAfterP
  have hPressureRoot := hPressureAfterD.buffer.rootBound
  have hPressure32 : pressure.root.toNat ≤ 4294967296 := by
    have := hPressureAfterD.buffer.addressBound
    change pressure.root.toNat + pressure.capacity.toNat < 4294967296 at this
    omega
  have hFinalOwner := hFieldsAfterD.released pressure hPressureRoot hPressure32 (regionsDisjoint_symm hSepPF)
  let result := resultFrame frameAfterD 29 ((heapF.release density).frees + 1)
  apply hNext _ _ fields result hHeapAfterP hFinalOwner ((hBudgetF.released density).released pressure)
  · exact hAfterDParams
  · simpa only [result, resultFrame_locals_length] using hAfterDLocals
  · rfl
  · exact (hScratchF.result 28 _ (by omega) (hValidF 28 (by decide))).result 29 _
      (by change frameF.params.length ≤ 29; omega)
      (by simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParamsF, hLocalsF])
  · dsimp only [result, frameAfterD]
    rw [resultFrame_get_ne _ 29 26 _ (by change frameF.params.length ≤ 29; omega) (by decide),
      resultFrame_get_ne _ 28 26 _ (by omega) (by decide)]
    exact hOwnerF
  · dsimp only [result, frameAfterD]
    rw [resultFrame_get_ne _ 29 27 _ (by change frameF.params.length ≤ 29; omega) (by decide),
      resultFrame_get_ne _ 28 27 _ (by omega) (by decide)]
    exact hPointerF
  · intro index hi
    dsimp only [result, frameAfterD]
    rw [resultFrame_get_ne _ 29 index _ (by change frameF.params.length ≤ 29; omega) (by omega),
      resultFrame_get_ne _ 28 index _ (by omega) (by omega)]
    exact (hPresF index (by omega) (by change index ≠ 26; omega) (by change index ≠ 27; omega)).trans
      ((hPresP index (by omega) (Or.inl (by change index < 15; omega))
        (by change index ≠ 23; omega) (by change index ≠ 24; omega)).trans
        (hPresD index (by omega) (Or.inl (by change index < 5; omega))
          (by change index ≠ 13; omega) (by change index ≠ 14; omega)))

#print axioms output_fields_shape
#print axioms output_fields_spec

end Project.EulerRiemann.Execution
