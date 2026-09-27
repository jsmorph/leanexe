import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def resultCapacityPrefix (elementCount : UInt64) : Wasm.Program :=
  [
    .constI64 8,
    .constI64 elementCount,
    .constI64 1,
    .mulI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .constI64 7,
    .addI64,
    .constI64 8,
    .divUI64,
    .constI64 8,
    .mulI64,
    .localSet 11,
    .localGet 11,
    .constI64 8,
    .ltUI64,
    .iff 0 0 [
      .constI64 8,
      .localSet 11
    ] []
  ]

def foldInvariant (fixedStore : Wasm.Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Wasm.AssertionF Unit :=
  fun st frame =>
    st = fixedStore ∧
    ∃ index : Nat,
      index ≤ input.size ∧
      frame.params = [.i64 inputPtr] ∧
      frame.locals.length = 20 ∧
      frame.values = [] ∧
      frame.get 1 = some (.i64 (ArrayFold.foldPrefix input
        (fun (sum element : UInt64) => sum + element) 0 index)) ∧
      frame.get 7 = some (.i64 root) ∧
      frame.get 11 = some (.i64 inputPtr) ∧
      frame.get 13 = some (.i64 (UInt64.ofNat index)) ∧
      frame.get 15 = some (.i64 (UInt64.ofNat input.size))

def foldMeasure (input : Array UInt64) (_st : Wasm.Store Unit)
    (frame : Wasm.Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

theorem artifact_behavior :
    LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR23fa7efc3fb0298b.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.generatedLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · rfl
  · rfl
  · decide
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · decide
  · intro hSize
    change wp module
      (resultCapacityPrefix 1 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    unfold resultCapacityPrefix
    wp_length_dispatch [func0Def, FixedArrayLengthDispatch.branchFrame,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
      initial _ heapTop 16 1 allocs
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hFitMemory : heapTop.toNat + 48 + (16 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
        simpa [FormalSpec.heapReserveBytes, hSize] using hHeapFitMemory
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hFitMemory hPages
      have hInputAlloc := FixedArrayPairResult.input_preserved_by_alloc
        initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
        hFitMemory hPages
      have hRootToNat := hFacts.wordAddress_toNat 0 (by decide)
      have hRootToNat' : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hRootToNat
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          initial.mem.pages * 65536 := by
        rw [hRootToNat']
        omega
      have hRootBoundGenerated : (heapTop.toNat + 48) % 4294967296 + 8 ≤
          initial.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have hRootAddress : UInt32.ofNat
          ((heapTop.toNat + 48) % 4294967296) =
          (heapTop + 48).toUInt32 :=
        (Allocation.root_toUInt32 heapTop (by omega)).symm
      have hInputLength := hInputAlloc.write64After (address :=
          (heapTop + 48).toUInt32) (value := 1) (by
        rw [hRootToNat']
        omega)
      have hLengthRead' := hInputLength.lengthRead
      have hLengthBound' := hInputLength.generatedLengthBound
      have hInputAddress' := hInputLength.pointerAddress_eq
      wp_alloc_window_lists [FixedArrayAllocatorWindow.allocFrame,
        FixedArrayAllocator.allocStore_pages, hFacts.rootToNat,
        hRootToNat', hRootBound, hLengthRead', hLengthBound', hInputAddress']
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [if_neg (by omega)]
      rw [hRootAddress, hLengthRead']
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_alloc_window_lists []
      have hRootAddressAdd : heapTop.toUInt32 + 48 =
          (heapTop + 48).toUInt32 := by
        simp
      rw [hRootAddressAdd]
      apply Wasm.wp_block_cons
      apply Wasm.wp_loop_cons
        (Inv := foldInvariant
          { (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs) with
            mem := (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
              (heapTop + 48).toUInt32 1 }
          inputPtr (heapTop + 48) input)
        (μ := foldMeasure input)
      · refine ⟨rfl, 0, by omega, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
        simp [ArrayFold.foldPrefix, Wasm.Locals.get]
      · rintro st frame
          ⟨rfl, index, hIndex, hParams', hLocals', hValues', hAcc,
            hRoot', hInputPtr', hIndex', hStop'⟩
        by_cases hContinue : index < input.size
        · have hIndexToNat : (UInt64.ofNat index).toNat = index :=
            UInt64.toNat_ofNat_of_lt' (by
              have hSizeLt := hInputLength.size_lt
              omega)
          have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
            UInt64.toNat_ofNat_of_lt' hInputLength.size_lt
          have hContinueEncoded :
              UInt64.ofNat index < UInt64.ofNat input.size := by
            rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
            exact hContinue
          have hItem : frame.validIndex 2 := by
            simpa [Wasm.Locals.validIndex, hParams', hLocals']
          have hAccLocalOption : frame.locals[0]? = some (.i64
              (ArrayFold.foldPrefix input
                (fun (sum element : UInt64) => sum + element) 0 index)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hAcc
          rcases List.getElem?_eq_some_iff.mp hAccLocalOption with
            ⟨hAccLocalBound, hAccLocal⟩
          have hIndexLocalOption : frame.locals[12]? =
              some (.i64 (UInt64.ofNat index)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hIndex'
          rcases List.getElem?_eq_some_iff.mp hIndexLocalOption with
            ⟨hIndexLocalBound, hIndexLocal⟩
          have hRootLocalOption : frame.locals[6]? =
              some (.i64 (heapTop + 48)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hRoot'
          rcases List.getElem?_eq_some_iff.mp hRootLocalOption with
            ⟨hRootLocalBound, hRootLocal⟩
          have hInputPtrLocalOption : frame.locals[10]? =
              some (.i64 inputPtr) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hInputPtr'
          rcases List.getElem?_eq_some_iff.mp hInputPtrLocalOption with
            ⟨hInputPtrLocalBound, hInputPtrLocal⟩
          have hStopLocalOption : frame.locals[14]? =
              some (.i64 (UInt64.ofNat input.size)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hStop'
          rcases List.getElem?_eq_some_iff.mp hStopLocalOption with
            ⟨hStopLocalBound, hStopLocal⟩
          have hNextToNat : (UInt64.ofNat (index + 1)).toNat = index + 1 :=
            UInt64.toNat_ofNat_of_lt' (by
              have hSizeLt := hInputLength.size_lt
              omega)
          change wp module
            (FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ _)
            _ _ frame env
          refine FixedArrayTraversalInput.continuingProgram_spec
            11 13 15 2 module env _ frame inputPtr
            (UInt64.ofNat index) (UInt64.ofNat input.size) input index
            hValues' hInputPtr' hIndex' hStop' rfl hContinueEncoded hItem
            hInputLength hContinue _ _ ?_
          wp_traversal_input [FixedArrayTraversalInput.dynamicResultFrame,
            foldInvariant, foldMeasure, hParams', hLocals', hValues', hAcc,
            hRoot', hInputPtr', hIndex', hStop', hAccLocalOption, hAccLocal,
            hIndexLocalOption, hIndexLocal, hRootLocalOption,
            hInputPtrLocalOption, hStopLocalOption, hNextToNat,
            ArrayFold.foldPrefix_succ input
              (fun (sum element : UInt64) => sum + element) 0 index hContinue,
            hIndexToNat, hInputSizeToNat]
          constructor
          · refine ⟨index + 1, by omega, ?_, hRootLocal,
              hInputPtrLocal, ?_, hStopLocal⟩
            · exact (ArrayFold.foldPrefix_succ input
                (fun (sum element : UInt64) => sum + element)
                0 index hContinue).symm
            · change UInt64.ofNat index + UInt64.ofNat 1 =
                UInt64.ofNat (index + 1)
              rw [← UInt64.ofNat_add]
          · rw [Nat.mod_eq_of_lt (by
              have hSizeLt := hInputLength.size_lt
              omega)]
            omega
        · have hDone : index = input.size := by omega
          have hAccFinal := hAcc
          rw [hDone, ArrayFold.foldPrefix_size] at hAccFinal
          have hAccFinalLocalOption : frame.locals[0]? = some (.i64
              (input.foldl (fun (sum element : UInt64) => sum + element) 0)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hAccFinal
          rcases List.getElem?_eq_some_iff.mp hAccFinalLocalOption with
            ⟨hAccFinalLocalBound, hAccFinalLocal⟩
          have hIndexLocalOption : frame.locals[12]? =
              some (.i64 (UInt64.ofNat index)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hIndex'
          rcases List.getElem?_eq_some_iff.mp hIndexLocalOption with
            ⟨hIndexLocalBound, hIndexLocal⟩
          have hStopLocalOption : frame.locals[14]? =
              some (.i64 (UInt64.ofNat input.size)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hStop'
          rcases List.getElem?_eq_some_iff.mp hStopLocalOption with
            ⟨hStopLocalBound, hStopLocal⟩
          have hRootLocalOption : frame.locals[6]? =
              some (.i64 (heapTop + 48)) := by
            simpa [Wasm.Locals.get, hParams', hLocals'] using hRoot'
          rcases List.getElem?_eq_some_iff.mp hRootLocalOption with
            ⟨hRootLocalBound, hRootLocal⟩
          have hPayloadToNat := hFacts.wordAddress_toNat 1 (by decide)
          have hPayloadToNat' : (heapTop + 56).toUInt32.toNat =
              heapTop.toNat + 56 := by
            simpa [add_assoc] using hPayloadToNat
          have hPayloadBound : (heapTop + 56).toUInt32.toNat + 8 ≤
              initial.mem.pages * 65536 := by
            rw [hPayloadToNat']
            omega
          let lengthStore : Store Unit :=
            { (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs) with
              mem := (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
                (heapTop + 48).toUInt32 1 }
          let resultValue :=
            input.foldl (fun (sum element : UInt64) => sum + element) 0
          let completedStore : Store Unit :=
            { lengthStore with
              mem := lengthStore.mem.write64 (heapTop + 56).toUInt32 resultValue }
          have hCompletedOutput : UInt64Array.At completedStore
              (heapTop + 48) #[resultValue] := by
            apply UInt64Array.singleton
            · simpa [completedStore, lengthStore, FormalSpec.expected, hSize,
                hFacts.rootToNat] using hOutputFit32
            · simpa [completedStore, lengthStore,
                FixedArrayAllocator.allocStore_pages, FormalSpec.expected,
                hSize, hFacts.rootToNat] using hOutputFitMemory
            · dsimp [completedStore, lengthStore]
              word_reads
            · dsimp [completedStore, lengthStore]
              word_reads
          wp_traversal_input [hValues', hDone, hIndexLocal, hStopLocal,
            hAccFinalLocal, hRootLocal, hPayloadToNat', hPayloadBound,
            FixedArrayAllocator.allocStore_pages, completedStore, lengthStore,
            resultValue, FormalSpec.expected, hSize, hCompletedOutput]
  · intro hSize

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
