import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

private def validBaseFrame (inputPtr : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals :=
      [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr,
        .i64 0, .i64 0, .i64 0, .i64 16, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

private def validAllocatedFrame (inputPtr heapTop : UInt64) : Locals :=
  FixedArrayAllocatorWindow.allocFrame 2 (validBaseFrame inputPtr) heapTop 16

private def validLengthStore (initial : Store Unit) (heapTop allocs : UInt64) :
    Store Unit :=
  { FixedArrayAllocator.allocStore initial heapTop 16 1 allocs with
    mem := (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
      (heapTop + 48).toUInt32 1 }

private def validLoopFrame (inputPtr heapTop : UInt64) (inputSize index : Nat)
    (acc item temp done staged released : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals :=
      [.i64 acc, .i64 item, .i64 temp, .i64 0, .i64 0, .i64 0,
        .i64 (heapTop + 48), .i64 0, .i64 0, .i64 0, .i64 inputPtr,
        .i64 (UInt64.ofNat inputSize), .i64 (UInt64.ofNat index),
        .i64 (UInt64.ofNat inputSize), .i64 (UInt64.ofNat inputSize),
        .i64 done, .i64 staged, .i64 released, .i64 0, .i64 0]
    values := [] }

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
  · omega
  · norm_num [func0Def, Wasm.Function.toLocals]
  · norm_num [UInt64.size]
  all_goals intro hSize
  all_goals
    wp_length_dispatch [func0Def, FixedArrayLengthDispatch.branchFrame,
      Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]
  all_goals
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [wp_nil]
  all_goals
    change wp «module» (FixedArrayAllocatorWindow.region 2 1 ++ _) _ _ _ _
  case hInvalid =>
    have hFitMemory :
        heapTop.toNat + 48 + (8 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    apply FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop)
      (capacity := 8) (stride := 1) (allocs := allocs)
    case hParams => rfl
    case hLocals => rfl
    case hValues => rfl
    case hCapacityLocal => rfl
    case hCapacity =>
      change 8 ≤ (8 : Nat)
      omega
    case hFitMemory => simpa using hFitMemory
    case hPages => exact hPages
    case hMemory32 => rfl
    case hHeapTop => exact hHeapTop
    case hFreeList => exact hFreeList
    case hAllocs => exact hAllocs
    case hNext =>
      have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitMemory hPages
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        have hWord : 8 * (0 + 1) ≤ (8 : UInt64).toNat := by
          change 8 ≤ (8 : Nat)
          omega
        simpa using hFacts.wordAddress_toNat 0 hWord
      have hRootBound :
          (heapTop + 48).toNat % 4294967296 + 8 ≤
            initial.mem.pages * 65536 := by
        rw [hFacts.rootToNat, Nat.mod_eq_of_lt]
        · simpa using hFitMemory
        · omega
      wp_alloc_window_lists [FixedArrayAllocatorWindow.allocFrame, hRootAddress,
        hRootBound, func0Def, FormalSpec.expected, hSize,
        FixedArrayEqNode.branchPost]
      constructor
      · rw [FixedArrayAllocator.allocStore_pages, ← hFacts.rootToNat]
        exact hRootBound
      · have hRootPointer :
            UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
              (heapTop + 48).toUInt32 := by
          rw [← hFacts.rootToNat]
          exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
        unfold FormalSpec.UInt64ArrayAt
        simp only [Array.size_empty, Nat.zero_add, Nat.mul_one]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hFacts.rootToNat]
          exact hFacts.fit32
        · simp only [Wasm.Mem.write64_pages,
            FixedArrayAllocator.allocStore_pages]
          rw [hFacts.rootToNat]
          simpa using hFitMemory
        · rw [hRootPointer, Wasm.Mem.read64_write64_same]
          rfl
        · simp
  case hValid =>
    change wp «module» (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial
      (validBaseFrame inputPtr) env
    have hFitMemory :
        heapTop.toNat + 48 + (16 : UInt64).toNat ≤
          initial.mem.pages * 65536 := by
      simpa [FormalSpec.expected, hSize] using hOutputFitMemory
    apply FixedArrayAllocatorWindow.region_spec_withTail
      (offset := 2) (tail := 4) (heapTop := heapTop)
      (capacity := 16) (stride := 1) (allocs := allocs)
    case hParams => rfl
    case hLocals => rfl
    case hValues => rfl
    case hCapacityLocal => rfl
    case hCapacity =>
      change 8 ≤ (16 : Nat)
      omega
    case hFitMemory => simpa using hFitMemory
    case hPages => exact hPages
    case hMemory32 => rfl
    case hHeapTop => exact hHeapTop
    case hFreeList => exact hFreeList
    case hAllocs => exact hAllocs
    case hNext =>
      have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
        hFitMemory hPages
      have hWord0 : 8 * (0 + 1) ≤ (16 : UInt64).toNat := by
        change 8 ≤ (16 : Nat)
        omega
      have hRootAddress :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 hWord0
      have hRootPointer :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        rw [← hFacts.rootToNat]
        exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
      have hRootPointerAdd :
          heapTop.toUInt32 + 48 = (heapTop + 48).toUInt32 := by
        rw [← hRootPointer]
        apply UInt32.toNat.inj
        simp
      have hRootBound :
          (heapTop + 48).toNat % 4294967296 + 8 ≤
            initial.mem.pages * 65536 := by
        rw [hFacts.rootToNat, Nat.mod_eq_of_lt]
        · omega
        · omega
      have hInputAllocated :=
        FixedArrayPairResult.input_preserved_by_alloc initial heapTop 16 1
          allocs inputPtr input hArray hInputBelow hFitMemory hPages
      have hInputAfterLength : UInt64Array.At
          { FixedArrayAllocator.allocStore initial heapTop 16 1 allocs with
            mem := (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
              (heapTop + 48).toUInt32 1 }
          inputPtr input := by
        apply hInputAllocated.write64After
        rw [hRootAddress]
        omega
      have hLengthReadAfter := hInputAfterLength.lengthRead
      have hLengthBoundAfter := hInputAfterLength.generatedLengthBound
      have hInputAddressAfter := hInputAfterLength.pointerAddress_eq
      have hAllocRoot :
          (FixedArrayAllocatorWindow.allocFrame 2 (validBaseFrame inputPtr)
            heapTop 16).get 7 = some (.i64 (heapTop + 48)) := by
        simp [FixedArrayAllocatorWindow.allocFrame, validBaseFrame, Locals.get]
      have hAllocValues :
          (FixedArrayAllocatorWindow.allocFrame 2 (validBaseFrame inputPtr)
            heapTop 16).values = [] := rfl
      rw [wp_localGet_cons, hAllocRoot, hAllocValues]
      wp_alloc_to_store_lists []
      rw [wp_store64_cons]
      simp only [FixedArrayAllocator.allocStore_pages]
      rw [if_neg (by
        apply Nat.not_lt.mpr
        simpa [hFacts.rootToNat] using hRootBound)]
      have hGeneratedRoot :
          UInt32.ofNat ((heapTop + 48).toNat % 2 ^ 32) + 0 =
            (heapTop + 48).toUInt32 := by
        have hPow : 2 ^ 32 = 4294967296 := by norm_num
        rw [hPow, UInt32.add_zero]
        rw [hFacts.rootToNat]
        exact hRootPointer
      rw [hGeneratedRoot]
      change wp «module» _ _ (validLengthStore initial heapTop allocs)
        (validAllocatedFrame inputPtr heapTop) env
      wp_length_dispatch [validAllocatedFrame, validBaseFrame,
        FixedArrayAllocatorWindow.allocFrame, hLengthReadAfter,
        hLengthBoundAfter, hInputAddressAfter]
      have hInputBoundValid :
          inputPtr.toNat % 4294967296 + 8 ≤
            (validLengthStore initial heapTop allocs).mem.pages * 65536 := by
        simpa [validLengthStore] using hLengthBoundAfter
      rw [if_neg (Nat.not_lt_of_ge hInputBoundValid)]
      rw [if_neg (Nat.not_lt_of_ge hInputBoundValid)]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      norm_num
      have hLengthReadValid :
          (validLengthStore initial heapTop allocs).mem.read64 inputPtr.toUInt32 =
            UInt64.ofNat input.size := by
        simpa [validLengthStore] using hLengthReadAfter
      rw [hLengthReadValid]
      change wp «module» (.block 0 0 _ :: _) _ _
        (validLoopFrame inputPtr heapTop input.size 0 0 0 0 inputPtr 0 0) env
      let Inv : Store Unit → Locals → Prop := fun st frame =>
        ∃ index item temp done staged released,
          index ≤ input.size ∧
          st = validLengthStore initial heapTop allocs ∧
          frame = validLoopFrame inputPtr heapTop input.size index
            (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index)
            item temp done staged released
      let measure : Store Unit → Locals → Nat := fun _ frame =>
        match frame.get 13 with
        | some (.i64 index) => input.size - index.toNat
        | _ => 0
      wp_block_loop invariant Inv decreasing measure
      case hInit =>
        dsimp [Inv]
        refine ⟨0, 0, 0, inputPtr, 0, 0, by omega, rfl, ?_⟩
        simp [validLoopFrame, ArrayFold.foldPrefix]
      case hStep =>
        intro st frame hInv
        dsimp [Inv] at hInv
        rcases hInv with
          ⟨index, item, temp, done, staged, released,
            hIndex, hStore, hFrame⟩
        subst st
        subst frame
        by_cases hDone : index = input.size
        · subst index
          unfold validLoopFrame
          wp_run
          norm_num
          simp
          have hWord1 : 8 * (1 + 1) ≤ (16 : UInt64).toNat := by
            change 16 ≤ (16 : Nat)
            omega
          have hPayloadBound :
              (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
                (validLengthStore initial heapTop allocs).mem.pages * 65536 := by
            rw [Nat.mod_eq_of_lt (by omega)]
            simpa [validLengthStore, FixedArrayAllocator.allocStore_pages]
              using hFitMemory
          have hPayloadFit32 :
              heapTop.toNat + 48 + 8 < 4294967296 := by
            have hFit := hFacts.fit32
            omega
          have hRootFit32 : heapTop.toNat + 48 < 4294967296 := by
            omega
          have hBaseFit32 : heapTop.toNat < 4294967296 := by
            omega
          have hPayloadAddress :
              UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
                (heapTop + 48 + 8).toUInt32 := by
            have hPayloadToNat :
                (heapTop + 48 + 8).toUInt32.toNat =
                  heapTop.toNat + 48 + 8 := by
              simpa using hFacts.wordAddress_toNat 1 hWord1
            apply UInt32.toNat.inj
            rw [hPayloadToNat]
            simp [Nat.mod_eq_of_lt hPayloadFit32]
          have hPayloadPointerAdd :
              heapTop.toUInt32 + 48 + 8 =
                (heapTop + 48 + 8).toUInt32 := by
            apply UInt32.toNat.inj
            have hPayloadToNat :
                (heapTop + 48 + 8).toUInt32.toNat =
                  heapTop.toNat + 48 + 8 := by
              simpa using hFacts.wordAddress_toNat 1 hWord1
            rw [hPayloadToNat]
            simp [UInt32.toNat_add, UInt64.toNat_toUInt32,
              Nat.mod_eq_of_lt hBaseFit32,
              Nat.mod_eq_of_lt hRootFit32,
              Nat.mod_eq_of_lt hPayloadFit32]
          have hPayloadStoreToNat :
              (heapTop.toUInt32 + 48 + 8).toNat =
                heapTop.toNat + 48 + 8 := by
            rw [hPayloadPointerAdd]
            simpa using hFacts.wordAddress_toNat 1 hWord1
          rw [if_neg (Nat.not_lt_of_ge hPayloadBound)]
          rw [hPayloadAddress]
          simp only [FixedArrayEqNode.branchPost]
          wp_run
          norm_num
          rw [show FormalSpec.expected input =
              #[input.foldl (fun sum element => sum + element) 0] by
            simp [FormalSpec.expected, hSize]]
          rw [ArrayFold.foldPrefix_size]
          unfold FormalSpec.UInt64ArrayAt
          simp only [Array.size_singleton]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hFacts.rootToNat]
            simpa using hFacts.fit32
          · simp only [Mem.write64_pages]
            rw [hFacts.rootToNat]
            simpa [validLengthStore, FixedArrayAllocator.allocStore_pages]
              using hFitMemory
          · rw [Memory.read64_write64_disjoint _ _ _ _
              (Or.inl (by rw [hRootAddress, hPayloadStoreToNat]))]
            change
              ((FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.write64
                (heapTop + 48).toUInt32 1).read64 (heapTop + 48).toUInt32 =
                UInt64.ofNat 1
            rw [Mem.read64_write64_same]
            rfl
          · intro i hi
            have hi0 : i = 0 := by omega
            subst i
            rw [Array.getElem_singleton]
            norm_num
            change
              ((validLengthStore initial heapTop allocs).mem.write64
                (heapTop.toUInt32 + 48 + 8)
                (input.foldl (fun sum element => sum + element) 0)).read64
                  (heapTop.toUInt32 + 48 + 8) =
                input.foldl (fun sum element => sum + element) 0
            rw [Mem.read64_write64_same]
        · have hIndexLt : index < input.size := by omega
          have hCurrentInput : UInt64Array.At
              (validLengthStore initial heapTop allocs) inputPtr input := by
            simpa [validLengthStore] using hInputAfterLength
          have hSizeEncoded :
              (UInt64.ofNat input.size).toNat = input.size :=
            UInt64.toNat_ofNat_of_lt' hCurrentInput.size_lt
          have hIndexEncoded :
              (UInt64.ofNat index).toNat = index :=
            UInt64.toNat_ofNat_of_lt'
              (Nat.lt_trans hIndexLt hCurrentInput.size_lt)
          have hGuardFalse :
              ¬UInt64.ofNat input.size ≤ UInt64.ofNat index := by
            rw [UInt64.le_iff_toNat_le, hSizeEncoded, hIndexEncoded]
            omega
          rcases hCurrentInput.generatedElement index hIndexLt with
            ⟨hElementBound, hElementRead⟩
          have hElementSafe :
              ¬(validLengthStore initial heapTop allocs).mem.pages * 65536 <
                (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 :=
            Nat.not_lt_of_ge hElementBound
          have hElementReadGenerated :
              (validLengthStore initial heapTop allocs).mem.read64
                  (UInt32.ofNat
                    ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
                input[index] := by
            simpa [Nat.mul_comm] using hElementRead
          unfold validLoopFrame
          wp_run
          norm_num
          simp [hGuardFalse, hElementSafe, hElementReadGenerated]
          have hIndexSuccLt : index + 1 < UInt64.size := by
            exact Nat.lt_of_le_of_lt (by omega) hCurrentInput.size_lt
          have hIndexSuccEncoded :
              (UInt64.ofNat index + 1).toNat = index + 1 := by
            simpa using UInt64.toNat_ofNat_of_lt' hIndexSuccLt
          constructor
          · dsimp [Inv]
            refine
              ⟨index + 1, input[index],
                ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 index + input[index],
                0,
                ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 index + input[index],
                1, by omega, rfl, ?_⟩
            rw [ArrayFold.foldPrefix_succ input
              (fun sum element => sum + element) 0 index hIndexLt]
            simp [validLoopFrame, UInt64.ofNat_add]
          · dsimp [measure]
            norm_num [Locals.get]
            change index + 1 < 18446744073709551616 at hIndexSuccLt
            change
              input.size - (index + 1) % 18446744073709551616 <
                input.size - index % 18446744073709551616
            rw [Nat.mod_eq_of_lt hIndexSuccLt,
              Nat.mod_eq_of_lt (by omega)]
            omega

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
