import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def capacityPrefix (length : UInt64) : Wasm.Program :=
  [
  .constI64 8,
  .constI64 length,
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
  .iff 0 0 [.constI64 8, .localSet 11] []
  ]

def capacityFrame (frame : Wasm.Locals) (capacity : UInt64) : Wasm.Locals :=
  { frame with locals := frame.locals.set 10 (.i64 capacity), values := [] }

def sumStep (sum element : UInt64) : UInt64 := sum + element

def foldBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++
  [
  .localGet 1,
  .localGet 2,
  .addI64,
  .localSet 3,
  .localGet 3,
  .localSet 17,
  .constI64 0,
  .localSet 16,
  .localGet 17,
  .localSet 1,
  .constI64 1,
  .localSet 18,
  .localGet 16,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 13,
  .constI64 1,
  .addI64,
  .localSet 13,
  .br 0
  ]

def foldLoop : Wasm.Program := [.block 0 0 [.loop 0 0 foldBody]]

def foldInvariant (st : Store Unit) (inputPtr root : UInt64)
    (input : Array UInt64) : Store Unit → Locals → Prop :=
  fun current frame =>
    current = st ∧
    ∃ index : Nat,
      index ≤ input.size ∧
      frame.params = [.i64 inputPtr] ∧
      frame.locals.length = 20 ∧
      frame.values = [] ∧
      frame.get 7 = some (.i64 root) ∧
      frame.get 11 = some (.i64 inputPtr) ∧
      frame.get 13 = some (.i64 (UInt64.ofNat index)) ∧
      frame.get 15 = some (.i64 (UInt64.ofNat input.size)) ∧
      frame.get 1 = some (.i64
        (ArrayFold.foldPrefix input sumStep 0 index))

def foldMeasure (input : Array UInt64) : Store Unit → Locals → Nat :=
  fun _ frame =>
    match frame.get 13 with
    | some (.i64 index) => input.size - index.toNat
    | _ => input.size + 1

theorem capacityPrefix_zero_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (capacityFrame frame 8) env) :
    wp module_ (capacityPrefix 0 ++ rest) Q st frame env := by
  simp (config := { maxSteps := 10000000 }) [capacityPrefix,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simpa [capacityFrame, hValues] using hNext

theorem capacityPrefix_one_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (capacityFrame frame 16) env) :
    wp module_ (capacityPrefix 1 ++ rest) Q st frame env := by
  simp (config := { maxSteps := 10000000 }) [capacityPrefix,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simpa [capacityFrame, hValues] using hNext

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
  case hParams => rfl
  case hValues => rfl
  case hInputLocalPositive => decide
  case hInputLocal =>
    simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  case hMaximumSize => norm_num [UInt64.size]
  case hValid =>
    intro hSize
    have hExpected : FormalSpec.expected input =
        #[input.foldl sumStep 0] := by
      unfold FormalSpec.expected
      rw [if_pos hSize]
      rfl
    have hFitMemory : heapTop.toNat + 48 + (16 : UInt64).toNat ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    have hFacts := Allocation.bumpFacts heapTop 16 initial.mem.pages
      hFitMemory hPages
    change wp module
      (capacityPrefix 1 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    refine capacityPrefix_one_spec module env initial _ ?_ ?_ ?_ _ _ ?_
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · refine FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
        initial _ heapTop 16 1 allocs ?_ ?_ ?_ ?_ ?_ hFitMemory hPages ?_
          hHeapTop hFreeList hAllocs _ _ ?_
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · decide
      · rfl
      · have hArrayAlloc := FixedArrayPairResult.input_preserved_by_alloc
          initial heapTop 16 1 allocs inputPtr input hArray hInputBelow
            hFitMemory hPages
        change wp module (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _
          (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs) _ env
        refine FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 1) (rootLocal := 7)
          (hValues := ?_) (hRoot := ?_) (hBound := ?_) (hNext := ?_)
        · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get]
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          omega
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          have hArrayLength : UInt64Array.At
              (FixedArrayResult.writeLength
                (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                (heapTop + 48) 1) inputPtr input := by
            have hWritten := hArrayAlloc.write64After
              (address := (heapTop + 48).toUInt32) (value := 1) (by
                rw [hRootAddress]
                omega)
            simpa [FixedArrayResult.writeLength] using hWritten
          change wp module
            (AnnotationMatches.function_0_array_fold_0_setup_program ++
              (foldLoop ++ _)) _
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
              (heapTop + 48) 1) _ env
          refine FixedArrayFold.forwardSetupProgram_spec
            11 12 13 16 14 1 18 15 0 module env _ _ inputPtr input
              ?_ ?_ ?_ ?_ hArrayLength _ _ ?_
          · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero]
          · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero]
          · intro slot hSlot
            simp [FixedArrayFold.setupLocals] at hSlot
            simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
              FixedArrayLengthDispatch.branchFrame, func0Def,
              Wasm.Function.toLocals, Wasm.Function.numParams,
              Wasm.ValueType.zero]
            omega
          · decide
          · unfold foldLoop
            simp only [List.cons_append, List.nil_append]
            wp_block_loop invariant
              (foldInvariant
                (FixedArrayResult.writeLength
                  (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                  (heapTop + 48) 1)
                inputPtr (heapTop + 48) input)
              decreasing (foldMeasure input)
            · refine ⟨rfl, 0, by omega, ?_⟩
              simp (config := { maxSteps := 10000000 }) [
                FixedArrayFold.forwardSetupFrame,
                FixedArrayAllocatorWindow.allocFrame, capacityFrame,
                FixedArrayLengthDispatch.branchFrame, func0Def,
                Wasm.Function.toLocals, Wasm.Function.numParams,
                Wasm.ValueType.zero, Wasm.Locals.get,
                ArrayFold.foldPrefix, sumStep]
            · intro st s hInv
              rcases hInv with
                ⟨rfl, index, hIndexLe, hParams, hLocals, hValues,
                  hRoot, hArrayLocal, hIndexLocal, hStopLocal, hAccumulator⟩
              have hRootOption : s.locals[6]? =
                  some (.i64 (heapTop + 48)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hRoot
              have hRootGet : s.locals[6] = .i64 (heapTop + 48) := by
                rw [List.getElem?_eq_getElem (by omega)] at hRootOption
                exact Option.some.inj hRootOption
              have hArrayOption : s.locals[10]? = some (.i64 inputPtr) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hArrayLocal
              have hArrayGet : s.locals[10] = .i64 inputPtr := by
                rw [List.getElem?_eq_getElem (by omega)] at hArrayOption
                exact Option.some.inj hArrayOption
              have hIndexOption : s.locals[12]? =
                  some (.i64 (UInt64.ofNat index)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hIndexLocal
              have hIndexGet : s.locals[12] =
                  .i64 (UInt64.ofNat index) := by
                rw [List.getElem?_eq_getElem (by omega)] at hIndexOption
                exact Option.some.inj hIndexOption
              have hStopOption : s.locals[14]? =
                  some (.i64 (UInt64.ofNat input.size)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hStopLocal
              have hStopGet : s.locals[14] =
                  .i64 (UInt64.ofNat input.size) := by
                rw [List.getElem?_eq_getElem (by omega)] at hStopOption
                exact Option.some.inj hStopOption
              have hAccumulatorOption : s.locals[0]? = some (.i64
                  (ArrayFold.foldPrefix input sumStep 0 index)) := by
                simpa [Wasm.Locals.get, hParams, hLocals] using hAccumulator
              have hAccumulatorGet : s.locals[0] = .i64
                  (ArrayFold.foldPrefix input sumStep 0 index) := by
                rw [List.getElem?_eq_getElem (by omega)] at hAccumulatorOption
                exact Option.some.inj hAccumulatorOption
              by_cases hIndex : index < input.size
              · unfold foldBody
                refine FixedArrayTraversalInput.continuingProgram_spec
                  (arrayLocal := 11) (indexLocal := 13) (stopLocal := 15)
                  (itemLocal := 2) (inputPtr := inputPtr)
                  (indexValue := UInt64.ofNat index)
                  (stopValue := UInt64.ofNat input.size)
                  (input := input) (index := index)
                  (hValues := hValues) (hArrayLocal := hArrayLocal)
                  (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
                  (hIndexValue := rfl) (hContinue := ?_)
                  (hItem := ?_) (hInput := hArrayLength) (hIndex := hIndex)
                  (hNext := ?_)
                · rw [UInt64.lt_iff_toNat_lt,
                    UInt64.toNat_ofNat_of_lt' (by
                      have hInputSize := hArrayLength.size_lt
                      omega),
                    UInt64.toNat_ofNat_of_lt' hArrayLength.size_lt]
                  exact hIndex
                · simpa [Wasm.Locals.validIndex, hParams, hLocals]
                · simp (config := { maxSteps := 10000000 }) [wp_simp,
                    FixedArrayTraversalInput.dynamicResultFrame,
                    Wasm.Locals.get, Wasm.Locals.set?, hParams, hLocals,
                    hValues, hRootGet, hArrayGet, hIndexGet, hStopGet,
                    hAccumulatorGet, foldInvariant, foldMeasure]
                  refine ⟨?_, ?_⟩
                  · refine ⟨index + 1, by omega, ?_, ?_⟩
                    · change UInt64.ofNat index + UInt64.ofNat 1 =
                        UInt64.ofNat (index + 1)
                      exact (UInt64.ofNat_add index 1).symm
                    · simpa [sumStep] using
                        (ArrayFold.foldPrefix_succ input sumStep 0 index
                          hIndex).symm
                  · rw [Nat.mod_eq_of_lt (by norm_num; omega),
                      Nat.mod_eq_of_lt (by norm_num; omega)]
                    omega
              · have hIndexEq : index = input.size := by omega
                subst index
                have hStopAfter :
                    ({ s with values :=
                      Value.i64 (UInt64.ofNat input.size) :: s.values } : Locals).get
                        15 =
                      some (.i64 (UInt64.ofNat input.size)) := by
                  simpa only [Wasm.Locals.get] using hStopLocal
                unfold foldBody FixedArrayTraversalInput.continuingProgram
                rw [List.append_assoc]
                simp only [List.cons_append, List.nil_append]
                rw [wp_localGet_cons, hIndexLocal]
                simp only
                rw [wp_localGet_cons, hStopAfter]
                simp only
                rw [wp_geUI64_cons]
                simp only
                rw [if_pos (by simp)]
                rw [wp_br_if_cons]
                rw [hValues]
                have hOne : (1 : UInt32) ≠ 0 := by decide
                simp only [hOne]
                simp only [FixedArrayFold.forwardSetupFrame_values,
                  List.take_zero, List.drop_zero, List.nil_append]
                change wp module
                  (FixedArrayFold.resultProgram 1 10 ++
                    (FixedArrayResult.payloadStoreProgram 7 10 0 ++ _)) _ _
                  ({ s with values := [] } : Locals) env
                refine FixedArrayFold.resultProgram_spec
                  (accumulatorLocal := 1) (resultLocal := 10)
                  (module_ := module) (env := env)
                  (st := FixedArrayResult.writeLength
                    (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                    (heapTop + 48) 1)
                  (frame := ({ s with values := [] } : Locals))
                  (value := ArrayFold.foldPrefix input sumStep 0 input.size)
                  (hValues := rfl) (hAccumulator := ?_)
                  (hResultLocal := ?_) (hResultValid := ?_) (hNext := ?_)
                · simpa only [Wasm.Locals.get] using hAccumulator
                · simpa [hParams]
                · simpa [Wasm.Locals.validIndex, hParams, hLocals]
                · refine FixedArrayResult.payloadStore_spec
                    (module_ := module) (env := env)
                    (st := FixedArrayResult.writeLength
                      (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                      (heapTop + 48) 1)
                    (frame := FixedArrayFold.resultFrame
                      ({ s with values := [] } : Locals) 10
                      (ArrayFold.foldPrefix input sumStep 0 input.size))
                    (root := heapTop + 48)
                    (value := ArrayFold.foldPrefix input sumStep 0 input.size)
                    (rootLocal := 7) (scratchLocal := 10) (index := 0)
                    (hRoot := ?_) (hValue := ?_) (hBound := ?_) (hNext := ?_)
                  · simpa [FixedArrayFold.resultFrame, Wasm.Locals.get,
                      hParams, hLocals] using hRootGet
                  · simp [FixedArrayFold.resultFrame, Wasm.Locals.get,
                      hParams, hLocals]
                  · have hPayloadAddress :
                        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
                          heapTop.toNat + 56 := by
                      simpa [FixedArrayResult.payloadAddress] using
                        hFacts.wordAddress_toNat 1 (by decide)
                    rw [hPayloadAddress, FixedArrayResult.writeLength_pages,
                      FixedArrayAllocator.allocStore_pages]
                    simpa using hFitMemory
                  · have hRootFit32 : (heapTop + 48).toNat + 16 ≤
                        4294967296 := by
                      rw [hFacts.rootToNat]
                      simpa using hFacts.fit32
                    have hRootFitMemory : (heapTop + 48).toNat + 16 ≤
                        (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs).mem.pages *
                          65536 := by
                      rw [hFacts.rootToNat,
                        FixedArrayAllocator.allocStore_pages]
                      simpa using hFitMemory
                    have hOutput := FixedArrayResult.singletonStore_at
                      (FixedArrayAllocator.allocStore initial heapTop 16 1 allocs)
                      (heapTop + 48)
                      (ArrayFold.foldPrefix input sumStep 0 input.size)
                      hRootFit32 hRootFitMemory
                    simpa (config := { maxSteps := 10000000 }) [wp_simp,
                      FixedArrayEqNode.branchPost, FixedArrayFold.resultFrame,
                      FixedArrayResult.singletonStore,
                      FixedArrayResult.writePayload,
                      FixedArrayResult.writeLength, Wasm.Locals.get,
                      Wasm.Locals.set?, hParams, hLocals, hValues, hRootGet,
                      hExpected, ArrayFold.foldPrefix_size,
                      FormalSpec.UInt64ArrayAt, UInt64Array.At, func0Def,
                      Wasm.Function.toLocals, Wasm.Function.numParams,
                      Wasm.ValueType.zero] using hOutput
  case hInvalid =>
    intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hFitMemory : heapTop.toNat + 48 + (8 : UInt64).toNat ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    have hFacts := Allocation.bumpFacts heapTop 8 initial.mem.pages
      hFitMemory hPages
    change wp module
      (capacityPrefix 0 ++
        (FixedArrayAllocatorWindow.region 2 1 ++ _)) _ initial _ env
    refine capacityPrefix_zero_spec module env initial _ ?_ ?_ ?_ _ _ ?_
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero]
    · refine FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
        initial _ heapTop 8 1 allocs ?_ ?_ ?_ ?_ ?_ hFitMemory hPages ?_
          hHeapTop hFreeList hAllocs _ _ ?_
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · simp [capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
          Wasm.Function.toLocals, Wasm.Function.numParams,
          Wasm.ValueType.zero]
      · decide
      · rfl
      · change wp module (FixedArrayResult.lengthStoreProgram 7 0 ++ _) _
          (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs) _ env
        refine FixedArrayResult.lengthStore_spec
          (root := heapTop + 48) (length := 0) (rootLocal := 7)
          (hValues := ?_) (hRoot := ?_) (hBound := ?_) (hNext := ?_)
        · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero]
        · simp [FixedArrayAllocatorWindow.allocFrame, capacityFrame,
            FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get]
        · have hRootAddress : (heapTop + 48).toUInt32.toNat =
              heapTop.toNat + 48 := by
            simpa using hFacts.wordAddress_toNat 0 (by decide)
          rw [hRootAddress, FixedArrayAllocator.allocStore_pages]
          omega
        · have hRootFit32 : (heapTop + 48).toNat + 8 ≤ 4294967296 := by
            rw [hFacts.rootToNat]
            omega
          have hRootFitMemory : (heapTop + 48).toNat + 8 ≤
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
                65536 := by
            rw [hFacts.rootToNat, FixedArrayAllocator.allocStore_pages]
            omega
          have hOutput := FixedArrayResult.emptyStore_at
            (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
            (heapTop + 48) hRootFit32 hRootFitMemory
          simpa (config := { maxSteps := 10000000 }) [wp_simp,
            FixedArrayEqNode.branchPost, FixedArrayAllocatorWindow.allocFrame,
            capacityFrame, FixedArrayLengthDispatch.branchFrame, func0Def,
            Wasm.Function.toLocals, Wasm.Function.numParams,
            Wasm.ValueType.zero, Wasm.Locals.get, Wasm.Locals.set?,
            FormalSpec.UInt64ArrayAt, UInt64Array.At, hExpected] using hOutput

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
