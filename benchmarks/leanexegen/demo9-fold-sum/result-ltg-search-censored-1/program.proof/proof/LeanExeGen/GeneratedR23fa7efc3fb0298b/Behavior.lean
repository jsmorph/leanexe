import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def resultCapacity (length : UInt64) : UInt64 :=
  ((8 + length * 1 * 8 + 7) / 8) * 8

def resultCapacityPrefix (length : UInt64) : Wasm.Program :=
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
  .iff 0 0 [
    .constI64 8,
    .localSet 11
  ] []
  ]

def resultCapacityFrame (frame : Locals) (capacity : UInt64) : Locals :=
  { frame with locals := frame.locals.set 10 (.i64 capacity) }

theorem resultCapacityPrefix_spec
    (length : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hNotSmall : ¬resultCapacity length < 8)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (resultCapacityFrame frame (resultCapacity length)) env) :
    wp module_ (resultCapacityPrefix length ++ rest) Q st frame env := by
  simp (config := { maxSteps := 10000000 }) [resultCapacityPrefix,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
    List.length_set, hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simpa [resultCapacity] using hNotSmall)]
  simpa [resultCapacityFrame, resultCapacity, hValues] using hNext

def foldSetupProgram : Wasm.Program :=
  [
  .localGet 0,
  .localSet 11,
  .localGet 11,
  .wrapI64,
  .load64 0,
  .localSet 12,
  .constI64 0,
  .localSet 13,
  .localGet 0,
  .localSet 16,
  .localGet 16,
  .wrapI64,
  .load64 0,
  .localSet 14,
  .constI64 0,
  .localSet 1,
  .constI64 0,
  .localSet 18,
  .localGet 14,
  .localGet 12,
  .ltUI64,
  .iff 0 1 [.localGet 14] [.localGet 12],
  .localSet 15
  ]

def foldStepSuffix : Wasm.Program :=
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

def foldBodyProgram : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 11 13 15 2 ++ foldStepSuffix

def foldResultProgram : Wasm.Program :=
  [.localGet 1, .localSet 10]

def foldProgram : Wasm.Program :=
  foldSetupProgram ++
    [.block 0 0 [.loop 0 0 foldBodyProgram]] ++
    foldResultProgram

theorem annotatedFoldProgram_eq :
    AnnotationMatches.function_0_array_fold_0_program = foldProgram := by
  rfl

def foldFrameIndex (frame : Locals) : Nat :=
  match frame.get 13 with
  | some (.i64 value) => value.toNat
  | _ => 0

def foldMeasure (input : Array UInt64) (_st : Store Unit)
    (frame : Locals) : Nat :=
  input.size - foldFrameIndex frame

def FoldInv (st : Store Unit) (inputPtr : UInt64)
    (input : Array UInt64) (root : UInt64) : AssertionF Unit :=
  fun st' frame =>
    ∃ index : Nat,
      index ≤ input.size ∧
      st' = st ∧
      frame.params = [.i64 inputPtr] ∧
      frame.locals.length = 20 ∧
      frame.values = [] ∧
      frame.get 7 = some (.i64 root) ∧
      frame.get 11 = some (.i64 inputPtr) ∧
      frame.get 13 = some (.i64 (UInt64.ofNat index)) ∧
      frame.get 15 = some (.i64 (UInt64.ofNat input.size)) ∧
      frame.get 1 = some (.i64
        (ArrayFold.foldPrefix input (fun sum element => sum + element) 0 index))

def FoldResult (inputPtr : UInt64) (input : Array UInt64)
    (root : UInt64) (frame : Locals) : Prop :=
  frame.params = [.i64 inputPtr] ∧
  frame.locals.length = 20 ∧
  frame.values = [] ∧
  frame.get 7 = some (.i64 root) ∧
  frame.get 10 = some (.i64
    (input.foldl (fun sum element => sum + element) 0))

def foldNextFrame (frame : Locals) (inputPtr item sum next : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := ((((((frame.locals.set 1 (.i64 item)).set 2 (.i64 sum)).set
      16 (.i64 sum)).set 15 (.i64 0)).set 0 (.i64 sum)).set
      17 (.i64 1)).set 12 (.i64 next)
    values := [] }

theorem foldNextFrame_inv
    (st : Store Unit) (current : Locals) (inputPtr : UInt64)
    (input : Array UInt64) (root : UInt64) (index : Nat)
    (hIndex : index + 1 ≤ input.size)
    (hLocals : current.locals.length = 20)
    (hRoot : current.locals[6] = .i64 root)
    (hArray : current.locals[10] = .i64 inputPtr)
    (hStop : current.locals[14] = .i64 (UInt64.ofNat input.size)) :
    FoldInv st inputPtr input root st
      (foldNextFrame current inputPtr input[index]
        (ArrayFold.foldPrefix input (fun sum element => sum + element) 0
          (index + 1))
        (UInt64.ofNat (index + 1))) := by
  refine ⟨index + 1, hIndex, rfl, rfl, ?_⟩
  simp (config := { maxSteps := 10000000 }) [foldNextFrame,
    Wasm.Locals.get, List.length_set, List.getElem?_set,
    hLocals, hRoot, hArray, hStop]

theorem foldNextFrame_measure
    (st : Store Unit) (current : Locals) (inputPtr : UInt64)
    (input : Array UInt64) (index : Nat)
    (hLocals : current.locals.length = 20)
    (hIndexLocal : current.get 13 = some (.i64 (UInt64.ofNat index)))
    (hIndex : index < input.size)
    (hIndexSize : index < UInt64.size)
    (hIndexSuccSize : index + 1 < UInt64.size) :
    foldMeasure input st
        (foldNextFrame current inputPtr input[index]
          (ArrayFold.foldPrefix input (fun sum element => sum + element) 0
            (index + 1))
          (UInt64.ofNat (index + 1))) <
      foldMeasure input st current := by
  unfold foldMeasure foldFrameIndex
  rw [hIndexLocal]
  simp (config := { maxSteps := 10000000 }) [foldNextFrame,
    Wasm.Locals.get, List.length_set, List.getElem?_set, hLocals,
    Nat.mod_eq_of_lt hIndexSuccSize,
    UInt64.toNat_ofNat_of_lt' hIndexSize,
    UInt64.toNat_ofNat_of_lt' hIndexSuccSize]
  omega

theorem foldResultProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (root : UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hRoot : frame.get 7 = some (.i64 root))
    (hAccumulator : frame.get 1 = some (.i64
      (input.foldl (fun sum element => sum + element) 0)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ resultFrame, FoldResult inputPtr input root resultFrame →
      wp module_ rest Q st resultFrame env) :
    wp module_ (foldResultProgram ++ rest) Q st frame env := by
  have hRootLocal : frame.locals[6]? = some (.i64 root) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hRoot
  have hRootValue : frame.locals[6] = .i64 root := by
    rw [List.getElem?_eq_getElem (by omega)] at hRootLocal
    exact Option.some.inj hRootLocal
  have hAccumulatorLocal : frame.locals[0]? = some (.i64
      (input.foldl (fun sum element => sum + element) 0)) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hAccumulator
  have hAccumulatorValue : frame.locals[0] = .i64
      (input.foldl (fun sum element => sum + element) 0) := by
    rw [List.getElem?_eq_getElem (by omega)] at hAccumulatorLocal
    exact Option.some.inj hAccumulatorLocal
  unfold foldResultProgram
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    List.getElem?_set, hParams, hLocals, hValues, hAccumulator]
  apply hNext
  simp [FoldResult, Wasm.Locals.get, List.length_set,
    List.getElem?_set, hParams, hLocals, hValues, hRootLocal]
  exact ⟨hRootValue, hAccumulatorValue⟩

set_option maxHeartbeats 5000000 in
theorem foldProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (root : UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hRoot : frame.get 7 = some (.i64 root))
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ resultFrame, FoldResult inputPtr input root resultFrame →
      wp module_ rest Q st resultFrame env) :
    wp module_
      (AnnotationMatches.function_0_array_fold_0_program ++ rest)
      Q st frame env := by
  rw [annotatedFoldProgram_eq]
  unfold foldProgram foldSetupProgram
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    List.getElem?_set, hParams, hLocals, hValues, hLengthRead,
    hLengthBound, hInputAddress]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    List.getElem?_set, hLocals]
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := FoldInv st inputPtr input root)
    (μ := foldMeasure input)
  · have hRootLocal : frame.locals[6]? = some (.i64 root) := by
      simpa [Wasm.Locals.get, hParams, hLocals] using hRoot
    have hRootValue : frame.locals[6] = .i64 root := by
      rw [List.getElem?_eq_getElem (by omega)] at hRootLocal
      exact Option.some.inj hRootLocal
    refine ⟨0, by omega, rfl, rfl, ?_⟩
    simp [Wasm.Locals.get, List.length_set, List.getElem?_set,
      hLocals, hRootValue, ArrayFold.foldPrefix]
  · intro st' current hInv
    rcases hInv with
      ⟨index, hIndexLe, rfl, hParams', hLocals', hValues', hRoot',
        hArrayLocal, hIndexLocal, hStopLocal, hAccumulator⟩
    have hRootOption : current.locals[6]? = some (.i64 root) := by
      simpa [Wasm.Locals.get, hParams', hLocals'] using hRoot'
    have hRootValue : current.locals[6] = .i64 root := by
      rw [List.getElem?_eq_getElem (by omega)] at hRootOption
      exact Option.some.inj hRootOption
    have hArrayOption : current.locals[10]? = some (.i64 inputPtr) := by
      simpa [Wasm.Locals.get, hParams', hLocals'] using hArrayLocal
    have hArrayValue : current.locals[10] = .i64 inputPtr := by
      rw [List.getElem?_eq_getElem (by omega)] at hArrayOption
      exact Option.some.inj hArrayOption
    have hIndexOption : current.locals[12]? =
        some (.i64 (UInt64.ofNat index)) := by
      simpa [Wasm.Locals.get, hParams', hLocals'] using hIndexLocal
    have hIndexValue : current.locals[12] =
        .i64 (UInt64.ofNat index) := by
      rw [List.getElem?_eq_getElem (by omega)] at hIndexOption
      exact Option.some.inj hIndexOption
    have hStopOption : current.locals[14]? =
        some (.i64 (UInt64.ofNat input.size)) := by
      simpa [Wasm.Locals.get, hParams', hLocals'] using hStopLocal
    have hStopValue : current.locals[14] =
        .i64 (UInt64.ofNat input.size) := by
      rw [List.getElem?_eq_getElem (by omega)] at hStopOption
      exact Option.some.inj hStopOption
    have hAccumulatorOption : current.locals[0]? =
        some (.i64 (ArrayFold.foldPrefix input
          (fun sum element => sum + element) 0 index)) := by
      simpa [Wasm.Locals.get, hParams', hLocals'] using hAccumulator
    have hAccumulatorValue : current.locals[0] =
        .i64 (ArrayFold.foldPrefix input
          (fun sum element => sum + element) 0 index) := by
      rw [List.getElem?_eq_getElem (by omega)] at hAccumulatorOption
      exact Option.some.inj hAccumulatorOption
    have hItem : current.validIndex 2 := by
      simp [Wasm.Locals.validIndex, hParams', hLocals']
    by_cases hIndex : index < input.size
    · unfold foldBodyProgram
      apply FixedArrayTraversalInput.continuingProgram_spec
        11 13 15 2 module_ env st' current inputPtr
          (UInt64.ofNat index) (UInt64.ofNat input.size) input index
          (hItem := hItem) (hInput := hInput) (hIndex := hIndex)
      · exact hValues'
      · exact hArrayLocal
      · exact hIndexLocal
      · exact hStopLocal
      · rfl
      · have hIndexSize : index < UInt64.size :=
          lt_trans hIndex hInput.size_lt
        rw [UInt64.lt_iff_toNat_lt,
          UInt64.toNat_ofNat_of_lt' hIndexSize,
          UInt64.toNat_ofNat_of_lt' hInput.size_lt]
        exact hIndex
      · have hPrefixNext := (ArrayFold.foldPrefix_succ input
          (fun sum element : UInt64 => sum + element) 0 index hIndex).symm
        have hIndexSize : index < UInt64.size :=
          lt_trans hIndex hInput.size_lt
        have hIndexSuccSize : index + 1 < UInt64.size := by
          exact lt_of_le_of_lt (by omega) hInput.size_lt
        have hIndexSucc :
            UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
          change UInt64.ofNat index + UInt64.ofNat 1 =
            UInt64.ofNat (index + 1)
          rw [← UInt64.ofNat_add]
        unfold foldStepSuffix
        simp (config := { maxSteps := 10000000 }) [wp_simp,
          FixedArrayTraversalInput.dynamicResultFrame, Wasm.Locals.set,
          Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
          List.getElem?_set, hParams', hLocals', hValues', hRootValue,
          hArrayValue, hIndexValue, hStopValue, hAccumulatorValue,
          hPrefixNext]
        rw [hIndexSucc]
        change
          FoldInv st' inputPtr input root st'
              (foldNextFrame current inputPtr input[index]
                (ArrayFold.foldPrefix input
                  (fun sum element => sum + element) 0 (index + 1))
                (UInt64.ofNat (index + 1))) ∧
            foldMeasure input st'
                (foldNextFrame current inputPtr input[index]
                  (ArrayFold.foldPrefix input
                    (fun sum element => sum + element) 0 (index + 1))
                  (UInt64.ofNat (index + 1))) <
              foldMeasure input st' current
        exact ⟨foldNextFrame_inv st' current inputPtr input root index
            (by omega) hLocals' hRootValue hArrayValue hStopValue,
          foldNextFrame_measure st' current inputPtr input index hLocals'
            hIndexLocal hIndex hIndexSize hIndexSuccSize⟩
    · have hDone : index = input.size := by
        omega
      subst index
      rw [ArrayFold.foldPrefix_size] at hAccumulator
      have hStopLocalAfter :
          ({ current with values := [.i64 (UInt64.ofNat input.size)] } :
            Locals).get 15 = some (.i64 (UInt64.ofNat input.size)) := by
        simpa [Wasm.Locals.get] using hStopLocal
      unfold foldBodyProgram FixedArrayTraversalInput.continuingProgram
      rw [List.append_assoc]
      simp only [List.cons_append, List.nil_append, wp_simp, hValues',
        hIndexLocal, hStopLocalAfter]
      rw [if_pos (by simp)]
      change wp module_ (foldResultProgram ++ rest) Q st'
        { params := current.params, locals := current.locals } env
      have hCurrent :
          ({ params := current.params, locals := current.locals } : Locals) =
            current := by
        cases current
        simp_all
      rw [hCurrent]
      apply foldResultProgram_spec module_ env st' current inputPtr input root
        hParams' hLocals' hValues' hRoot' hAccumulator Q rest hNext

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
  all_goals try rfl
  all_goals try decide
  case hInputLocal =>
    simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  case hValid =>
    intro hSize
    have hExpected : FormalSpec.expected input =
        #[input.foldl (fun sum element => sum + element) 0] := by
      simp [FormalSpec.expected, hSize]
    have hFitMemory : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change wp module
      (resultCapacityPrefix 1 ++
        FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
    apply resultCapacityPrefix_spec 1 module env initial
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · decide
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
      initial _ heapTop (resultCapacity 1) 1 allocs
    · simp [resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · simp [resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · simp [resultCapacityFrame, resultCapacity,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · decide
    · simpa [resultCapacity] using hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    let allocSt := FixedArrayAllocator.allocStore initial heapTop
      (resultCapacity 1) 1 allocs
    let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
      (resultCapacityFrame
        (FixedArrayLengthDispatch.branchFrame 7
          (func0Def.toLocals
            (List.take func0Def.numParams [.i64 inputPtr]).reverse)
          inputPtr)
        (resultCapacity 1))
      heapTop (resultCapacity 1)
    have hAllocParams : allocFrame.params = [.i64 inputPtr] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
        resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    have hAllocLocals : allocFrame.locals.length = 20 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
        resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    have hAllocValues : allocFrame.values = [] := by
      rfl
    have hRoot : allocFrame.get 7 = some (.i64 (heapTop + 48)) := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame,
        resultCapacityFrame, resultCapacity,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    have hFacts := Allocation.bumpFacts heapTop (resultCapacity 1)
      initial.mem.pages (by simpa [resultCapacity] using hFitMemory) hPages
    have hRootAddress : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hFacts.wordAddress_toNat 0 (by decide)
    have hPayloadAddress :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
          heapTop.toNat + 48 + 8 := by
      simpa [FixedArrayResult.payloadAddress] using
        hFacts.wordAddress_toNat 1 (by decide)
    have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
        allocSt.mem.pages * 65536 := by
      rw [hRootAddress]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hPayloadBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 1).mem.pages *
            65536 := by
      rw [hPayloadAddress, FixedArrayResult.writeLength_pages]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
      apply FixedArrayPairResult.input_preserved_by_alloc initial heapTop
        (resultCapacity 1) 1 allocs inputPtr input hArray hInputBelow
      · simpa [resultCapacity] using hFitMemory
      · exact hPages
    have hInputAfterLength : UInt64Array.At
        (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
        inputPtr input := by
      have hAfter : inputPtr.toNat + 8 * (input.size + 1) ≤
          (heapTop + 48).toUInt32.toNat := by
        rw [hRootAddress]
        omega
      simpa [FixedArrayResult.writeLength] using
        hInputAlloc.write64After hAfter
    have hFit32 : heapTop.toNat + 48 + 16 ≤ 4294967296 := by
      simpa [hExpected] using hOutputFit32
    have hSingleton := FixedArrayResult.singletonStore_at allocSt
      (heapTop + 48)
      (input.foldl (fun sum element => sum + element) 0)
      (by rw [hFacts.rootToNat]; omega) (by
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        rw [hFacts.rootToNat]
        omega)
    change wp module
      (FixedArrayResult.lengthStoreProgram 7 1 ++ _) _ allocSt allocFrame env
    apply FixedArrayResult.lengthStore_spec module env allocSt allocFrame
      (heapTop + 48) 1 7 hAllocValues hRoot hRootBound
    change wp module
      (AnnotationMatches.function_0_array_fold_0_program ++ _) _
      (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
      allocFrame env
    apply foldProgram_spec module env
      (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
      allocFrame inputPtr input (heapTop + 48) hAllocParams hAllocLocals
      hAllocValues hRoot hInputAfterLength
    intro resultFrame hFold
    rcases hFold with
      ⟨hResultParams, hResultLocals, hResultValues, hResultRoot,
        hResultSum⟩
    change wp module
      (FixedArrayResult.payloadStoreProgram 7 10 0 ++ _) _
      (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
      resultFrame env
    apply FixedArrayResult.payloadStore_spec module env
      (FixedArrayResult.writeLength allocSt (heapTop + 48) 1)
      resultFrame (heapTop + 48)
      (input.foldl (fun sum element => sum + element) 0) 7 10 0
      hResultRoot hResultSum hPayloadBound
    have hRootOption : resultFrame.locals[6]? =
        some (.i64 (heapTop + 48)) := by
      simpa [Wasm.Locals.get, hResultParams, hResultLocals] using hResultRoot
    have hRootValue : resultFrame.locals[6] = .i64 (heapTop + 48) := by
      rw [List.getElem?_eq_getElem (by omega)] at hRootOption
      exact Option.some.inj hRootOption
    simp (config := { maxSteps := 10000000 }) [wp_simp, hRootValue,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      List.length_set, List.getElem?_set, hResultParams, hResultLocals,
      hResultValues, FixedArrayEqNode.branchPost, func0Def,
      Function.toLocals, Function.numParams, ValueType.zero, hExpected]
    change UInt64Array.At
      (FixedArrayResult.singletonStore allocSt (heapTop + 48)
        (input.foldl (fun sum element => sum + element) 0))
      (heapTop + 48)
      #[input.foldl (fun sum element => sum + element) 0]
    exact hSingleton
  case hInvalid =>
    intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hFitMemory : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change wp module
      (resultCapacityPrefix 0 ++
        FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
    apply resultCapacityPrefix_spec 0 module env initial
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · decide
    apply FixedArrayAllocatorWindow.region_spec_withTail 2 4 module env
      initial _ heapTop (resultCapacity 0) 1 allocs
    · simp [resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · simp [resultCapacityFrame, FixedArrayLengthDispatch.branchFrame,
        func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    · rfl
    · simp [resultCapacityFrame, resultCapacity,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · decide
    · simpa [resultCapacity] using hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    have hRoot :
        (FixedArrayAllocatorWindow.allocFrame 2
          (resultCapacityFrame
            (FixedArrayLengthDispatch.branchFrame 7
              (func0Def.toLocals
                (List.take func0Def.numParams [.i64 inputPtr]).reverse)
              inputPtr)
            (resultCapacity 0))
          heapTop (resultCapacity 0)).get 7 =
          some (.i64 (heapTop + 48)) := by
      simp [FixedArrayAllocatorWindow.allocFrame, resultCapacityFrame,
        resultCapacity, FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    apply FixedArrayResult.lengthStore_spec
      (root := heapTop + 48) (length := 0) (rootLocal := 7)
    · rfl
    · exact hRoot
    · have hFacts := Allocation.bumpFacts heapTop (resultCapacity 0)
        initial.mem.pages (by simpa [resultCapacity] using hFitMemory) hPages
      have hRootAddress : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hFacts.wordAddress_toNat 0 (by decide)
      rw [hRootAddress]
      simpa [FixedArrayAllocator.allocStore_pages] using hFitMemory
    · have hFacts := Allocation.bumpFacts heapTop (resultCapacity 0)
        initial.mem.pages (by simpa [resultCapacity] using hFitMemory) hPages
      have hFit32 : heapTop.toNat + 48 + 8 ≤ 4294967296 := by
        simpa [hExpected] using hOutputFit32
      have hEmpty : UInt64Array.At
          (FixedArrayResult.writeLength
            (FixedArrayAllocator.allocStore initial heapTop
              (resultCapacity 0) 1 allocs)
            (heapTop + 48) 0)
          (heapTop + 48) #[] := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hFacts.rootToNat]
          exact hFit32
        · rw [hFacts.rootToNat, FixedArrayResult.writeLength_pages,
              FixedArrayAllocator.allocStore_pages]
          exact hFitMemory
        · simp [FixedArrayResult.writeLength]
        · intro i hi
          simp at hi
      simp (config := { maxSteps := 10000000 }) [wp_simp, hRoot,
        Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
        List.length_set, List.getElem?_set,
        FixedArrayEqNode.branchPost, FixedArrayAllocatorWindow.allocFrame,
        resultCapacityFrame, resultCapacity,
        FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero,
        hExpected]
      change UInt64Array.At
        (FixedArrayResult.writeLength
          (FixedArrayAllocator.allocStore initial heapTop
            (resultCapacity 0) 1 allocs)
          (heapTop + 48) 0)
        (heapTop + 48) #[]
      exact hEmpty

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
