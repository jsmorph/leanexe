import LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec
import LeanExeGen.GeneratedRb9ad29e25c8033e5.Program
import LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches
import Project.ProofKit.Annotation
import Project.ProofKit.Array
import Project.ProofKit.EncodedIndexDecoder
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFindIdxEq
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.Frame

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior

open Wasm Project.ProofKit

private theorem afterDecodedIndexTail_eq :
    ((Annotation.resolve
      AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
      [{ instructionIndex := 20, field := .elseBranch }]).getD []).drop 8 =
      .localGet 4 ::
        ((Annotation.resolve
          AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
          [{ instructionIndex := 20, field := .elseBranch }]).getD []).drop 9 := by
  rfl

private theorem afterDecodedIndexPointerTail_eq :
    ((Annotation.resolve
      AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
      [{ instructionIndex := 20, field := .elseBranch }]).getD []).drop 9 =
      .localGet 3 :: .localSet 8 :: .localGet 8 :: .wrapI64 ::
        .load64 (0 : UInt32) :: .ltUI64 ::
          ((Annotation.resolve
            AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
            [{ instructionIndex := 20, field := .elseBranch }]).getD []).drop 15 := by
  rfl

private def eraseSetupProgram : Wasm.Program :=
  [
    .localGet 10,
    .constI64 1,
    .subI64,
    .localSet 13,
    .localGet 9,
    .constI64 1,
    .mulI64,
    .localSet 11,
    .localGet 13,
    .localGet 9,
    .subI64,
    .constI64 1,
    .mulI64,
    .localSet 12
  ]

private def eraseSetupFrame (frame : Locals) (length index : UInt64) : Locals :=
  { frame with
    locals := (((frame.locals.set 12 (.i64 (length - 1))).set
      10 (.i64 index)).set 11 (.i64 (length - 1 - index)))
    values := [] }

private theorem eraseSetupProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (length index : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 23)
    (hValues : frame.values = [])
    (hLength : frame.get 10 = some (.i64 length))
    (hIndex : frame.get 9 = some (.i64 index))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (eraseSetupFrame frame length index) env) :
    wp module_ (eraseSetupProgram ++ rest) Q st frame env := by
  have hLengthLocal : frame.locals[9] = .i64 length := by
    have h := hLength
    simp only [Wasm.Locals.get, hParams] at h
    rw [if_neg (by omega), if_pos (by omega)] at h
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hIndexLocal : frame.locals[8] = .i64 index := by
    have h := hIndex
    simp only [Wasm.Locals.get, hParams] at h
    rw [if_neg (by omega), if_pos (by omega)] at h
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simpa (config := { maxSteps := 10000000 })
    [eraseSetupProgram, eraseSetupFrame, wp_simp, Wasm.Locals.get,
      Wasm.Locals.set?, hParams, hLocals, hValues, hLength, hIndex,
      hLengthLocal, hIndexLocal, List.length_set, List.getElem?_set]
    using hNext

private def localCapacityProgram
    (lengthLocal : Nat) (stride : UInt64) (capacityLocal : Nat) : Wasm.Program :=
  [
    .constI64 8,
    .localGet lengthLocal,
    .constI64 stride,
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
    .localSet capacityLocal,
    .localGet capacityLocal,
    .constI64 8,
    .ltUI64,
    .iff 0 0 [.constI64 8, .localSet capacityLocal] []
  ]

private theorem localCapacityProgram_spec
    (lengthLocal : Nat) (stride : UInt64) (capacityLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (length : UInt64)
    (hValues : frame.values = [])
    (hLength : frame.get lengthLocal = some (.i64 length))
    (hCapacityLocal : frame.params.length ≤ capacityLocal)
    (hCapacityValid : frame.validIndex capacityLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (FixedArrayCapacity.capacityFrame frame capacityLocal
        (FixedArrayCapacity.normalizedCapacity length stride)) env) :
    wp module_ (localCapacityProgram lengthLocal stride capacityLocal ++ rest)
      Q st frame env := by
  have hLengthAfter (values : List Value) :
      ({ frame with values := values } : Locals).get lengthLocal =
        some (.i64 length) := by
    simpa only [Wasm.Locals.get] using hLength
  have hNotParam : ¬capacityLocal < frame.params.length :=
    Nat.not_lt.mpr hCapacityLocal
  have hCapacityBound :
      capacityLocal < frame.params.length + frame.locals.length :=
    hCapacityValid
  have hLocal :
      capacityLocal - frame.params.length < frame.locals.length := by
    omega
  unfold localCapacityProgram
  simp only [List.cons_append, List.nil_append, wp_constI64_cons,
    wp_localGet_cons, hLengthAfter]
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set, hValues,
    hNotParam, hCapacityBound, hLocal]
  refine wp_iff_cons rfl ?_
  by_cases hSmall : FixedArrayCapacity.unnormalizedCapacity length stride < 8
  · have hSmall' : (8 + length * stride * 8 + 7) / 8 * 8 < 8 := by
      simpa [FixedArrayCapacity.unnormalizedCapacity] using hSmall
    simp only [hSmall', if_pos]
    simpa [FixedArrayCapacity.capacityFrame,
      FixedArrayCapacity.normalizedCapacity, hSmall, hValues,
      hNotParam, hCapacityBound] using hNext
  · have hSmall' : ¬(8 + length * stride * 8 + 7) / 8 * 8 < 8 := by
      simpa [FixedArrayCapacity.unnormalizedCapacity] using hSmall
    simp only [hSmall', if_false]
    simpa [FixedArrayCapacity.capacityFrame,
      FixedArrayCapacity.normalizedCapacity,
      FixedArrayCapacity.unnormalizedCapacity, hSmall, hSmall', hValues,
      hNotParam, hCapacityBound] using hNext

private abbrev successfulRemovalBody : Wasm.Program :=
  ((Annotation.resolve func0
    [{ instructionIndex := 7, field := .thenBranch },
      { instructionIndex := 20, field := .elseBranch },
      { instructionIndex := 15, field := .thenBranch },
      { instructionIndex := 11, field := .thenBranch }]).getD [])

private theorem successfulRemovalSetupTail_eq :
    successfulRemovalBody.drop 0 =
      eraseSetupProgram ++ successfulRemovalBody.drop 14 := by
  rfl

private theorem successfulRemovalCapacityTail_eq :
    successfulRemovalBody.drop 14 =
      localCapacityProgram 13 1 18 ++ successfulRemovalBody.drop 32 := by
  rfl

private theorem successfulRemovalAllocatorTail_eq :
    successfulRemovalBody.drop 32 =
      FixedArrayAllocatorWindow.region 9 1 ++
        successfulRemovalBody.drop 49 := by
  rfl

private theorem successfulRemovalLengthTail_eq :
    successfulRemovalBody.drop 49 =
      FixedArrayResult.lengthStoreLocalProgram 14 13 ++
        successfulRemovalBody.drop 53 := by
  rfl

private theorem successfulRemovalFinishTail_eq :
    successfulRemovalBody.drop 59 = [.localGet 14] := by
  rfl

private abbrev oversizedBody : Wasm.Program :=
  AnnotationMatches.function_0_length_dispatch_0_invalid_branch_program

private theorem oversizedCapacityAllocatorTail_eq :
    oversizedBody.drop 0 =
      FixedArrayCapacity.constantProgram 0 1 12 ++
        (FixedArrayAllocatorWindow.region 3 1 ++ oversizedBody.drop 35) := by
  rfl

private theorem oversizedLengthTail_eq :
    oversizedBody.drop 35 =
      FixedArrayResult.lengthStoreProgram 8 0 ++ oversizedBody.drop 39 := by
  rfl

private theorem oversizedFinishTail_eq :
    oversizedBody.drop 39 = FixedArrayResult.finishProgram 8 6 7 := by
  rfl

private def oversizedBaseFrame (inputPtr : UInt64) : Locals :=
  FixedArrayLengthDispatch.branchFrame 8
    (func0Def.toLocals
      (List.take func0Def.numParams [.i64 inputPtr]).reverse)
    inputPtr

private abbrev oversizedAllocatedFrame
    (inputPtr heapTop : UInt64) : Locals :=
  FixedArrayAllocatorWindow.allocFrame 3
    (FixedArrayCapacity.capacityFrame (oversizedBaseFrame inputPtr) 12
      (FixedArrayCapacity.normalizedCapacity 0 1))
    heapTop (FixedArrayCapacity.normalizedCapacity 0 1)

private theorem oversizedBaseFrame_params_length (inputPtr : UInt64) :
    (oversizedBaseFrame inputPtr).params.length = 1 := by
  simp [oversizedBaseFrame, FixedArrayLengthDispatch.branchFrame,
    func0Def, Function.toLocals, Function.numParams, ValueType.zero]

private theorem oversizedBaseFrame_locals_length (inputPtr : UInt64) :
    (oversizedBaseFrame inputPtr).locals.length = 23 := by
  simp [oversizedBaseFrame, FixedArrayLengthDispatch.branchFrame,
    func0Def, Function.toLocals, Function.numParams, ValueType.zero]

private theorem oversizedAllocatedFrame_params_length
    (inputPtr heapTop : UInt64) :
    (oversizedAllocatedFrame inputPtr heapTop).params.length = 1 := by
  rw [FixedArrayAllocatorWindow.allocFrame_params,
    FixedArrayCapacity.capacityFrame_params]
  exact oversizedBaseFrame_params_length inputPtr

private theorem oversizedAllocatedFrame_locals_length
    (inputPtr heapTop : UInt64) :
    (oversizedAllocatedFrame inputPtr heapTop).locals.length = 23 := by
  rw [FixedArrayAllocatorWindow.allocFrame_locals_length,
    FixedArrayCapacity.capacityFrame_locals_length]
  exact oversizedBaseFrame_locals_length inputPtr

private theorem oversizedAllocatedFrame_values
    (inputPtr heapTop : UInt64) :
    (oversizedAllocatedFrame inputPtr heapTop).values = [] := by
  rfl

private theorem oversizedAllocatedFrame_root
    (inputPtr heapTop : UInt64) :
    (oversizedAllocatedFrame inputPtr heapTop).get 8 =
      some (.i64 (heapTop + 48)) := by
  apply FixedArrayAllocatorWindow.allocFrame_get_root
      (offset := 3) (tail := 6)
  · rw [FixedArrayCapacity.capacityFrame_params]
    exact oversizedBaseFrame_params_length inputPtr
  · rw [FixedArrayCapacity.capacityFrame_locals_length]
    exact oversizedBaseFrame_locals_length inputPtr

private abbrev removalFrame (base : Locals) (length index capacity heapTop : UInt64) :
    Locals :=
  FixedArrayAllocatorWindow.allocFrame 9
    (FixedArrayCapacity.capacityFrame
      (eraseSetupFrame base length index) 18 capacity)
    heapTop capacity

private theorem removalFrame_params_length
    (base : Locals) (length index capacity heapTop : UInt64) :
    (removalFrame base length index capacity heapTop).params.length =
      base.params.length := by
  simp [removalFrame, FixedArrayAllocatorWindow.allocFrame_params,
    FixedArrayCapacity.capacityFrame_params, eraseSetupFrame]

private theorem removalFrame_locals_length
    (base : Locals) (length index capacity heapTop : UInt64) :
    (removalFrame base length index capacity heapTop).locals.length =
      base.locals.length := by
  simp [removalFrame, FixedArrayAllocatorWindow.allocFrame_locals_length,
    FixedArrayCapacity.capacityFrame_locals_length, eraseSetupFrame,
    List.length_set]

private def successfulBaseFrame
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat) : Locals :=
  let found := FixedArrayFindIdxEq.someFrame 8
    { params := [.i64 inputPtr]
      locals :=
        [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 inputPtr, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0]
      values := [] }
    inputPtr input index
  let locals1 := found.locals.set 1
    (.i64 (FixedArrayFindIdxEq.encodedIndex index))
  let locals2 := locals1.set 2 (.i64 inputPtr)
  let locals3 := locals2.set 7
    (.i64 (FixedArrayFindIdxEq.encodedIndex index))
  let locals4 := locals3.set 8 (.i64 1)
  let locals5 := locals4.set 3 (.i64 (UInt64.ofNat index))
  let locals6 := locals5.set 7 (.i64 inputPtr)
  let locals7 := locals6.set 8 (.i64 (UInt64.ofNat index))
  let locals8 := locals7.set 9 (.i64 (UInt64.ofNat input.size))
  { params := [.i64 inputPtr]
    locals := locals8
    values := [] }

private theorem successfulBaseFrame_params_length
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat) :
    (successfulBaseFrame inputPtr input index).params.length = 1 := by
  simp [successfulBaseFrame, FixedArrayFindIdxEq.someFrame_params]

private theorem successfulBaseFrame_locals_length
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat) :
    (successfulBaseFrame inputPtr input index).locals.length = 23 := by
  simp [successfulBaseFrame,
    FixedArrayFindIdxEq.someFrame_locals_length, List.length_set]

private abbrev successfulRemovalFrame
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) : Locals :=
  removalFrame (successfulBaseFrame inputPtr input index)
    (UInt64.ofNat input.size) (UInt64.ofNat index) capacity heapTop

private theorem removalFrame_values
    (base : Locals) (length index capacity heapTop : UInt64) :
    (removalFrame base length index capacity heapTop).values = [] := by
  rfl

private theorem removalFrame_counter_valid
    (base : Locals) (length index capacity heapTop : UInt64)
    (hParams : base.params.length = 1)
    (hLocals : base.locals.length = 23) :
    (removalFrame base length index capacity heapTop).validIndex 15 := by
  simp [removalFrame, Wasm.Locals.validIndex,
    FixedArrayAllocatorWindow.allocFrame_params,
    FixedArrayAllocatorWindow.allocFrame_locals_length,
    FixedArrayCapacity.capacityFrame_params,
    FixedArrayCapacity.capacityFrame_locals_length, eraseSetupFrame,
    hParams, hLocals]

private theorem removalFrame_source
    (base : Locals) (length index capacity heapTop source : UInt64)
    (hParams : base.params.length = 1)
    (hLocals : base.locals.length = 23)
    (hSource : base.get 8 = some (.i64 source)) :
    (removalFrame base length index capacity heapTop).get 8 =
      some (.i64 source) := by
  have hSourceLocal : base.locals[7] = .i64 source := by
    have h := hSource
    simp only [Wasm.Locals.get, hParams] at h
    rw [if_neg (by omega), if_pos (by omega)] at h
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp [removalFrame, FixedArrayAllocatorWindow.allocFrame,
    FixedArrayCapacity.capacityFrame, eraseSetupFrame, Wasm.Locals.get,
    hParams, hLocals, hSourceLocal, List.length_set, List.getElem?_set]

private theorem removalFrame_prefix
    (base : Locals) (length index capacity heapTop : UInt64)
    (hParams : base.params.length = 1)
    (hLocals : base.locals.length = 23) :
    (removalFrame base length index capacity heapTop).get 11 =
      some (.i64 index) := by
  simp [removalFrame, FixedArrayAllocatorWindow.allocFrame,
    FixedArrayCapacity.capacityFrame, eraseSetupFrame, Wasm.Locals.get,
    hParams, hLocals, List.length_set, List.getElem?_set]

private theorem removalFrame_suffix
    (base : Locals) (length index capacity heapTop : UInt64)
    (hParams : base.params.length = 1)
    (hLocals : base.locals.length = 23) :
    (removalFrame base length index capacity heapTop).get 12 =
      some (.i64 (length - 1 - index)) := by
  simp [removalFrame, FixedArrayAllocatorWindow.allocFrame,
    FixedArrayCapacity.capacityFrame, eraseSetupFrame, Wasm.Locals.get,
    hParams, hLocals, List.length_set, List.getElem?_set]

private theorem removalFrame_target
    (base : Locals) (length index capacity heapTop : UInt64)
    (hParams : base.params.length = 1)
    (hLocals : base.locals.length = 23) :
    (removalFrame base length index capacity heapTop).get 14 =
      some (.i64 (heapTop + 48)) := by
  apply FixedArrayAllocatorWindow.allocFrame_get_root
      (offset := 9) (tail := 0)
  · simpa [FixedArrayCapacity.capacityFrame, eraseSetupFrame] using hParams
  · simpa [FixedArrayCapacity.capacityFrame, eraseSetupFrame] using hLocals

private theorem successfulRemovalFrame_root
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulRemovalFrame inputPtr input index capacity heapTop).get 14 =
      some (.i64 (heapTop + 48)) := by
  apply removalFrame_target
  · exact successfulBaseFrame_params_length inputPtr input index
  · exact successfulBaseFrame_locals_length inputPtr input index

private theorem successfulRemovalFrame_counter_valid
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulRemovalFrame inputPtr input index capacity heapTop).validIndex 15 := by
  apply removalFrame_counter_valid
  · exact successfulBaseFrame_params_length inputPtr input index
  · exact successfulBaseFrame_locals_length inputPtr input index

private def successfulCopyFrame
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) : Locals :=
  FixedArrayCopy.counterFrame
    (successfulRemovalFrame inputPtr input index capacity heapTop)
    15 (input.size - 1 - index)
    (successfulRemovalFrame_counter_valid
      inputPtr input index capacity heapTop)

private theorem successfulCopyFrame_params_length
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulCopyFrame inputPtr input index capacity heapTop).params.length = 1 := by
  rw [successfulCopyFrame, FixedArrayCopy.counterFrame_params_length,
    removalFrame_params_length]
  exact successfulBaseFrame_params_length inputPtr input index

private theorem successfulCopyFrame_locals_length
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulCopyFrame inputPtr input index capacity heapTop).locals.length = 23 := by
  rw [successfulCopyFrame, FixedArrayCopy.counterFrame_locals_length,
    removalFrame_locals_length]
  exact successfulBaseFrame_locals_length inputPtr input index

private theorem successfulCopyFrame_values
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulCopyFrame inputPtr input index capacity heapTop).values = [] := by
  rfl

private theorem successfulCopyFrame_root
    (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (capacity heapTop : UInt64) :
    (successfulCopyFrame inputPtr input index capacity heapTop).get 14 =
      some (.i64 (heapTop + 48)) := by
  rw [successfulCopyFrame, FixedArrayCopy.counterFrame_get_ne]
  · exact successfulRemovalFrame_root
      inputPtr input index capacity heapTop
  · norm_num

set_option maxHeartbeats 4000000 in
theorem artifact_behavior :
    LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» := by
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
  wp_fixed_array_length_le_dispatch_from hArray at 8, 8
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  · norm_num
  · intro hSize
    change wp module
      (((Annotation.resolve func0
        [{ instructionIndex := 7, field := .thenBranch }]).getD []).drop 0)
      _ _ _ _
    rw [AnnotationMatches.function_0_find_idx_eq_0_tail_eq]
    apply FixedArrayFindIdxEq.program_spec (scratch := 8) (tail := 12)
      (inputPtr := inputPtr) (input := input)
    · norm_num
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · simp [FixedArrayLengthDispatch.branchFrame, func0Def,
        Function.toLocals, Function.numParams, ValueType.zero]
    · exact hArray
    · intro hFind item
      change input.findIdx? (fun element => element == (0 : UInt64)) = none
        at hFind
      have hExpected : FormalSpec.expected input = input := by
        simp [FormalSpec.expected, hSize, hFind]
      change wp module
        (AnnotationMatches.function_0_length_dispatch_0_valid_branch_program.drop 12)
        _ _ _ _
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [AnnotationMatches.function_0_length_dispatch_0_valid_branch_program,
          wp_simp,
          FixedArrayFindIdxEq.noneFrame,
          FixedArrayFindIdxEq.loopFrame, FixedArrayFindIdxEq.setupFrame,
          FixedArrayLengthDispatch.branchFrame, FixedArrayEqNode.branchPost,
          Wasm.Locals.get, Wasm.Locals.set?, List.getElem?_set,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          func0Def, Function.toLocals, Function.numParams, ValueType.zero,
          hExpected, hArray]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [wp_simp, FixedArrayEqNode.branchPost, Wasm.Locals.get,
          Wasm.Locals.set?, List.getElem?_set, List.getElem?_cons_zero,
          List.getElem?_cons_succ, hArray]
      change UInt64Array.At initial inputPtr input
      exact hArray
    · intro index hIndex hFind
      have hIndexSucc : index + 1 < UInt64.size := by
        have hInputSize := hArray.size_lt
        omega
      have hEncodedNe : FixedArrayFindIdxEq.encodedIndex index ≠ 0 :=
        FixedArrayFindIdxEq.encodedIndex_ne_zero hIndexSucc
      change input.findIdx? (fun element => element == (0 : UInt64)) =
        some index at hFind
      have hExpected : FormalSpec.expected input = input.eraseIdx! index := by
        simp [FormalSpec.expected, hSize, hFind]
      change wp module
        (AnnotationMatches.function_0_length_dispatch_0_valid_branch_program.drop 12)
        _ _ _ _
      simp (config := { maxSteps := 10000000 }) (discharger := omega)
        [AnnotationMatches.function_0_length_dispatch_0_valid_branch_program,
          wp_simp, FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayFindIdxEq.someFrame_values,
          FixedArrayLengthDispatch.branchFrame, Wasm.Locals.get,
          Wasm.Locals.set?, List.length_set, List.getElem?_set,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          func0Def, Function.toLocals, Function.numParams, ValueType.zero,
          hEncodedNe, hExpected]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      simp only [wp_localGet_cons]
      simp (config := { maxSteps := 10000000 }) (discharger := omega) only
        [FixedArrayFindIdxEq.someFrame_params,
          FixedArrayLengthDispatch.branchFrame_params,
          Wasm.Locals.get, List.length, List.length_set,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true]
      simp only [wp_localSet_cons]
      simp (config := { maxSteps := 10000000 }) (discharger := omega) only
        [FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length,
          FixedArrayLengthDispatch.branchFrame_params,
          FixedArrayLengthDispatch.branchFrame_locals_length,
          Wasm.Locals.set?, List.length, List.length_set,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true]
      change wp module
        (((Annotation.resolve func0
          [{ instructionIndex := 7, field := .thenBranch },
            { instructionIndex := 20, field := .elseBranch }]).getD []).drop 2)
        _ _ _ _
      rw [AnnotationMatches.function_0_encoded_index_0_tail_eq]
      apply EncodedIndexDecoder.program_spec
        (encodedLocal := 2) (scratch := 8) (decodedLocal := 4)
        (encoded := FixedArrayFindIdxEq.encodedIndex index)
      · simp (config := { maxSteps := 10000000 }) (discharger := omega)
          [Wasm.Locals.get, List.length_set, List.getElem?_set,
            FixedArrayFindIdxEq.someFrame_params,
            FixedArrayFindIdxEq.someFrame_locals_length]
      · simp [FixedArrayFindIdxEq.someFrame_params]
      · simp (discharger := omega) [Wasm.Locals.validIndex,
          FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length]
      · simp [FixedArrayFindIdxEq.someFrame_params]
      · simp (discharger := omega) [Wasm.Locals.validIndex,
          FixedArrayFindIdxEq.someFrame_params,
          FixedArrayFindIdxEq.someFrame_locals_length]
      · have hEncodedIndexLt :
            UInt64.ofNat index < UInt64.ofNat input.size := by
          rw [UInt64.lt_iff_toNat_lt,
            UInt64.toNat_ofNat_of_lt' (by omega : index < UInt64.size),
            UInt64.toNat_ofNat_of_lt' hArray.size_lt]
          exact hIndex
        change wp module
          (((Annotation.resolve
            AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
            [{ instructionIndex := 20, field := .elseBranch }]).getD []).drop 8)
          _ _ _ _
        rw [afterDecodedIndexTail_eq]
        simp only [wp_localGet_cons]
        rw [EncodedIndexDecoder.resultFrame_decoded]
        · simp only [hEncodedNe, if_false,
            FixedArrayFindIdxEq.encodedIndex_sub_one]
          rw [afterDecodedIndexPointerTail_eq]
          simp only [wp_localGet_cons]
          rw [Frame.withValues_get]
          rw [EncodedIndexDecoder.resultFrame_get_ne]
          · simp (config := { maxSteps := 10000000 }) (discharger := omega)
              [wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
                List.length_set, List.getElem?_set,
                FixedArrayFindIdxEq.someFrame_params,
                FixedArrayFindIdxEq.someFrame_locals_length,
                hLengthBound, hInputAddress, hLengthRead,
                hEncodedIndexLt]
            rw [if_neg (by omega)]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            simp (config := { maxSteps := 10000000 }) (discharger := omega)
              [Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
                EncodedIndexDecoder.resultFrame,
                FixedArrayFindIdxEq.someFrame_params,
                FixedArrayFindIdxEq.someFrame_locals_length,
                List.length_set, List.getElem?_set,
                List.getElem?_cons_zero, List.getElem?_cons_succ,
                hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one,
                hLengthBound, hInputAddress, hLengthRead,
                hEncodedIndexLt]
            rw [if_neg (by omega)]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simpa using hEncodedIndexLt)]
            change wp module (successfulRemovalBody.drop 0) _ _ _ _
            rw [successfulRemovalSetupTail_eq]
            apply eraseSetupProgram_spec
              (length := UInt64.ofNat input.size)
              (index := UInt64.ofNat index)
            · simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [Wasm.Locals.get, Wasm.Locals.set?,
                  EncodedIndexDecoder.resultFrame,
                  FixedArrayFindIdxEq.someFrame_params,
                  FixedArrayFindIdxEq.someFrame_locals_length,
                  List.length_set, List.getElem?_set,
                  List.getElem?_cons_zero, List.getElem?_cons_succ,
                  hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one]
            · simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [Wasm.Locals.get, Wasm.Locals.set?,
                  EncodedIndexDecoder.resultFrame,
                  FixedArrayFindIdxEq.someFrame_params,
                  FixedArrayFindIdxEq.someFrame_locals_length,
                  List.length_set, List.getElem?_set,
                  List.getElem?_cons_zero, List.getElem?_cons_succ,
                  hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one]
            · simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [Wasm.Locals.get, Wasm.Locals.set?,
                  EncodedIndexDecoder.resultFrame,
                  FixedArrayFindIdxEq.someFrame_params,
                  FixedArrayFindIdxEq.someFrame_locals_length,
                  List.length_set, List.getElem?_set,
                  List.getElem?_cons_zero, List.getElem?_cons_succ,
                  hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one]
            · simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [Wasm.Locals.get, Wasm.Locals.set?,
                  EncodedIndexDecoder.resultFrame,
                  FixedArrayFindIdxEq.someFrame_params,
                  FixedArrayFindIdxEq.someFrame_locals_length,
                  List.length_set, List.getElem?_set,
                  List.getElem?_cons_zero, List.getElem?_cons_succ,
                  hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one]
            · simp (config := { maxSteps := 10000000 })
                (discharger := omega)
                [Wasm.Locals.get, Wasm.Locals.set?,
                  EncodedIndexDecoder.resultFrame,
                  FixedArrayFindIdxEq.someFrame_params,
                  FixedArrayFindIdxEq.someFrame_locals_length,
                  List.length_set, List.getElem?_set,
                  List.getElem?_cons_zero, List.getElem?_cons_succ,
                  hEncodedNe, FixedArrayFindIdxEq.encodedIndex_sub_one]
            · rw [successfulRemovalCapacityTail_eq]
              apply localCapacityProgram_spec
                (length := UInt64.ofNat input.size - 1)
              · simp [eraseSetupFrame]
              · simp (discharger := omega)
                  [eraseSetupFrame, Wasm.Locals.get,
                    List.length_set, List.getElem?_set]
              · simp [eraseSetupFrame]
              · simp (discharger := omega)
                  [eraseSetupFrame, Wasm.Locals.validIndex,
                    List.length_set]
              · have hCapacityEq :
                    FixedArrayCapacity.normalizedCapacity
                        (UInt64.ofNat input.size - 1) 1 =
                      UInt64.ofNat (8 * input.size) := by
                  interval_cases hInputSize : input.size
                  all_goals first | omega | native_decide
                rw [successfulRemovalAllocatorTail_eq]
                apply FixedArrayAllocatorWindow.region_spec_withTail
                  (offset := 9) (tail := 0) (heapTop := heapTop)
                  (capacity := FixedArrayCapacity.normalizedCapacity
                    (UInt64.ofNat input.size - 1) 1)
                  (stride := 1) (allocs := allocs)
                · simp (config := { maxSteps := 10000000 })
                    (discharger := omega)
                    [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                      EncodedIndexDecoder.resultFrame,
                      FixedArrayFindIdxEq.someFrame_params,
                      FixedArrayFindIdxEq.someFrame_locals_length,
                      List.length_set, hEncodedNe]
                · simp (config := { maxSteps := 10000000 })
                    (discharger := omega)
                    [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                      EncodedIndexDecoder.resultFrame,
                      FixedArrayFindIdxEq.someFrame_params,
                      FixedArrayFindIdxEq.someFrame_locals_length,
                      List.length_set, hEncodedNe]
                · simp [FixedArrayCapacity.capacityFrame, eraseSetupFrame]
                · simp (discharger := omega)
                    [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                      List.length_set, List.getElem?_set]
                · exact FixedArrayCapacity.normalizedCapacity_toNat_ge_eight
                    (UInt64.ofNat input.size - 1) 1
                · rw [hCapacityEq,
                    UInt64.toNat_ofNat_of_lt' (by
                      have hWordSize :
                          UInt64.size = 18446744073709551616 := rfl
                      omega : 8 * input.size < UInt64.size)]
                  simpa [FormalSpec.heapReserveBytes, hSize, hFind,
                    Nat.add_assoc] using hHeapFitMemory
                · exact hPages
                · rfl
                · exact hHeapTop
                · exact hFreeList
                · exact hAllocs
                · rw [successfulRemovalLengthTail_eq]
                  apply FixedArrayResult.lengthStoreLocal_spec
                    (root := heapTop + 48)
                    (length := UInt64.ofNat input.size - 1)
                  · apply FixedArrayAllocatorWindow.allocFrame_get_root
                      (offset := 9) (tail := 0)
                    · simp (config := { maxSteps := 10000000 })
                        (discharger := omega)
                        [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                          EncodedIndexDecoder.resultFrame,
                          FixedArrayFindIdxEq.someFrame_params,
                          FixedArrayFindIdxEq.someFrame_locals_length,
                          List.length_set, hEncodedNe]
                    · simp (config := { maxSteps := 10000000 })
                        (discharger := omega)
                        [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                          EncodedIndexDecoder.resultFrame,
                          FixedArrayFindIdxEq.someFrame_params,
                          FixedArrayFindIdxEq.someFrame_locals_length,
                          List.length_set, hEncodedNe]
                  · simp (config := { maxSteps := 10000000 })
                      (discharger := omega)
                      [FixedArrayAllocatorWindow.allocFrame,
                        FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                        Wasm.Locals.get, List.length_set,
                        List.getElem?_set]
                  · have hAllocationFit :
                        heapTop.toNat + 48 +
                            (FixedArrayCapacity.normalizedCapacity
                              (UInt64.ofNat input.size - 1) 1).toNat ≤
                          initial.mem.pages * 65536 := by
                      rw [hCapacityEq,
                        UInt64.toNat_ofNat_of_lt' (by
                          have hWordSize :
                              UInt64.size = 18446744073709551616 := rfl
                          omega : 8 * input.size < UInt64.size)]
                      simpa [FormalSpec.heapReserveBytes, hSize, hFind,
                        Nat.add_assoc] using hHeapFitMemory
                    have hFacts := Allocation.bumpFacts heapTop
                      (FixedArrayCapacity.normalizedCapacity
                        (UInt64.ofNat input.size - 1) 1)
                      initial.mem.pages hAllocationFit hPages
                    have hCapacityNat :
                        (FixedArrayCapacity.normalizedCapacity
                          (UInt64.ofNat input.size - 1) 1).toNat =
                            8 * input.size := by
                      rw [hCapacityEq,
                        UInt64.toNat_ofNat_of_lt' (by
                          have hWordSize :
                              UInt64.size = 18446744073709551616 := rfl
                          omega : 8 * input.size < UInt64.size)]
                    rw [Project.ProofKit.Memory.toUInt32_toNat,
                      hFacts.rootToNat,
                      Nat.mod_eq_of_lt (by omega),
                      FixedArrayAllocator.allocStore_pages]
                    omega
                  · have hAllocationFit :
                        heapTop.toNat + 48 +
                            (FixedArrayCapacity.normalizedCapacity
                              (UInt64.ofNat input.size - 1) 1).toNat ≤
                          initial.mem.pages * 65536 := by
                      rw [hCapacityEq,
                        UInt64.toNat_ofNat_of_lt' (by
                          have hWordSize :
                              UInt64.size = 18446744073709551616 := rfl
                          omega : 8 * input.size < UInt64.size)]
                      simpa [FormalSpec.heapReserveBytes, hSize, hFind,
                        Nat.add_assoc] using hHeapFitMemory
                    have hFacts := Allocation.bumpFacts heapTop
                      (FixedArrayCapacity.normalizedCapacity
                        (UInt64.ofNat input.size - 1) 1)
                      initial.mem.pages hAllocationFit hPages
                    have hCapacityNat :
                        (FixedArrayCapacity.normalizedCapacity
                          (UInt64.ofNat input.size - 1) 1).toNat =
                            8 * input.size := by
                      rw [hCapacityEq,
                        UInt64.toNat_ofNat_of_lt' (by
                          have hWordSize :
                              UInt64.size = 18446744073709551616 := rfl
                          omega : 8 * input.size < UInt64.size)]
                    have hInputAllocated :=
                      FixedArrayPairResult.input_preserved_by_alloc
                        initial heapTop
                        (FixedArrayCapacity.normalizedCapacity
                          (UInt64.ofNat input.size - 1) 1)
                        1 allocs inputPtr input hArray hInputBelow
                        hAllocationFit hPages
                    have hResultLengthEq :
                        UInt64.ofNat input.size - 1 =
                          UInt64.ofNat (input.size - 1) := by
                      interval_cases hInputSize : input.size
                      all_goals first | omega | native_decide
                    have hSuffixEq :
                        UInt64.ofNat input.size - 1 - UInt64.ofNat index =
                          UInt64.ofNat (input.size - 1 - index) := by
                      interval_cases hInputSize : input.size
                      all_goals interval_cases hEraseIndex : index
                      all_goals first | omega | native_decide
                    rw [AnnotationMatches.function_0_erase_copy_0_tail_eq]
                    apply FixedArrayCopy.eraseIdxProgram_spec
                      (sourcePtr := inputPtr) (targetPtr := heapTop + 48)
                      (input := input) (erase := index)
                    · exact hIndex
                    · unfold FixedArrayResult.writeLength
                      apply hInputAllocated.write64After
                      rw [Project.ProofKit.Memory.toUInt32_toNat,
                        hFacts.rootToNat,
                        Nat.mod_eq_of_lt (by omega)]
                      omega
                    · norm_num
                    · norm_num
                    · norm_num
                    · norm_num
                    · exact removalFrame_values _ _ _ _ _
                    · apply removalFrame_source
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            Wasm.Locals.get, List.length_set,
                            List.getElem?_set, List.getElem?_cons_zero,
                            List.getElem?_cons_succ, hEncodedNe,
                            FixedArrayFindIdxEq.encodedIndex_sub_one]
                    · apply FixedArrayAllocatorWindow.allocFrame_get_root
                        (offset := 9) (tail := 0)
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                            EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [FixedArrayCapacity.capacityFrame, eraseSetupFrame,
                            EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                    · apply removalFrame_prefix
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                    · rw [← hSuffixEq]
                      apply removalFrame_suffix
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                      · simp (config := { maxSteps := 10000000 })
                          (discharger := omega)
                          [EncodedIndexDecoder.resultFrame,
                            FixedArrayFindIdxEq.someFrame_params,
                            FixedArrayFindIdxEq.someFrame_locals_length,
                            List.length_set, hEncodedNe]
                    · rw [hFacts.rootToNat]
                      have hFit := hFacts.fit32
                      rw [hCapacityNat] at hFit
                      omega
                    · rw [FixedArrayResult.writeLength_pages,
                        FixedArrayAllocator.allocStore_pages,
                        hFacts.rootToNat]
                      have hFit := hAllocationFit
                      rw [hCapacityNat] at hFit
                      omega
                    · unfold FixedArrayResult.writeLength
                      rw [Mem.read64_write64_same]
                      exact hResultLengthEq
                    · rw [hFacts.rootToNat]
                      omega
                    · intro final hResult
                      change wp module (successfulRemovalBody.drop 59) _ final
                        (successfulCopyFrame inputPtr input index
                          (FixedArrayCapacity.normalizedCapacity
                            (UInt64.ofNat input.size - 1) 1)
                          heapTop) env
                      rw [successfulRemovalFinishTail_eq]
                      simp only [wp_localGet_cons]
                      rw [successfulCopyFrame_root]
                      simp only
                      rw [wp_nil]
                      change wp module [] _ final _ env
                      rw [wp_nil]
                      simp (config := { maxSteps := 10000000 })
                        (discharger := omega)
                        [FixedArrayEqNode.branchPost,
                          successfulCopyFrame_values,
                          successfulCopyFrame_params_length,
                          successfulCopyFrame_locals_length,
                          Wasm.Locals.get, Wasm.Locals.set?,
                          List.length_set, List.getElem?_set, hResult]
                      exact hResult
          · simp
          · simp
          · norm_num
          · norm_num
          · norm_num
        · simp
        · simp (discharger := omega) [Wasm.Locals.validIndex,
            FixedArrayFindIdxEq.someFrame_locals_length]
  · intro hInvalid
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hInvalid]
    have hCapacityEq :
        FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by
      native_decide
    have hAllocationFit :
        heapTop.toNat + 48 +
            (FixedArrayCapacity.normalizedCapacity 0 1).toNat ≤
          initial.mem.pages * 65536 := by
      rw [hCapacityEq]
      simpa [FormalSpec.heapReserveBytes, hInvalid] using hHeapFitMemory
    have hFacts := Allocation.bumpFacts heapTop
      (FixedArrayCapacity.normalizedCapacity 0 1)
      initial.mem.pages hAllocationFit hPages
    change wp module (oversizedBody.drop 0) _ initial
      (oversizedBaseFrame inputPtr) env
    rw [oversizedCapacityAllocatorTail_eq]
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 3) (tail := 6)
      (heapTop := heapTop) (allocs := allocs)
    · exact oversizedBaseFrame_params_length inputPtr
    · exact oversizedBaseFrame_locals_length inputPtr
    · rfl
    · exact hAllocationFit
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · change wp module (oversizedBody.drop 35) _
        (FixedArrayAllocator.allocStore initial heapTop
          (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs)
        (oversizedAllocatedFrame inputPtr heapTop) env
      rw [oversizedLengthTail_eq]
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 8)
      · exact oversizedAllocatedFrame_values inputPtr heapTop
      · exact oversizedAllocatedFrame_root inputPtr heapTop
      · rw [Project.ProofKit.Memory.toUInt32_toNat,
          hFacts.rootToNat, Nat.mod_eq_of_lt (by omega),
          FixedArrayAllocator.allocStore_pages]
        have hMinimum :=
          FixedArrayCapacity.normalizedCapacity_toNat_ge_eight 0 1
        omega
      · have hEmpty : UInt64Array.At
            (FixedArrayResult.writeLength
              (FixedArrayAllocator.allocStore initial heapTop
                (FixedArrayCapacity.normalizedCapacity 0 1) 1 allocs)
              (heapTop + 48) 0)
            (heapTop + 48) #[] := by
          apply FixedArrayResult.emptyStore_at
          · rw [hFacts.rootToNat]
            simpa [hExpected] using hOutputFit32
          · rw [hFacts.rootToNat,
              FixedArrayAllocator.allocStore_pages]
            simpa [hExpected] using hOutputFitMemory
        rw [oversizedFinishTail_eq]
        apply FixedArrayResult.finishProgram_spec
          (root := heapTop + 48)
          (rootLocal := 8) (destinationLocal := 6) (returnLocal := 7)
        · exact oversizedAllocatedFrame_values inputPtr heapTop
        · exact oversizedAllocatedFrame_root inputPtr heapTop
        · rw [oversizedAllocatedFrame_params_length]
          norm_num
        · simp [Wasm.Locals.validIndex,
            oversizedAllocatedFrame_params_length,
            oversizedAllocatedFrame_locals_length]
        · rw [oversizedAllocatedFrame_params_length]
          norm_num
        · simp [Wasm.Locals.validIndex,
            oversizedAllocatedFrame_params_length,
            oversizedAllocatedFrame_locals_length]
        · rw [wp_nil]
          simp only [FixedArrayEqNode.branchPost]
          simp only [wp_localGet_cons]
          rw [Frame.withValues_get]
          rw [FixedArrayResult.finishFrame_return_get]
          · simp only
            rw [wp_nil]
            refine ⟨heapTop + 48, ?_, ?_⟩
            · simp [func0Def, Function.numParams]
            · rw [hExpected]
              exact hEmpty
          · rw [oversizedAllocatedFrame_params_length]
            norm_num
          · simp [Wasm.Locals.validIndex,
              oversizedAllocatedFrame_params_length,
              oversizedAllocatedFrame_locals_length]

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior
