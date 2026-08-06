import LeanExeGen.GeneratedRd1e76d3580ead0d9.FormalSpec
import LeanExeGen.GeneratedRd1e76d3580ead0d9.Program
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRd1e76d3580ead0d9.Behavior

open Wasm
open Project.ProofKit

macro "wp_run24" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

macro "wp_set24" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) only [
      List.cons_append, List.nil_append, wp_constI64_cons, wp_localSet_cons,
      Wasm.Locals.set?, Wasm.Locals.validIndex, List.length_set,
      List.getElem?_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff,
      Nat.reduceSub, $ts,*])

def capacityPrefix : Wasm.Program :=
  [
  .constI64 8,
  .constI64 2,
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
  .localSet 19,
  .localGet 19,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 19
  ] []
  ]

def capacityFrame (frame : Locals) : Locals :=
  { frame with locals := frame.locals.set 18 (.i64 24) }

theorem capacityPrefix_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (capacityFrame frame) env) :
    wp module_ (capacityPrefix ++ rest) Q st frame env := by
  simp (config := { maxSteps := 10000000 }) [capacityPrefix, capacityFrame,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
    List.length_set, List.getElem?_set, hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simpa [capacityFrame, hValues] using hNext

def pairConstSuffix (first second : UInt64) (destination : Nat) : Wasm.Program :=
  FixedArrayResult.lengthStoreProgram 15 2 ++
    ([.constI64 first, .localSet 18] ++
      (FixedArrayResult.payloadStoreProgram 15 18 0 ++
        ([.constI64 second, .localSet 18] ++
          (FixedArrayResult.payloadStoreProgram 15 18 1 ++
            FixedArrayResult.finishProgram 15 destination 14))))

def constResultProgram (first second : UInt64) (destination : Nat) : Wasm.Program :=
  capacityPrefix ++ (FixedArrayAllocatorWindow.region 10 1 ++
    pairConstSuffix first second destination)

def inputValueProgram (index : Nat) : Wasm.Program :=
  [
  .localGet 0,
  .localSet 19,
  .constI64 (UInt64.ofNat index),
  .localSet 20,
  .localGet 20,
  .localGet 19,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 19,
    .localGet 20,
    .constI64 1,
    .mulI64,
    .constI64 1,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 18
  ]

def pairInputSuffix (index destination : Nat) : Wasm.Program :=
  FixedArrayResult.lengthStoreProgram 15 2 ++
    (inputValueProgram index ++
      (FixedArrayResult.payloadStoreProgram 15 18 0 ++
        ([.constI64 1, .localSet 18] ++
          (FixedArrayResult.payloadStoreProgram 15 18 1 ++
            FixedArrayResult.finishProgram 15 destination 14))))

def inputResultProgram (index destination : Nat) : Wasm.Program :=
  capacityPrefix ++ (FixedArrayAllocatorWindow.region 10 1 ++
    pairInputSuffix index destination)

def scratchFrame (frame : Locals) (value : UInt64) : Locals :=
  { frame with locals := frame.locals.set 17 (.i64 value), values := [] }

theorem scratchSet_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (value : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (scratchFrame frame value) env) :
    wp module_ ([.constI64 value, .localSet 18] ++ rest) Q st frame env := by
  wp_set24 [hParams, hLocals, hValues]
  simpa [scratchFrame] using hNext

theorem scratchFrame_params (frame : Locals) (value : UInt64) :
    (scratchFrame frame value).params = frame.params := rfl

theorem scratchFrame_locals_length (frame : Locals) (value : UInt64) :
    (scratchFrame frame value).locals.length = frame.locals.length := by
  simp [scratchFrame]

theorem scratchFrame_values (frame : Locals) (value : UInt64) :
    (scratchFrame frame value).values = [] := rfl

theorem scratchFrame_get15 (frame : Locals) (root value : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hRoot : frame.get 15 = some (.i64 root)) :
    (scratchFrame frame value).get 15 = some (.i64 root) := by
  simpa [scratchFrame, Wasm.Locals.get, hParams, hLocals] using hRoot

theorem scratchFrame_get18 (frame : Locals) (value : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24) :
    (scratchFrame frame value).get 18 = some (.i64 value) := by
  simp [scratchFrame, Wasm.Locals.get, hParams, hLocals]

def inputValueFrame (frame : Locals) (inputPtr : UInt64) (index : Nat)
    (value : UInt64) : Locals :=
  { frame with locals :=
      ((frame.locals.set 18 (.i64 inputPtr)).set 19
        (.i64 (UInt64.ofNat index))).set 17 (.i64 value), values := [] }

theorem inputValueFrame_params (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) :
    (inputValueFrame frame inputPtr index value).params = frame.params := rfl

theorem inputValueFrame_locals_length (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) :
    (inputValueFrame frame inputPtr index value).locals.length =
      frame.locals.length := by
  simp [inputValueFrame]

theorem inputValueFrame_values (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) :
    (inputValueFrame frame inputPtr index value).values = [] := rfl

theorem inputValueFrame_get15 (frame : Locals) (inputPtr root value : UInt64)
    (index : Nat)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hRoot : frame.get 15 = some (.i64 root)) :
    (inputValueFrame frame inputPtr index value).get 15 =
      some (.i64 root) := by
  simpa [inputValueFrame, Wasm.Locals.get, hParams, hLocals] using hRoot

theorem inputValueFrame_get18 (frame : Locals) (inputPtr value : UInt64)
    (index : Nat)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24) :
    (inputValueFrame frame inputPtr index value).get 18 =
      some (.i64 value) := by
  simp [inputValueFrame, Wasm.Locals.get, hParams, hLocals]

theorem inputValueProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (hParamsValue : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (inputValueFrame frame inputPtr index input[index]) env) :
    wp module_ (inputValueProgram index ++ rest) Q st frame env := by
  have hParams : frame.params.length = 1 := by simp [hParamsValue]
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.lengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hValueRead := hInput.elementRead index hIndex
  have hValueBound := hInput.elementBound index hIndex
  have hValueAddress := hInput.elementAddress_eq index hIndex
  have hValueAddress' :
      UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296) =
        (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
    simpa [Nat.mul_comm] using hValueAddress
  have hValueRead' :
      st.mem.read64
        (UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
          input[index] := by
    rw [hValueAddress']
    exact hValueRead
  have hIndex64 : index < UInt64.size := by
    have hSize := hInput.size_lt
    omega
  have hIndexToNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' hIndex64
  have hGeneratedAddress :
      inputPtr.toUInt32 + 8 * (UInt32.ofNat index + 1) =
        (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
    rw [← hValueAddress]
    apply UInt32.toNat.inj
    simp [hInput.pointerAddress_toNat, hIndexToNat]
  have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
    rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
    exact hIndex
  have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
  have hValueBound' :
      (inputPtr.toNat + 8 * (index + 1)) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
    have hBound :
        (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
          4294967296)).toNat + 8 ≤ st.mem.pages * 65536 := by
      rw [hValueAddress]
      exact hValueBound
    simpa using hBound
  unfold inputValueProgram
  wp_run24 [hParamsValue, hParams, hLocals, hValues, hLengthRead,
    hLengthBound, hInputAddress, hIndexToNat, hIndexEncoded]
  rw [if_neg (Nat.not_lt.mpr hLengthBound')]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hIndexEncoded])]
  wp_run24 [hParamsValue, hParams, hLocals, hValues, hValueRead,
    hValueRead', hValueBound, hValueAddress, hValueAddress', hIndexToNat,
    hIndex]
  rw [if_neg (Nat.not_lt.mpr hValueBound')]
  rw [hGeneratedAddress, hValueRead]
  simpa [inputValueFrame, hParamsValue] using hNext

def pairPost (first second : UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values = [] ∧
        frame.params.length = 1 ∧
        frame.locals.length = 24 ∧
        frame.locals[13]? = some (.i64 outputPtr) ∧
        UInt64Array.At final outputPtr #[first, second]
    | _ => False

def publicPost (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values.take 1 = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | .Return final values => ∃ outputPtr,
        values.take 1 = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | _ => False

def fallthroughPost (module_ : Wasm.Module) (env : HostEnv Unit)
    (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | _ => False

def resultContinuation (module_ : Wasm.Module) (env : HostEnv Unit)
    (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | .Break 0 final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | .Break (index + 1) final frame =>
        publicPost input (.Break index final frame)
    | other => publicPost input other

theorem pairPost_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (input : Array UInt64)
    (first second : UInt64)
    (hExpected : FormalSpec.expected input = #[first, second]) :
    pairPost first second ⇛ resultContinuation module_ env input := by
  intro continuation hPair
  cases continuation <;> simp only [pairPost] at hPair
  rename_i final frame
  rcases hPair with
    ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
      hOutputLocal, hOutput⟩
  have hOutputGet : frame.locals[13] = .i64 outputPtr := by
    have h := hOutputLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [resultContinuation]
  wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
  simp only [publicPost]
  refine ⟨outputPtr, rfl, ?_⟩
  change UInt64Array.At final outputPtr (FormalSpec.expected input)
  rw [hExpected]
  exact hOutput

theorem fallthroughPost_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (input : Array UInt64) :
    fallthroughPost module_ env input ⇛
      resultContinuation module_ env input := by
  intro continuation hFallthrough
  cases continuation <;> simp only [fallthroughPost] at hFallthrough
  simpa only [resultContinuation] using hFallthrough

theorem finishPair_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (root first second : UInt64) (destination : Nat)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hRoot : frame.get 15 = some (.i64 root))
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hArray : UInt64Array.At st root #[first, second]) :
    wp module_ (FixedArrayResult.finishProgram 15 destination 14)
      (pairPost first second) st frame env := by
  have hRootOption : frame.locals[14]? = some (.i64 root) := by
    simpa [Wasm.Locals.get, hParams, hLocals] using hRoot
  have hRootLocal : frame.locals[14] = .i64 root := by
    rw [List.getElem?_eq_getElem (by omega)] at hRootOption
    exact Option.some.inj hRootOption
  have hDestinationLocal : destination - 1 < 24 := by omega
  unfold FixedArrayResult.finishProgram
  wp_run24 [hParams, hLocals, hValues, hRootLocal,
    hDestinationPositive.ne', hDestination, hDestinationLocal]
  simpa [pairPost, hParams, hLocals] using hArray

theorem input_preserved_by_alloc
    (st : Store Unit) (heapTop capacity stride allocs inputPtr : UInt64)
    (input : Array UInt64)
    (hInput : UInt64Array.At st inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) :
    UInt64Array.At
      (FixedArrayAllocator.allocStore st heapTop capacity stride allocs)
      inputPtr input := by
  have hFacts := Allocation.bumpFacts heapTop capacity st.mem.pages
    hFitMemory hPages
  apply hInput.frameBefore hInputBelow
  · exact FixedArrayAllocator.allocStore_pages st heapTop capacity stride allocs
  · intro address hAddress
    simp only [FixedArrayAllocator.allocStore, FixedArrayAllocator.headerMem]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]
    rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
      simp [Nat.mod_eq_of_lt (by omega)]
      omega)]

set_option Elab.async false in
theorem constResultProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop allocs first second : UInt64)
    (destination : Nat)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (constResultProgram first second destination)
      (pairPost first second) st frame env := by
  unfold constResultProgram
  apply capacityPrefix_spec module_ env st frame hParams hLocals hValues
  apply FixedArrayAllocatorWindow.region_spec 10 module_ env st (capacityFrame frame)
    heapTop 24 1 allocs
  · simpa [capacityFrame] using hParams
  · simpa [capacityFrame] using hLocals
  · simpa [capacityFrame] using hValues
  · simp [capacityFrame, hLocals]
  · decide
  · simpa using hFitMemory
  · exact hPages
  · exact hMemory32
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · have hFacts := Allocation.bumpFacts heapTop 24 st.mem.pages
      (by simpa using hFitMemory) hPages
    have hRootAddressNat := hFacts.wordAddress_toNat 0 (by decide)
    have hFirstAddressNat := hFacts.wordAddress_toNat 1 (by decide)
    have hSecondAddressNat := hFacts.wordAddress_toNat 2 (by decide)
    have hRootToNat32 : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hRootAddressNat
    have hFirstToNat32 :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
          heapTop.toNat + 48 + 8 := by
      simpa [FixedArrayResult.payloadAddress] using hFirstAddressNat
    have hSecondToNat32 :
        (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat =
          heapTop.toNat + 48 + 16 := by
      simpa [FixedArrayResult.payloadAddress] using hSecondAddressNat
    let allocSt := FixedArrayAllocator.allocStore st heapTop 24 1 allocs
    let allocFrame := FixedArrayAllocatorWindow.allocFrame 10 (capacityFrame frame)
      heapTop 24
    have hAllocValues : allocFrame.values = [] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame, hValues]
    have hAllocParams : allocFrame.params.length = 1 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParams]
    have hAllocLocals : allocFrame.locals.length = 24 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hLocals]
    have hRoot : allocFrame.get 15 = some (.i64 (heapTop + 48)) := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame, hParams,
        hLocals, Wasm.Locals.get]
    have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
        allocSt.mem.pages * 65536 := by
      rw [hRootToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hFirstBound : (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
        (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages * 65536 := by
      rw [hFirstToNat32, FixedArrayResult.writeLength_pages]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hSecondBound : (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat + 8 ≤
        (FixedArrayResult.writePayload
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 2)
          (heapTop + 48) 0 first).mem.pages * 65536 := by
      rw [FixedArrayResult.writePayload_pages, FixedArrayResult.writeLength_pages,
        hSecondToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hPair := FixedArrayResult.pairStore_at allocSt (heapTop + 48)
      first second (by rw [hFacts.rootToNat]; omega) (by
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        rw [hFacts.rootToNat]
        omega)
    unfold pairConstSuffix
    refine FixedArrayResult.lengthStore_spec module_ env allocSt allocFrame
      (heapTop + 48) 2 15 hAllocValues hRoot hRootBound
      (pairPost first second) _ ?_
    refine scratchSet_spec module_ env _ allocFrame first hAllocParams
      hAllocLocals hAllocValues (pairPost first second) _ ?_
    refine FixedArrayResult.payloadStore_spec module_ env _ _ (heapTop + 48)
      first 15 18 0 ?_ ?_ hFirstBound (pairPost first second) _ ?_
    · exact scratchFrame_get15 allocFrame (heapTop + 48) first
        hAllocParams hAllocLocals hRoot
    · exact scratchFrame_get18 allocFrame first hAllocParams hAllocLocals
    refine scratchSet_spec module_ env _ _ second (by
      simpa [scratchFrame_params] using hAllocParams) (by
      simpa [scratchFrame_locals_length] using hAllocLocals) (by
      exact scratchFrame_values allocFrame first) (pairPost first second) _ ?_
    refine FixedArrayResult.payloadStore_spec module_ env _ _ (heapTop + 48)
      second 15 18 1 ?_ ?_ hSecondBound (pairPost first second) _ ?_
    · exact scratchFrame_get15 (scratchFrame allocFrame first)
        (heapTop + 48) second (by simpa [scratchFrame_params] using hAllocParams)
        (by simpa [scratchFrame_locals_length] using hAllocLocals)
        (scratchFrame_get15 allocFrame (heapTop + 48) first
          hAllocParams hAllocLocals hRoot)
    · exact scratchFrame_get18 (scratchFrame allocFrame first) second
        (by simpa [scratchFrame_params] using hAllocParams)
        (by simpa [scratchFrame_locals_length] using hAllocLocals)
    apply finishPair_spec module_ env _ _ (heapTop + 48) first second
      destination
    · simpa [scratchFrame_params] using hAllocParams
    · simpa [scratchFrame_locals_length] using hAllocLocals
    · exact scratchFrame_values (scratchFrame allocFrame first) second
    · exact scratchFrame_get15 (scratchFrame allocFrame first)
        (heapTop + 48) second
        (by simpa [scratchFrame_params] using hAllocParams)
        (by simpa [scratchFrame_locals_length] using hAllocLocals)
        (scratchFrame_get15 allocFrame (heapTop + 48) first
          hAllocParams hAllocLocals hRoot)
    · exact hDestinationPositive
    · exact hDestination
    · exact hPair

set_option Elab.async false in
theorem inputResultProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop allocs inputPtr : UInt64)
    (input : Array UInt64) (index destination : Nat)
    (hParamsValue : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (inputResultProgram index destination)
      (pairPost input[index] 1) st frame env := by
  have hParams : frame.params.length = 1 := by simp [hParamsValue]
  unfold inputResultProgram
  apply capacityPrefix_spec module_ env st frame hParams hLocals hValues
  apply FixedArrayAllocatorWindow.region_spec 10 module_ env st (capacityFrame frame)
    heapTop 24 1 allocs
  · simpa [capacityFrame] using hParams
  · simpa [capacityFrame] using hLocals
  · simpa [capacityFrame] using hValues
  · simp [capacityFrame, hLocals]
  · decide
  · simpa using hFitMemory
  · exact hPages
  · exact hMemory32
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · have hFacts := Allocation.bumpFacts heapTop 24 st.mem.pages
      (by simpa using hFitMemory) hPages
    have hRootAddressNat := hFacts.wordAddress_toNat 0 (by decide)
    have hFirstAddressNat := hFacts.wordAddress_toNat 1 (by decide)
    have hSecondAddressNat := hFacts.wordAddress_toNat 2 (by decide)
    have hRootToNat32 : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hRootAddressNat
    have hFirstToNat32 :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
          heapTop.toNat + 48 + 8 := by
      simpa [FixedArrayResult.payloadAddress] using hFirstAddressNat
    have hSecondToNat32 :
        (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat =
          heapTop.toNat + 48 + 16 := by
      simpa [FixedArrayResult.payloadAddress] using hSecondAddressNat
    let allocSt := FixedArrayAllocator.allocStore st heapTop 24 1 allocs
    let allocFrame := FixedArrayAllocatorWindow.allocFrame 10 (capacityFrame frame)
      heapTop 24
    have hAllocValues : allocFrame.values = [] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame, hValues]
    have hAllocParams : allocFrame.params.length = 1 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParams]
    have hAllocLocals : allocFrame.locals.length = 24 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hLocals]
    have hAllocParamsValue : allocFrame.params = [.i64 inputPtr] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParamsValue]
    have hRoot : allocFrame.get 15 = some (.i64 (heapTop + 48)) := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame, hParams,
        hLocals, Wasm.Locals.get]
    have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
        allocSt.mem.pages * 65536 := by
      rw [hRootToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
      exact input_preserved_by_alloc st heapTop 24 1 allocs inputPtr input
        hInput hInputBelow (by simpa using hFitMemory) hPages
    have hInputAfterLength : UInt64Array.At
        (FixedArrayResult.writeLength allocSt (heapTop + 48) 2) inputPtr input := by
      exact hInputAlloc.write64After (address := (heapTop + 48).toUInt32)
        (value := 2) (by rw [hRootToNat32]; omega)
    have hLengthRead := hInputAfterLength.lengthRead
    have hLengthBound := hInputAfterLength.lengthBound
    have hInputAddress := hInputAfterLength.pointerAddress_eq
    have hValueRead := hInputAfterLength.elementRead index hIndex
    have hValueBound := hInputAfterLength.elementBound index hIndex
    have hValueAddress := hInputAfterLength.elementAddress_eq index hIndex
    have hIndex64 : index < UInt64.size := by
      have hSize := hInputAfterLength.size_lt
      omega
    have hIndexToNat : (UInt64.ofNat index).toNat = index :=
      UInt64.toNat_ofNat_of_lt' hIndex64
    have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
      UInt64.toNat_ofNat_of_lt' hInputAfterLength.size_lt
    have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
      exact hIndex
    have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
        (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages * 65536 := by
      simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
    have hValueBound' :
        (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 ≤
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages *
            65536 := by
      have hBound :
          (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
            4294967296)).toNat + 8 ≤
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages *
              65536 := by
        rw [hValueAddress]
        exact hValueBound
      simpa [Nat.mul_comm] using hBound
    have hFirstBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages *
            65536 := by
      rw [show (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
        heapTop.toNat + 48 + 8 by exact hFirstToNat32]
      simp only [FixedArrayResult.writeLength_pages, allocSt,
        FixedArrayAllocator.allocStore_pages]
      omega
    have hSecondBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writePayload
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 2)
            (heapTop + 48) 0 input[index]).mem.pages * 65536 := by
      rw [FixedArrayResult.writePayload_pages, FixedArrayResult.writeLength_pages,
        hSecondToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hPair := FixedArrayResult.pairStore_at allocSt (heapTop + 48)
      input[index] 1 (by rw [hFacts.rootToNat]; omega) (by
        simp only [allocSt, FixedArrayAllocator.allocStore_pages]
        rw [hFacts.rootToNat]
        omega)
    unfold pairInputSuffix
    refine FixedArrayResult.lengthStore_spec module_ env allocSt allocFrame
      (heapTop + 48) 2 15 hAllocValues hRoot hRootBound
      (pairPost input[index] 1) _ ?_
    refine inputValueProgram_spec module_ env _ allocFrame inputPtr input index
      hAllocParamsValue hAllocLocals hAllocValues hInputAfterLength hIndex
      (pairPost input[index] 1) _ ?_
    refine FixedArrayResult.payloadStore_spec module_ env _ _ (heapTop + 48)
      input[index] 15 18 0 ?_ ?_ hFirstBound (pairPost input[index] 1) _ ?_
    · exact inputValueFrame_get15 allocFrame inputPtr (heapTop + 48)
        input[index] index hAllocParams hAllocLocals hRoot
    · exact inputValueFrame_get18 allocFrame inputPtr input[index] index
        hAllocParams hAllocLocals
    refine scratchSet_spec module_ env _ _ 1 (by
      simpa [inputValueFrame_params] using hAllocParams) (by
      simpa [inputValueFrame_locals_length] using hAllocLocals) (by
      exact inputValueFrame_values allocFrame inputPtr index input[index])
      (pairPost input[index] 1) _ ?_
    refine FixedArrayResult.payloadStore_spec module_ env _ _ (heapTop + 48)
      1 15 18 1 ?_ ?_ hSecondBound (pairPost input[index] 1) _ ?_
    · exact scratchFrame_get15
        (inputValueFrame allocFrame inputPtr index input[index])
        (heapTop + 48) 1
        (by simpa [inputValueFrame_params] using hAllocParams)
        (by simpa [inputValueFrame_locals_length] using hAllocLocals)
        (inputValueFrame_get15 allocFrame inputPtr (heapTop + 48)
          input[index] index hAllocParams hAllocLocals hRoot)
    · exact scratchFrame_get18
        (inputValueFrame allocFrame inputPtr index input[index]) 1
        (by simpa [inputValueFrame_params] using hAllocParams)
        (by simpa [inputValueFrame_locals_length] using hAllocLocals)
    apply finishPair_spec module_ env _ _ (heapTop + 48) input[index] 1
      destination
    · simpa [scratchFrame_params, inputValueFrame_params] using hAllocParams
    · simpa [scratchFrame_locals_length, inputValueFrame_locals_length]
        using hAllocLocals
    · exact scratchFrame_values
        (inputValueFrame allocFrame inputPtr index input[index]) 1
    · exact scratchFrame_get15
        (inputValueFrame allocFrame inputPtr index input[index])
        (heapTop + 48) 1
        (by simpa [inputValueFrame_params] using hAllocParams)
        (by simpa [inputValueFrame_locals_length] using hAllocLocals)
        (inputValueFrame_get15 allocFrame inputPtr (heapTop + 48)
          input[index] index hAllocParams hAllocLocals hRoot)
    · exact hDestinationPositive
    · exact hDestination
    · exact hPair

theorem constResultProgram_result_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop allocs first second : UInt64)
    (destination : Nat) (input : Array UInt64)
    (hExpected : FormalSpec.expected input = #[first, second])
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (constResultProgram first second destination)
      (resultContinuation module_ env input) st frame env := by
  apply Wasm.wp.conseq (Q := pairPost first second)
  · exact pairPost_conseq module_ env input first second hExpected
  · exact constResultProgram_spec module_ env st frame heapTop allocs first
      second destination hParams hLocals hValues hDestinationPositive
      hDestination hFitMemory hPages hMemory32 hHeapTop hFreeList hAllocs

theorem inputResultProgram_result_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop allocs inputPtr : UInt64)
    (input : Array UInt64) (index destination : Nat)
    (hIndex : index < input.size)
    (hExpected : FormalSpec.expected input = #[input[index], 1])
    (hParamsValue : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hInput : UInt64Array.At st inputPtr input)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (inputResultProgram index destination)
      (resultContinuation module_ env input) st frame env := by
  apply Wasm.wp.conseq (Q := pairPost input[index] 1)
  · exact pairPost_conseq module_ env input input[index] 1 hExpected
  · exact inputResultProgram_spec module_ env st frame heapTop allocs inputPtr
      input index destination hParamsValue hLocals hValues
      hDestinationPositive hDestination hInput hIndex hInputBelow hFitMemory
      hPages hMemory32 hHeapTop hFreeList hAllocs

theorem artifact_behavior :
    FormalSpec.ArtifactSpec
      LeanExeGen.GeneratedRd1e76d3580ead0d9.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32Expected, hFitMemoryExpected, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
      initial.mem.pages * 65536 := by
    simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
  have hEncoded15 : UInt64.ofNat input.size = 15 ↔ input.size = 15 := by
    simpa using hArray.encodedSize_eq (size := 15) (by
      norm_num [UInt64.size])
  have hExpectedSize : (FormalSpec.expected input).size = 2 := by
    unfold FormalSpec.expected
    aesop
  have hFitMemory : heapTop.toNat + 48 + 24 ≤
      initial.mem.pages * 65536 := by
    simpa [hExpectedSize] using hFitMemoryExpected
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  by_cases hSize : input.size = 15
  · have hElement (index : Nat) (hIndex : index < input.size) :
        (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 ≤
            initial.mem.pages * 65536 ∧
          initial.mem.read64
              (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
                4294967296)) = input[index] := by
      have hRead := hArray.elementRead index hIndex
      have hBound := hArray.elementBound index hIndex
      have hAddress := hArray.elementAddress_eq index hIndex
      constructor
      · have hBound' :
            (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
              4294967296)).toNat + 8 ≤ initial.mem.pages * 65536 := by
          rw [hAddress]
          exact hBound
        simpa [Nat.mul_comm] using hBound'
      · rw [hAddress]
        exact hRead
    have hIndex0 : 0 < input.size := by omega
    have hRead0 := hArray.elementRead 0 hIndex0
    have hBound0 := hArray.elementBound 0 hIndex0
    have hAddress0 := hArray.elementAddress_eq 0 hIndex0
    have hBound0' : (inputPtr.toNat + (0 + 1) * 8) % 4294967296 + 8 ≤
        initial.mem.pages * 65536 := by
      have hBound :
          (UInt32.ofNat ((inputPtr.toNat + 8 * (0 + 1)) %
            4294967296)).toNat + 8 ≤ initial.mem.pages * 65536 := by
        rw [hAddress0]
        exact hBound0
      simpa [Nat.mul_comm] using hBound
    have hGeneratedAddress0 :
        UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296) =
          inputPtr.toUInt32 + 8 := by
      apply UInt32.toNat.inj
      simp
    have hRead0' : initial.mem.read64 (inputPtr.toUInt32 + 8) = input[0] := by
      rw [← hGeneratedAddress0, hAddress0]
      exact hRead0
    apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
    unfold func0Def func0
    wp_run24 [hLengthRead, hLengthBound, hInputAddress, hEncoded15, hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run24 [hLengthRead, hLengthBound, hInputAddress, hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hSize])]
    wp_run24 [hLengthRead, hInputAddress, hRead0, hRead0', hBound0,
      hAddress0, hSize]
    refine ⟨hBound0', ?_⟩
    have hElement1 := hElement 1 (by omega)
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hLengthRead, hInputAddress, hSize])]
    wp_run24 [hLengthRead, hInputAddress, hElement1.2, hSize]
    refine ⟨hElement1.1, ?_⟩
    by_cases hKey1 : input[1] = input[0]
    · refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [hKey1])]
      wp_run24 []
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      have hExpected : FormalSpec.expected input = #[input[2], 1] := by
        simp [FormalSpec.expected, hSize, hKey1, eq_comm]
      change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
        (inputResultProgram 2 3) _ initial _ env
      apply Wasm.wp.conseq (Q := pairPost input[2] 1)
      · intro continuation hPair
        cases continuation <;> simp only [pairPost] at hPair
        rename_i final frame'
        rcases hPair with
          ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
            hOutputLocal, hOutput⟩
        have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
          have h := hOutputLocal
          rw [List.getElem?_eq_getElem (by omega)] at h
          exact Option.some.inj h
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
        change UInt64Array.At final outputPtr (FormalSpec.expected input)
        rw [hExpected]
        exact hOutput
      · exact inputResultProgram_spec _ env initial _ heapTop allocs inputPtr
          input 2 3 rfl rfl rfl (by decide) (by decide) hArray (by omega)
          hInputBelow hFitMemory hPages rfl hHeapTop hFreeList hAllocs
    · refine wp_iff_cons rfl ?_
      have hKey1' : ¬ input[0] = input[1] := fun h => hKey1 h.symm
      rw [if_neg (by simp [hKey1'])]
      wp_run24 []
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      apply Wasm.wp.conseq (Q := fallthroughPost
        LeanExeGen.GeneratedRd1e76d3580ead0d9.«module» env input)
      · intro continuation hFallthrough
        cases continuation <;> simp only [fallthroughPost] at hFallthrough
        rename_i final frame'
        simpa only [List.take_zero, List.drop_zero, List.nil_append,
          wp_simp, publicPost, Wasm.Locals.get, List.take,
          List.cons.injEq, and_true] using hFallthrough
      have hElement1' := hElement 1 (by omega)
      wp_run24 [hLengthRead, hInputAddress, hSize]
      rw [if_neg (Nat.not_lt.mpr hLengthBound')]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [hSize])]
      wp_run24 [hLengthRead, hInputAddress, hElement1'.2, hSize]
      rw [if_neg (Nat.not_lt.mpr hElement1'.1)]
      by_cases hRootLt : input[0] < input[1]
      · refine wp_iff_cons rfl ?_
        rw [if_pos (by simpa using hRootLt)]
        have hElement3 := hElement 3 (by omega)
        wp_run24 [hLengthRead, hInputAddress, hSize]
        rw [if_neg (Nat.not_lt.mpr hLengthBound')]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hSize])]
        wp_run24 [hLengthRead, hInputAddress, hElement3.2, hSize]
        rw [if_neg (Nat.not_lt.mpr hElement3.1)]
        by_cases hKey3 : input[3] = input[0]
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hKey3])]
          wp_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          have hExpected : FormalSpec.expected input = #[input[4], 1] := by
            simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt, hKey3]
          change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
            (inputResultProgram 4 4) _ initial _ env
          apply Wasm.wp.conseq (Q := pairPost input[4] 1)
          · intro continuation hPair
            cases continuation <;> simp only [pairPost] at hPair
            rename_i final frame'
            rcases hPair with
              ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                hOutputLocal, hOutput⟩
            have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
              have h := hOutputLocal
              rw [List.getElem?_eq_getElem (by omega)] at h
              exact Option.some.inj h
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [fallthroughPost]
            wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [publicPost]
            refine ⟨outputPtr, rfl, ?_⟩
            change UInt64Array.At final outputPtr (FormalSpec.expected input)
            rw [hExpected]
            exact hOutput
          · exact inputResultProgram_spec _ env initial _ heapTop allocs inputPtr
              input 4 4 rfl rfl rfl (by decide) (by decide) hArray (by omega)
              hInputBelow hFitMemory hPages rfl hHeapTop hFreeList hAllocs
        · refine wp_iff_cons rfl ?_
          have hKey3' : ¬ input[0] = input[3] := fun h => hKey3 h.symm
          rw [if_neg (by simp [hKey3, hKey3'])]
          wp_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          apply Wasm.wp.conseq (Q := fallthroughPost
            LeanExeGen.GeneratedRd1e76d3580ead0d9.«module» env input)
          · intro continuation hFallthrough
            cases continuation
            case Fallthrough final frame' =>
              simpa only [List.take_zero, List.drop_zero, List.nil_append,
                wp_simp, fallthroughPost] using hFallthrough
            all_goals simp only [fallthroughPost] at hFallthrough
          have hElement3' := hElement 3 (by omega)
          wp_run24 [hLengthRead, hInputAddress, hSize]
          rw [if_neg (Nat.not_lt.mpr hLengthBound')]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hSize])]
          wp_run24 [hLengthRead, hInputAddress, hElement3'.2, hSize]
          rw [if_neg (Nat.not_lt.mpr hElement3'.1)]
          by_cases hLeftLt : input[0] < input[3]
          · refine wp_iff_cons rfl ?_
            rw [if_pos (by simpa using hLeftLt)]
            have hElement7 := hElement 7 (by omega)
            wp_run24 [hLengthRead, hInputAddress, hSize]
            rw [if_neg (Nat.not_lt.mpr hLengthBound')]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hSize])]
            wp_run24 [hLengthRead, hInputAddress, hElement7.2, hSize]
            rw [if_neg (Nat.not_lt.mpr hElement7.1)]
            by_cases hKey7 : input[7] = input[0]
            · refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hKey7])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              have hExpected : FormalSpec.expected input = #[input[8], 1] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey3, hKey3', hLeftLt, hKey7]
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (inputResultProgram 8 5) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost input[8] 1)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact inputResultProgram_spec _ env initial _ heapTop allocs
                  inputPtr input 8 5 rfl rfl rfl (by decide) (by decide) hArray
                  (by omega) hInputBelow hFitMemory hPages rfl hHeapTop hFreeList
                  hAllocs
            · refine wp_iff_cons rfl ?_
              have hKey7' : ¬ input[0] = input[7] := fun h => hKey7 h.symm
              rw [if_neg (by simp [hKey7, hKey7'])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              have hExpected : FormalSpec.expected input = #[0, 0] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey3, hKey3', hLeftLt, hKey7, hKey7']
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (constResultProgram 0 0 6) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost 0 0)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact constResultProgram_spec _ env initial _ heapTop allocs 0 0
                  6 rfl rfl rfl (by decide) (by decide) hFitMemory hPages rfl
                  hHeapTop hFreeList hAllocs
          · refine wp_iff_cons rfl ?_
            rw [if_neg (by simpa using hLeftLt)]
            have hElement9 := hElement 9 (by omega)
            wp_run24 [hLengthRead, hInputAddress, hSize]
            rw [if_neg (Nat.not_lt.mpr hLengthBound')]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hSize])]
            wp_run24 [hLengthRead, hInputAddress, hElement9.2, hSize]
            rw [if_neg (Nat.not_lt.mpr hElement9.1)]
            by_cases hKey9 : input[9] = input[0]
            · refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hKey9])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              have hExpected : FormalSpec.expected input = #[input[10], 1] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey3, hKey3', hLeftLt, hKey9]
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (inputResultProgram 10 7) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost input[10] 1)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact inputResultProgram_spec _ env initial _ heapTop allocs
                  inputPtr input 10 7 rfl rfl rfl (by decide) (by decide) hArray
                  (by omega) hInputBelow hFitMemory hPages rfl hHeapTop hFreeList
                  hAllocs
            · refine wp_iff_cons rfl ?_
              have hKey9' : ¬ input[0] = input[9] := fun h => hKey9 h.symm
              rw [if_neg (by simp [hKey9, hKey9'])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              have hExpected : FormalSpec.expected input = #[0, 0] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey3, hKey3', hLeftLt, hKey9, hKey9']
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (constResultProgram 0 0 8) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost 0 0)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact constResultProgram_spec _ env initial _ heapTop allocs 0 0
                  8 rfl rfl rfl (by decide) (by decide) hFitMemory hPages rfl
                  hHeapTop hFreeList hAllocs
      · refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa using hRootLt)]
        have hElement5 := hElement 5 (by omega)
        wp_run24 [hLengthRead, hInputAddress, hSize]
        rw [if_neg (Nat.not_lt.mpr hLengthBound')]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hSize])]
        wp_run24 [hLengthRead, hInputAddress, hElement5.2, hSize]
        rw [if_neg (Nat.not_lt.mpr hElement5.1)]
        by_cases hKey5 : input[5] = input[0]
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hKey5])]
          wp_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          have hExpected : FormalSpec.expected input = #[input[6], 1] := by
            simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt, hKey5]
          change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
            (inputResultProgram 6 9) _ initial _ env
          apply Wasm.wp.conseq (Q := pairPost input[6] 1)
          · intro continuation hPair
            cases continuation <;> simp only [pairPost] at hPair
            rename_i final frame'
            rcases hPair with
              ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                hOutputLocal, hOutput⟩
            have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
              have h := hOutputLocal
              rw [List.getElem?_eq_getElem (by omega)] at h
              exact Option.some.inj h
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [fallthroughPost]
            wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [publicPost]
            refine ⟨outputPtr, rfl, ?_⟩
            change UInt64Array.At final outputPtr (FormalSpec.expected input)
            rw [hExpected]
            exact hOutput
          · exact inputResultProgram_spec _ env initial _ heapTop allocs inputPtr
              input 6 9 rfl rfl rfl (by decide) (by decide) hArray (by omega)
              hInputBelow hFitMemory hPages rfl hHeapTop hFreeList hAllocs
        · refine wp_iff_cons rfl ?_
          have hKey5' : ¬ input[0] = input[5] := fun h => hKey5 h.symm
          rw [if_neg (by simp [hKey5, hKey5'])]
          wp_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          apply Wasm.wp.conseq (Q := fallthroughPost
            LeanExeGen.GeneratedRd1e76d3580ead0d9.«module» env input)
          · intro continuation hFallthrough
            cases continuation
            case Fallthrough final frame' =>
              simpa only [List.take_zero, List.drop_zero, List.nil_append,
                wp_simp, fallthroughPost] using hFallthrough
            all_goals simp only [fallthroughPost] at hFallthrough
          have hElement5' := hElement 5 (by omega)
          wp_run24 [hLengthRead, hInputAddress, hSize]
          rw [if_neg (Nat.not_lt.mpr hLengthBound')]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hSize])]
          wp_run24 [hLengthRead, hInputAddress, hElement5'.2, hSize]
          rw [if_neg (Nat.not_lt.mpr hElement5'.1)]
          by_cases hRightLt : input[0] < input[5]
          · refine wp_iff_cons rfl ?_
            rw [if_pos (by simpa using hRightLt)]
            have hElement11 := hElement 11 (by omega)
            wp_run24 [hLengthRead, hInputAddress, hSize]
            rw [if_neg (Nat.not_lt.mpr hLengthBound')]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hSize])]
            wp_run24 [hLengthRead, hInputAddress, hElement11.2, hSize]
            rw [if_neg (Nat.not_lt.mpr hElement11.1)]
            by_cases hKey11 : input[11] = input[0]
            · refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hKey11])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              have hExpected : FormalSpec.expected input = #[input[12], 1] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey5, hKey5', hRightLt, hKey11]
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (inputResultProgram 12 10) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost input[12] 1)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact inputResultProgram_spec _ env initial _ heapTop allocs
                  inputPtr input 12 10 rfl rfl rfl (by decide) (by decide)
                  hArray (by omega) hInputBelow hFitMemory hPages rfl hHeapTop
                  hFreeList hAllocs
            · refine wp_iff_cons rfl ?_
              have hKey11' : ¬ input[0] = input[11] := fun h => hKey11 h.symm
              rw [if_neg (by simp [hKey11, hKey11'])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              have hExpected : FormalSpec.expected input = #[0, 0] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey5, hKey5', hRightLt, hKey11, hKey11']
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (constResultProgram 0 0 11) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost 0 0)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact constResultProgram_spec _ env initial _ heapTop allocs 0 0
                  11 rfl rfl rfl (by decide) (by decide) hFitMemory hPages rfl
                  hHeapTop hFreeList hAllocs
          · refine wp_iff_cons rfl ?_
            rw [if_neg (by simpa using hRightLt)]
            have hElement13 := hElement 13 (by omega)
            wp_run24 [hLengthRead, hInputAddress, hSize]
            rw [if_neg (Nat.not_lt.mpr hLengthBound')]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hSize])]
            wp_run24 [hLengthRead, hInputAddress, hElement13.2, hSize]
            rw [if_neg (Nat.not_lt.mpr hElement13.1)]
            by_cases hKey13 : input[13] = input[0]
            · refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hKey13])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              have hExpected : FormalSpec.expected input = #[input[14], 1] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey5, hKey5', hRightLt, hKey13]
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (inputResultProgram 14 12) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost input[14] 1)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact inputResultProgram_spec _ env initial _ heapTop allocs
                  inputPtr input 14 12 rfl rfl rfl (by decide) (by decide)
                  hArray (by omega) hInputBelow hFitMemory hPages rfl hHeapTop
                  hFreeList hAllocs
            · refine wp_iff_cons rfl ?_
              have hKey13' : ¬ input[0] = input[13] := fun h => hKey13 h.symm
              rw [if_neg (by simp [hKey13, hKey13'])]
              wp_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              have hExpected : FormalSpec.expected input = #[0, 0] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey1', hRootLt,
                  hKey5, hKey5', hRightLt, hKey13, hKey13']
              change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
                (constResultProgram 0 0 13) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost 0 0)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [fallthroughPost]
                wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change UInt64Array.At final outputPtr (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · exact constResultProgram_spec _ env initial _ heapTop allocs 0 0
                  13 rfl rfl rfl (by decide) (by decide) hFitMemory hPages rfl
                  hHeapTop hFreeList hAllocs
  · apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
    unfold func0Def func0
    wp_run24 [hLengthRead, hLengthBound, hInputAddress, hEncoded15, hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    have hExpected : FormalSpec.expected input = #[0, 0] := by
      simp [FormalSpec.expected, hSize]
    change wp LeanExeGen.GeneratedRd1e76d3580ead0d9.«module»
      (constResultProgram 0 0 1) _ initial _ env
    apply Wasm.wp.conseq (Q := pairPost 0 0)
    · intro continuation hPair
      cases continuation <;> simp only [pairPost] at hPair
      rename_i final frame'
      rcases hPair with
        ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
          hOutputLocal, hOutput⟩
      have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
        have h := hOutputLocal
        rw [List.getElem?_eq_getElem (by omega)] at h
        exact Option.some.inj h
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      wp_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
      change UInt64Array.At final outputPtr (FormalSpec.expected input)
      rw [hExpected]
      exact hOutput
    · exact constResultProgram_spec _ env initial _ heapTop allocs 0 0 1 rfl
        rfl rfl (by decide) (by decide) hFitMemory hPages rfl hHeapTop
        hFreeList hAllocs

end LeanExeGen.GeneratedRd1e76d3580ead0d9.Behavior
