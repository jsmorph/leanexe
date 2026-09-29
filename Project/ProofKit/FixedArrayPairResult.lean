import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayInput
import Project.ProofKit.FixedArrayResult

namespace Project.ProofKit.FixedArrayPairResult

open Wasm

macro "wp_pair24" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

macro "wp_pair_set24" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
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
  simp (config := { maxSteps := 10000000 }) [capacityPrefix,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?, List.length_set,
    hParams, hLocals, hValues]
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
  FixedArrayInput.program 10 index

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
  wp_pair_set24 [hParams, hLocals, hValues]
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
  unfold inputValueProgram
  apply FixedArrayInput.program_spec 10 module_ env st frame inputPtr input index
    hParamsValue (by simpa using hLocals) hValues hInput hIndex
  simpa [inputValueFrame, FixedArrayInput.resultFrame, hValues] using hNext

def pairPost (first second : UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values = [] ∧
        frame.params.length = 1 ∧
        frame.locals.length = 24 ∧
        frame.locals[13]? = some (.i64 outputPtr) ∧
        UInt64Array.At final outputPtr #[first, second]
    | _ => False

def publicPost (expected : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values.take 1 = [.i64 outputPtr] ∧
        UInt64Array.At final outputPtr expected
    | .Return final values => ∃ outputPtr,
        values.take 1 = [.i64 outputPtr] ∧
        UInt64Array.At final outputPtr expected
    | _ => False

def fallthroughPost (module_ : Wasm.Module) (env : HostEnv Unit)
    (expected : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost expected) final
          { frame with values := [] } env
    | _ => False

def resultContinuation (module_ : Wasm.Module) (env : HostEnv Unit)
    (expected : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost expected) final
          { frame with values := [] } env
    | .Break 0 final frame =>
        wp module_ [.localGet 14] (publicPost expected) final
          { frame with values := [] } env
    | .Break (index + 1) final frame =>
        publicPost expected (.Break index final frame)
    | other => publicPost expected other

theorem pairPost_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (expected : Array UInt64)
    (first second : UInt64) (hExpected : expected = #[first, second]) :
    pairPost first second ⇛ resultContinuation module_ env expected := by
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
  wp_pair24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
  simp only [publicPost]
  refine ⟨outputPtr, rfl, ?_⟩
  rw [hExpected]
  exact hOutput

theorem fallthroughPost_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (expected : Array UInt64) :
    fallthroughPost module_ env expected ⇛
      resultContinuation module_ env expected := by
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
  wp_pair24 [hParams, hLocals, hValues, hRootLocal,
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
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
      omega)]
    rw [Memory.write64_bytes_before _ _ _ (by
      simp
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
  apply FixedArrayAllocatorWindow.region_spec 10 module_ env st
    (capacityFrame frame) heapTop 24 1 allocs
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
    let allocFrame := FixedArrayAllocatorWindow.allocFrame 10
      (capacityFrame frame) heapTop 24
    have hAllocValues : allocFrame.values = [] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hValues]
    have hAllocParams : allocFrame.params.length = 1 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParams]
    have hAllocLocals : allocFrame.locals.length = 24 := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hLocals]
    have hRoot : allocFrame.get 15 = some (.i64 (heapTop + 48)) := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParams, hLocals, Wasm.Locals.get]
    have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
        allocSt.mem.pages * 65536 := by
      rw [hRootToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hFirstBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages *
            65536 := by
      rw [hFirstToNat32, FixedArrayResult.writeLength_pages]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hSecondBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writePayload
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 2)
            (heapTop + 48) 0 first).mem.pages * 65536 := by
      rw [FixedArrayResult.writePayload_pages,
        FixedArrayResult.writeLength_pages, hSecondToNat32]
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
        (heapTop + 48) second (by
          simpa [scratchFrame_params] using hAllocParams) (by
          simpa [scratchFrame_locals_length] using hAllocLocals)
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
  apply FixedArrayAllocatorWindow.region_spec 10 module_ env st
    (capacityFrame frame) heapTop 24 1 allocs
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
    let allocFrame := FixedArrayAllocatorWindow.allocFrame 10
      (capacityFrame frame) heapTop 24
    have hAllocValues : allocFrame.values = [] := by
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hValues]
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
      simp [allocFrame, FixedArrayAllocatorWindow.allocFrame, capacityFrame,
        hParams, hLocals, Wasm.Locals.get]
    have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
        allocSt.mem.pages * 65536 := by
      rw [hRootToNat32]
      simp only [allocSt, FixedArrayAllocator.allocStore_pages]
      omega
    have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
      exact input_preserved_by_alloc st heapTop 24 1 allocs inputPtr input
        hInput hInputBelow (by simpa using hFitMemory) hPages
    have hInputAfterLength : UInt64Array.At
        (FixedArrayResult.writeLength allocSt (heapTop + 48) 2)
        inputPtr input := by
      exact hInputAlloc.write64After (address := (heapTop + 48).toUInt32)
        (value := 2) (by rw [hRootToNat32]; omega)
    have hFirstBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writeLength allocSt (heapTop + 48) 2).mem.pages *
            65536 := by
      rw [show
        (FixedArrayResult.payloadAddress (heapTop + 48) 0).toUInt32.toNat =
          heapTop.toNat + 48 + 8 by exact hFirstToNat32]
      simp only [FixedArrayResult.writeLength_pages, allocSt,
        FixedArrayAllocator.allocStore_pages]
      omega
    have hSecondBound :
        (FixedArrayResult.payloadAddress (heapTop + 48) 1).toUInt32.toNat + 8 ≤
          (FixedArrayResult.writePayload
            (FixedArrayResult.writeLength allocSt (heapTop + 48) 2)
            (heapTop + 48) 0 input[index]).mem.pages * 65536 := by
      rw [FixedArrayResult.writePayload_pages,
        FixedArrayResult.writeLength_pages, hSecondToNat32]
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
    (destination : Nat) (expected : Array UInt64)
    (hExpected : expected = #[first, second])
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
      (resultContinuation module_ env expected) st frame env := by
  apply Wasm.wp.conseq (Q := pairPost first second)
  · exact pairPost_conseq module_ env expected first second hExpected
  · exact constResultProgram_spec module_ env st frame heapTop allocs first
      second destination hParams hLocals hValues hDestinationPositive
      hDestination hFitMemory hPages hMemory32 hHeapTop hFreeList hAllocs

theorem inputResultProgram_result_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (heapTop allocs inputPtr : UInt64)
    (input : Array UInt64) (index destination : Nat)
    (hIndex : index < input.size)
    (expected : Array UInt64)
    (hExpected : expected = #[input[index], 1])
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
      (resultContinuation module_ env expected) st frame env := by
  apply Wasm.wp.conseq (Q := pairPost input[index] 1)
  · exact pairPost_conseq module_ env expected input[index] 1 hExpected
  · exact inputResultProgram_spec module_ env st frame heapTop allocs inputPtr
      input index destination hParamsValue hLocals hValues
      hDestinationPositive hDestination hInput hIndex hInputBelow hFitMemory
      hPages hMemory32 hHeapTop hFreeList hAllocs

end Project.ProofKit.FixedArrayPairResult
