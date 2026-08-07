import Project.ProofKit.FixedArraySearch

namespace Project.ProofKit.FixedArraySearchChain

open Wasm

inductive Chain where
  | last (keyIndex valueIndex foundDestination missDestination : Nat)
  | next (keyIndex valueIndex foundDestination : Nat) (tail : Chain)
  deriving Repr

def Chain.result : Chain → Array UInt64 → UInt64 → Array UInt64
  | .last keyIndex valueIndex _ _, input, key =>
      if input[keyIndex]! = key then #[input[valueIndex]!, 1] else #[0, 0]
  | .next keyIndex valueIndex _ tail, input, key =>
      if input[keyIndex]! = key then #[input[valueIndex]!, 1]
      else tail.result input key

def Chain.Valid (input : Array UInt64) : Chain → Prop
  | .last keyIndex valueIndex foundDestination missDestination =>
      keyIndex < input.size ∧ valueIndex < input.size ∧
        0 < foundDestination ∧ foundDestination < 25 ∧
        0 < missDestination ∧ missDestination < 25
  | .next keyIndex valueIndex foundDestination tail =>
      keyIndex < input.size ∧ valueIndex < input.size ∧
        0 < foundDestination ∧ foundDestination < 25 ∧ tail.Valid input

def Chain.program (offset keyLocal : Nat) : Chain → Wasm.Program
  | .last keyIndex valueIndex foundDestination missDestination =>
      FixedArrayEqNode.program offset keyIndex keyLocal
        (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
        (FixedArrayPairResult.constResultProgram 0 0 missDestination)
  | .next keyIndex valueIndex foundDestination tail =>
      FixedArrayEqNode.program offset keyIndex keyLocal
        (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
        (tail.program offset keyLocal)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1048576 in
theorem Chain.program_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr key : UInt64}
    {input expected : Array UInt64} {offset keyLocal branches : Nat}
    (chain : Chain)
    (hFrame : FixedArrayEqNode.SearchFrame offset keyLocal frame inputPtr key)
    (hValid : chain.Valid input)
    (hKeyPositive : 0 < keyLocal)
    (hKeyBeforeScratch : keyLocal < offset + 5)
    (hLocalWindow : offset + 14 = 24)
    (hContext : FixedArraySearch.PairResultContext module_ st heapTop allocs
      inputPtr input expected)
    (hExpected : expected = chain.result input key) :
    wp module_ (chain.program offset keyLocal)
      (FixedArrayEqNode.branchN module_ env branches
        (FixedArraySearch.finalPost module_ env expected)) st frame env := by
  induction chain generalizing frame branches with
  | last keyIndex valueIndex foundDestination missDestination =>
      rcases hValid with
        ⟨hKeyIndex, hValueIndex, hFoundPositive, hFoundBound,
          hMissPositive, hMissBound⟩
      change wp module_
        (FixedArrayEqNode.program offset keyIndex keyLocal _ _ ++ [])
        _ st frame env
      refine hFrame.program_spec hContext.inputAt hKeyIndex hKeyPositive
        hKeyBeforeScratch ?_ ?_
      · intro hEqual
        change wp module_
          (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        exact FixedArraySearch.inputResultProgram_branchN_spec
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hLocalWindow
          hFoundPositive hFoundBound hValueIndex hContext (by
            rw [hExpected]
            simp [Chain.result, getElem!_pos input keyIndex hKeyIndex,
              getElem!_pos input valueIndex hValueIndex, hEqual])
      · intro hUnequal
        change wp module_
          (FixedArrayPairResult.constResultProgram 0 0 missDestination)
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        exact FixedArraySearch.constResultProgram_branchN_spec
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hLocalWindow
          hMissPositive hMissBound hContext (by
            rw [hExpected]
            simp [Chain.result, getElem!_pos input keyIndex hKeyIndex,
              hUnequal])
  | next keyIndex valueIndex foundDestination tail ih =>
      rcases hValid with
        ⟨hKeyIndex, hValueIndex, hFoundPositive, hFoundBound, hTailValid⟩
      change wp module_
        (FixedArrayEqNode.program offset keyIndex keyLocal _ _ ++ [])
        _ st frame env
      refine hFrame.program_spec hContext.inputAt hKeyIndex hKeyPositive
        hKeyBeforeScratch ?_ ?_
      · intro hEqual
        change wp module_
          (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        exact FixedArraySearch.inputResultProgram_branchN_spec
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hLocalWindow
          hFoundPositive hFoundBound hValueIndex hContext (by
            rw [hExpected]
            simp [Chain.result, getElem!_pos input keyIndex hKeyIndex,
              getElem!_pos input valueIndex hValueIndex, hEqual])
      · intro hUnequal
        have hExpectedTail : expected = tail.result input key := by
          rw [hExpected]
          simp [Chain.result, getElem!_pos input keyIndex hKeyIndex, hUnequal]
        exact ih (frame := FixedArrayEqNode.branchFrame offset frame inputPtr
          keyIndex input[keyIndex]) (branches := branches + 1)
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hTailValid hExpectedTail

def Chain.wrapperProgram (chain : Chain) (inputLocal expectedSize offset
    keyIndex keyLocal invalidDestination : Nat) : Wasm.Program :=
  FixedArraySearch.wrapperProgram (chain.program offset keyLocal) inputLocal
    expectedSize offset keyIndex keyLocal invalidDestination

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1048576 in
theorem Chain.wrapperProgram_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr : UInt64}
    {input expected : Array UInt64}
    {inputLocal expectedSize offset keyIndex keyLocal invalidDestination : Nat}
    (chain : Chain)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInputLocalPositive : 0 < inputLocal)
    (hInputLocal : inputLocal < 1 + frame.locals.length)
    (hExpectedSizeBound : expectedSize < UInt64.size)
    (hInput : UInt64Array.At st inputPtr input)
    (hContext : FixedArraySearch.PairResultContext module_ st heapTop allocs
      inputPtr input expected)
    (hInvalidDestinationPositive : 0 < invalidDestination)
    (hInvalidDestination : invalidDestination < 25)
    (hKeyIndex : input.size = expectedSize → keyIndex < input.size)
    (hKeyPositive : 0 < keyLocal)
    (hKeyBeforeScratch : keyLocal < offset + 5)
    (hKey : keyLocal < offset + 15)
    (hLocalWindow : offset + 14 = 24)
    (hInvalidExpected : input.size ≠ expectedSize → expected = #[0, 0])
    (hChainValid : input.size = expectedSize → chain.Valid input)
    (hValidExpected : input.size = expectedSize →
      expected = chain.result input input[keyIndex]!) :
    wp module_
      (chain.wrapperProgram inputLocal expectedSize offset keyIndex keyLocal
        invalidDestination)
      (FixedArrayPairResult.publicPost expected) st frame env := by
  unfold Chain.wrapperProgram
  apply FixedArraySearch.wrapperProgram_spec hParams hLocals hValues
    hInputLocalPositive hInputLocal hExpectedSizeBound hInput hContext
    hInvalidDestinationPositive hInvalidDestination hKeyIndex hKeyPositive
    hKey hLocalWindow hInvalidExpected
  intro hSize searchFrame hSearch
  exact chain.program_spec (env := env) (branches := 0) hSearch
    (hChainValid hSize) hKeyPositive hKeyBeforeScratch hLocalWindow hContext
    (hValidExpected hSize)

end Project.ProofKit.FixedArraySearchChain
