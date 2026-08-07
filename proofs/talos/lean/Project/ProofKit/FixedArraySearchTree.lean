import Project.ProofKit.FixedArrayLtNode
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArraySearch

namespace Project.ProofKit.FixedArraySearchTree

open Wasm

inductive Tree where
  | leaf (keyIndex valueIndex foundDestination missDestination : Nat)
  | branch (keyIndex valueIndex foundDestination : Nat)
      (less notLess : Tree)
  deriving Repr

def Tree.result : Tree → Array UInt64 → UInt64 → Array UInt64
  | .leaf keyIndex valueIndex _ _, input, key =>
      if input[keyIndex]! = key then #[input[valueIndex]!, 1] else #[0, 0]
  | .branch keyIndex valueIndex _ less notLess, input, key =>
      if input[keyIndex]! = key then
        #[input[valueIndex]!, 1]
      else if key < input[keyIndex]! then
        less.result input key
      else
        notLess.result input key

def Tree.Valid (input : Array UInt64) : Tree → Prop
  | .leaf keyIndex valueIndex foundDestination missDestination =>
      keyIndex < input.size ∧ valueIndex < input.size ∧
        0 < foundDestination ∧ foundDestination < 25 ∧
        0 < missDestination ∧ missDestination < 25
  | .branch keyIndex valueIndex foundDestination less notLess =>
      keyIndex < input.size ∧ valueIndex < input.size ∧
        0 < foundDestination ∧ foundDestination < 25 ∧
        less.Valid input ∧ notLess.Valid input

def Tree.program (offset keyLocal : Nat) : Tree → Wasm.Program
  | .leaf keyIndex valueIndex foundDestination missDestination =>
      FixedArrayEqNode.keyFirstProgram offset keyIndex keyLocal
        (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
        (FixedArrayPairResult.constResultProgram 0 0 missDestination)
  | .branch keyIndex valueIndex foundDestination less notLess =>
      FixedArrayEqNode.keyFirstProgram offset keyIndex keyLocal
        (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
        (FixedArrayLtNode.program offset keyIndex keyLocal
          (less.program offset keyLocal) (notLess.program offset keyLocal))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1048576 in
theorem Tree.program_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr key : UInt64}
    {input expected : Array UInt64} {offset keyLocal branches : Nat}
    (tree : Tree)
    (hFrame : FixedArrayEqNode.SearchFrame offset keyLocal frame inputPtr key)
    (hValid : tree.Valid input)
    (hKeyPositive : 0 < keyLocal)
    (hKeyBeforeScratch : keyLocal < offset + 5)
    (hLocalWindow : offset + 14 = 24)
    (hContext : FixedArraySearch.PairResultContext module_ st heapTop allocs
      inputPtr input expected)
    (hExpected : expected = tree.result input key) :
    wp module_ (tree.program offset keyLocal)
      (FixedArrayEqNode.branchN module_ env branches
        (FixedArraySearch.finalPost module_ env expected)) st frame env := by
  induction tree generalizing frame branches with
  | leaf keyIndex valueIndex foundDestination missDestination =>
      rcases hValid with
        ⟨hKeyIndex, hValueIndex, hFoundPositive, hFoundBound,
          hMissPositive, hMissBound⟩
      change wp module_
        (FixedArrayEqNode.keyFirstProgram offset keyIndex keyLocal _ _ ++ [])
        _ st frame env
      refine hFrame.keyFirstProgram_spec hContext.inputAt hKeyIndex ?_ ?_
      · intro hEqual
        change wp module_
          (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        exact FixedArraySearch.inputResultProgram_branchN_spec
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hLocalWindow
          hFoundPositive hFoundBound hValueIndex hContext (by
            rw [hExpected]
            simp [Tree.result, getElem!_pos input keyIndex hKeyIndex,
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
            simp [Tree.result, getElem!_pos input keyIndex hKeyIndex,
              hUnequal])
  | branch keyIndex valueIndex foundDestination less notLess ihLess ihNotLess =>
      rcases hValid with
        ⟨hKeyIndex, hValueIndex, hFoundPositive, hFoundBound,
          hLessValid, hNotLessValid⟩
      change wp module_
        (FixedArrayEqNode.keyFirstProgram offset keyIndex keyLocal _ _ ++ [])
        _ st frame env
      refine hFrame.keyFirstProgram_spec hContext.inputAt hKeyIndex ?_ ?_
      · intro hEqual
        change wp module_
          (FixedArrayPairResult.inputResultProgram valueIndex foundDestination)
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        exact FixedArraySearch.inputResultProgram_branchN_spec
          (hFrame.branch hKeyPositive hKeyBeforeScratch) hLocalWindow
          hFoundPositive hFoundBound hValueIndex hContext (by
            rw [hExpected]
            simp [Tree.result, getElem!_pos input keyIndex hKeyIndex,
              getElem!_pos input valueIndex hValueIndex, hEqual])
      · intro hUnequal
        have hNodeFrame : FixedArrayEqNode.SearchFrame offset keyLocal
            (FixedArrayEqNode.branchFrame offset frame inputPtr keyIndex
              input[keyIndex]) inputPtr key :=
          hFrame.branch hKeyPositive hKeyBeforeScratch
        change wp module_
          (FixedArrayLtNode.program offset keyIndex keyLocal _ _ ++ [])
          (FixedArrayEqNode.branchN module_ env (branches + 1)
            (FixedArraySearch.finalPost module_ env expected)) st _ env
        refine FixedArrayLtNode.program_spec offset keyIndex keyLocal _ _ []
          module_ env st _ inputPtr key input hNodeFrame hContext.inputAt
          hKeyIndex _ ?_ ?_
        · intro hIsLess
          have hExpectedLess : expected = less.result input key := by
            rw [hExpected]
            simp [Tree.result, getElem!_pos input keyIndex hKeyIndex,
              hUnequal, hIsLess]
          exact ihLess
            (frame := FixedArrayEqNode.branchFrame offset
              (FixedArrayEqNode.branchFrame offset frame inputPtr keyIndex
                input[keyIndex]) inputPtr keyIndex input[keyIndex])
            (branches := branches + 2)
            (hNodeFrame.branch hKeyPositive hKeyBeforeScratch)
            hLessValid hExpectedLess
        · intro hNotIsLess
          have hExpectedNotLess : expected = notLess.result input key := by
            rw [hExpected]
            simp [Tree.result, getElem!_pos input keyIndex hKeyIndex,
              hUnequal, hNotIsLess]
          exact ihNotLess
            (frame := FixedArrayEqNode.branchFrame offset
              (FixedArrayEqNode.branchFrame offset frame inputPtr keyIndex
                input[keyIndex]) inputPtr keyIndex input[keyIndex])
            (branches := branches + 2)
            (hNodeFrame.branch hKeyPositive hKeyBeforeScratch)
            hNotLessValid hExpectedNotLess

def Tree.wrapperProgram (tree : Tree) (inputLocal expectedSize offset
    keyIndex keyLocal invalidDestination : Nat) : Wasm.Program :=
  FixedArrayLengthDispatch.program inputLocal expectedSize
    (FixedArrayPairResult.constResultProgram 0 0 invalidDestination)
    (FixedArrayEqNode.loadKeyProgram offset keyIndex keyLocal ++
      tree.program offset keyLocal) ++
    [.localGet 14]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1048576 in
theorem Tree.wrapperProgram_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr : UInt64}
    {input expected : Array UInt64}
    {inputLocal expectedSize offset keyIndex keyLocal invalidDestination : Nat}
    (tree : Tree)
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
    (hTreeValid : input.size = expectedSize → tree.Valid input)
    (hValidExpected : input.size = expectedSize →
      expected = tree.result input input[keyIndex]!) :
    wp module_
      (tree.wrapperProgram inputLocal expectedSize offset keyIndex keyLocal
        invalidDestination)
      (FixedArrayPairResult.publicPost expected) st frame env := by
  unfold Tree.wrapperProgram
  apply FixedArrayLengthDispatch.program_spec inputLocal expectedSize _ _ _
    module_ env st frame inputPtr input hParams hValues hInputLocalPositive
    hInputLocal hExpectedSizeBound hInput
  · intro hSize
    have hExpected := hInvalidExpected hSize
    apply Wasm.wp.conseq (Q := FixedArrayPairResult.pairPost 0 0)
    · exact FixedArraySearch.pairPost_branchN_conseq module_ env expected
        0 0 hExpected 0
    · apply FixedArrayPairResult.constResultProgram_spec module_ env st _
        heapTop allocs 0 0 invalidDestination
      · simp [FixedArrayLengthDispatch.branchFrame, hParams]
      · rw [FixedArrayLengthDispatch.branchFrame_locals_length, hLocals,
          hLocalWindow]
      · exact FixedArrayLengthDispatch.branchFrame_values
          inputLocal frame inputPtr
      · exact hInvalidDestinationPositive
      · exact hInvalidDestination
      · have hFit := hContext.fitExpected
        rw [hExpected] at hFit
        simpa using hFit
      · exact hContext.pages
      · exact hContext.memory32
      · exact hContext.heapTopGlobal
      · exact hContext.freeListGlobal
      · exact hContext.allocsGlobal
  · intro hSize
    let lengthFrame := FixedArrayLengthDispatch.branchFrame inputLocal frame
      inputPtr
    have hLengthParams : lengthFrame.params = [.i64 inputPtr] := by
      change (FixedArrayLengthDispatch.branchFrame inputLocal frame
        inputPtr).params = [.i64 inputPtr]
      rw [FixedArrayLengthDispatch.branchFrame_params]
      exact hParams
    have hLengthLocals : lengthFrame.locals.length = offset + 14 := by
      change (FixedArrayLengthDispatch.branchFrame inputLocal frame
        inputPtr).locals.length = offset + 14
      rw [FixedArrayLengthDispatch.branchFrame_locals_length]
      exact hLocals
    have hLengthValues : lengthFrame.values = [] := by
      rfl
    apply FixedArrayEqNode.loadKeyProgram_spec offset keyIndex keyLocal
      module_ env st lengthFrame inputPtr input hLengthParams hLengthLocals
      hLengthValues hInput (hKeyIndex hSize) hKeyPositive hKey
    change wp module_ (tree.program offset keyLocal)
      (FixedArraySearch.finalPost module_ env expected) st _ env
    exact tree.program_spec (env := env) (branches := 0)
      (FixedArrayEqNode.keyFrame_searchFrame offset keyIndex keyLocal
        lengthFrame inputPtr input[keyIndex] hLengthParams hLengthLocals
        hKeyPositive hKey)
      (hTreeValid hSize) hKeyPositive hKeyBeforeScratch hLocalWindow hContext
      (by simpa [getElem!_pos input keyIndex (hKeyIndex hSize)] using
        hValidExpected hSize)

end Project.ProofKit.FixedArraySearchTree
