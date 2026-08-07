import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayPairResult

namespace Project.ProofKit.FixedArraySearch

open Wasm

def finalPost (module_ : Wasm.Module) (env : HostEnv Unit)
    (expected : Array UInt64) : Assertion Unit :=
  FixedArrayEqNode.branchPost module_ env [.localGet 14]
    (FixedArrayPairResult.publicPost expected)

theorem resultContinuation_eq (module_ : Wasm.Module) (env : HostEnv Unit)
    (expected : Array UInt64) :
    FixedArrayPairResult.resultContinuation module_ env expected =
      finalPost module_ env expected := by
  funext continuation
  cases continuation <;> rfl

theorem pairPost_branchN_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (expected : Array UInt64)
    (first second : UInt64) (hExpected : expected = #[first, second])
    (branches : Nat) :
    FixedArrayPairResult.pairPost first second ⇛
      FixedArrayEqNode.branchN module_ env branches
        (finalPost module_ env expected) := by
  induction branches with
  | zero =>
      simpa [FixedArrayEqNode.branchN, resultContinuation_eq] using
        FixedArrayPairResult.pairPost_conseq module_ env expected first second
          hExpected
  | succ branches ih =>
      intro continuation hPair
      have hNext := ih continuation hPair
      cases continuation <;>
        simp only [FixedArrayPairResult.pairPost] at hPair
      rename_i final frame
      rcases hPair with
        ⟨outputPtr, hValues, hParams, hLocals, hOutput, hArray⟩
      have hFrame : { frame with values := [] } = frame := by
        cases frame
        simp_all
      simp only [FixedArrayEqNode.branchN, FixedArrayEqNode.branchPost]
      simpa only [wp_simp, hFrame] using hNext

structure PairResultContext (module_ : Wasm.Module) (st : Store Unit)
    (heapTop allocs inputPtr : UInt64) (input expected : Array UInt64) : Prop where
  inputAt : UInt64Array.At st inputPtr input
  inputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat
  fitExpected : heapTop.toNat + 48 + 8 * (expected.size + 1) ≤
    st.mem.pages * 65536
  pages : st.mem.pages ≤ 65536
  memory32 : module_.memIs64 = false
  heapTopGlobal : st.globals.globals[0]? = some (.i64 heapTop)
  freeListGlobal : st.globals.globals[1]? = some (.i64 0)
  allocsGlobal : st.globals.globals[2]? = some (.i64 allocs)

theorem inputResultProgram_branchN_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr key : UInt64}
    {input expected : Array UInt64}
    {offset keyLocal index destination branches : Nat}
    (hFrame : FixedArrayEqNode.SearchFrame offset keyLocal frame inputPtr key)
    (hLocalWindow : offset + 14 = 24)
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hIndex : index < input.size)
    (hContext : PairResultContext module_ st heapTop allocs inputPtr input
      expected)
    (hExpected : expected = #[input[index], 1]) :
    wp module_ (FixedArrayPairResult.inputResultProgram index destination)
      (FixedArrayEqNode.branchN module_ env branches
        (finalPost module_ env expected)) st frame env := by
  apply Wasm.wp.conseq
    (Q := FixedArrayPairResult.pairPost input[index] 1)
  · exact pairPost_branchN_conseq module_ env expected input[index] 1
      hExpected branches
  · have hFitMemory := hContext.fitExpected
    have hLocals : frame.locals.length = 24 := by
      rw [hFrame.2.1]
      exact hLocalWindow
    rw [hExpected] at hFitMemory
    exact FixedArrayPairResult.inputResultProgram_spec module_ env st frame
      heapTop allocs inputPtr input index destination hFrame.1 hLocals
      hFrame.2.2.1 hDestinationPositive hDestination hContext.inputAt hIndex
      hContext.inputBelow (by simpa using hFitMemory) hContext.pages
      hContext.memory32 hContext.heapTopGlobal hContext.freeListGlobal
      hContext.allocsGlobal

theorem constResultProgram_branchN_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {st : Store Unit}
    {frame : Locals} {heapTop allocs inputPtr key first second : UInt64}
    {input expected : Array UInt64}
    {offset keyLocal destination branches : Nat}
    (hFrame : FixedArrayEqNode.SearchFrame offset keyLocal frame inputPtr key)
    (hLocalWindow : offset + 14 = 24)
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hContext : PairResultContext module_ st heapTop allocs inputPtr input
      expected)
    (hExpected : expected = #[first, second]) :
    wp module_
      (FixedArrayPairResult.constResultProgram first second destination)
      (FixedArrayEqNode.branchN module_ env branches
        (finalPost module_ env expected)) st frame env := by
  apply Wasm.wp.conseq (Q := FixedArrayPairResult.pairPost first second)
  · exact pairPost_branchN_conseq module_ env expected first second hExpected
      branches
  · have hFitMemory := hContext.fitExpected
    have hLocals : frame.locals.length = 24 := by
      rw [hFrame.2.1]
      exact hLocalWindow
    rw [hExpected] at hFitMemory
    exact FixedArrayPairResult.constResultProgram_spec module_ env st frame
      heapTop allocs first second destination (by simp [hFrame.1]) hLocals
      hFrame.2.2.1 hDestinationPositive hDestination
      (by simpa using hFitMemory) hContext.pages hContext.memory32
      hContext.heapTopGlobal hContext.freeListGlobal hContext.allocsGlobal

end Project.ProofKit.FixedArraySearch
