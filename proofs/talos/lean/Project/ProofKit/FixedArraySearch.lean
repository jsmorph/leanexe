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

end Project.ProofKit.FixedArraySearch
