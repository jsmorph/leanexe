import Project.LebU32.Decision
import Project.LebU32.FinalStep
import Project.LebU32.ContinueStep
import Project.ProofKit.FixedArrayEqNode

namespace Project.LebU32.Spec
open Wasm Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

def dispatchCode : Wasm.Program := decisionCode ++ [.iff 0 0 finalByteCode continueByteCode, .br 0]

theorem branchPost_of_wp (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (rest : Wasm.Program) (Q : Assertion Unit) (hValues : frame.values = [])
    (hNext : wp «module» rest Q store frame env) :
    wp «module» [] (FixedArrayEqNode.branchPost «module» env rest Q) store frame env := by
  have hFrame : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  simpa only [wp_nil, FixedArrayEqNode.branchPost, hFrame] using hNext

theorem dispatch_spec (env : HostEnv Unit) (seed : Heap) (initial current : Store Unit)
    (input value : UInt64) (base : Locals) (count : Nat) (bytes : ByteArray)
    (facts : RunningFacts seed initial input current base count value bytes)
    (hLength : (lebList 10 input).length ≤ 5)
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, encodingInvariant seed initial input final result →
      encodingMeasure final result < encodingMeasure current base →
      wp «module» (.br 0 :: rest) Q final result env) :
    wp «module» (dispatchCode ++ rest) Q current base env := by
  rw [dispatchCode, List.append_assoc]
  apply decision_spec env current base _ _ _ _ facts.frame
  intro frame hFrame
  have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hFrame.values.symm
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  by_cases hRest : value / 128 = 0
  · rw [ite_eq_left (by simp [hRest])]
    apply Wasm.wp.conseq (Q := FixedArrayEqNode.branchPost «module» env (.br 0 :: rest) Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simp only [hEmpty]
      change wp «module» (finalByteCode ++ []) _ current frame env
      apply finalStep_spec env seed initial current input value base frame count bytes facts hFrame
        hLength hRest hFit hMemory hPages hCap
      intro final result hFinished hDecrease
      obtain ⟨output, hBytes, hResultFrame, hStorage⟩ := hFinished
      apply branchPost_of_wp env final result (.br 0 :: rest) Q hResultFrame.values
      exact hNext final result (Or.inr ⟨output, hBytes, hResultFrame, hStorage⟩) hDecrease
  · rw [ite_eq_right (by simp [hRest])]
    apply Wasm.wp.conseq (Q := FixedArrayEqNode.branchPost «module» env (.br 0 :: rest) Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simp only [hEmpty]
      change wp «module» (continueByteCode ++ []) _ current frame env
      apply continueStep_spec env seed initial current input value base frame count bytes facts hFrame
        hLength hRest hFit hMemory hPages hCap
      intro final result hRunning hDecrease
      obtain ⟨count', value', bytes', hFacts⟩ := hRunning
      apply branchPost_of_wp env final result (.br 0 :: rest) Q hFacts.frame.values
      exact hNext final result (Or.inl ⟨count', value', bytes', hFacts⟩) hDecrease

#print axioms dispatch_spec
end Project.LebU32.Spec
