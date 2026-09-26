import Project.EulerGridStep.RecyclingFirst
import Project.EulerGridStep.RecyclingSecond

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The loop dispatches its first, second, and reusable allocation phases. -/
theorem recycling_advance {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio inputUnused pointer unused root : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3)) (hStatus : output[0]! = 0)
    (hState : RecyclingState initial base pointer input output index root)
    (hInitial : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 root, .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (RecyclingAdvancePost m env base pointer ratio root input output index) := by
  rcases hState.running hStatus hi with ⟨rfl, rfl, a, r, f, hStorage⟩ |
    ⟨rfl, rfl, a, r, f, hFirst⟩ | ⟨roots, a, r, f, rfl, hPool⟩
  · cases hStorage with
    | initial a r f hBuffers hHeap hBudget =>
      apply recycling_first_transition layout env initial ratio inputUnused pointer unused a r f base input
        (Array.replicate (1 + 6 * (input.size / 3)) 0) hInput hi hSize (by simp)
      · simpa only [Array.size_replicate] using hBuffers
      · simpa only [Array.size_replicate] using hHeap
      · simpa only [Array.size_replicate] using hBudget
      · exact hSeparate
    | accepted i out a r f hPositive _ _ => omega
    | rejected i out a r f hPositive _ => omega
  · exact recycling_second_transition layout env initial ratio inputUnused pointer unused a r f base input
      output hInput hi hSize hFirst hInitial hSeparate
  · exact recycling_reused_transition layout env initial roots ratio inputUnused pointer unused a r f
      base input output index hInput hi hSize hPool hInitial

#print axioms recycling_advance
end Project.EulerGridStep.Execution
