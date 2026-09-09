import Project.EulerGridStep.GridLoopTransition

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- One exact cell call preserves the complete outer-loop storage invariant. -/
theorem gridLoop_advance {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3)) (hStatus : output[0]! = 0)
    (hStorage : GridLoopStorage initial base (input.size / 3) index output allocs releases frees)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (gridLoopRoot base output.size index output[0]!), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        let next := Model.advanceAt ratio input output index
        values = [.i64 (gridLoopRoot base next.size (index + 1) next[0]!),
          .i64 (gridLoopRoot base next.size (index + 1) next[0]!)] ∧
        (∃ a r f, GridLoopStorage final base (input.size / 3) (index + 1) next a r f) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        UInt64Array.At final (gridLoopRoot base output.size index output[0]!) output ∧
        (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At final output.size) := by
  dsimp only
  rw [gridLoopRoot_advance base index ratio input output (by omega) hStatus]
  cases hStorage with
  | initial a r f hBuffers hHeap hBudget =>
      simp only [gridLoopRoot, ite_true]
      apply (advanceAt_first_preserved_outcome layout env initial ratio inputUnused pointer unused allocs releases frees base
        input (Array.replicate (1 + 6 * (input.size / 3)) 0) hInput hi hSize
        (by simpa using hBuffers) (by simpa using hHeap) (by simpa using hBudget) hSeparate).mono
      rintro final values ⟨hv, ha, hp, hg, ho, hb⟩
      refine ⟨hv, gridLoopStorage_of_advance (by simpa using (show 0 < 1 + 6 * (input.size / 3) by omega)) hStatus ha,
        hp, hg, ho, ?_⟩
      simpa only [Array.size_replicate] using hb
  | accepted i out a r f hPositive hs hArena =>
      simp only [gridLoopRoot, Nat.ne_of_gt hPositive, ite_false, hs, ite_true]
      apply (advanceAt_later_protected_outcome layout env initial ratio inputUnused pointer unused allocs releases frees base
        input output index hInput hPositive hi hSize hArena (Array.replicate output.size 0) hProtected hSeparate).mono
      rintro final values ⟨hv, ha, hp, hg, ho, hb⟩
      exact ⟨hv, gridLoopStorage_of_advance (by omega) hs ha, hp, hg, ho, hb⟩
  | rejected i out a r f hPositive hArena =>
      have h := hStatus.symm.trans hArena.status
      exact False.elim (by simpa using h)

#print axioms gridLoop_advance
end Project.EulerGridStep.Execution
