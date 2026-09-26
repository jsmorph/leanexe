import Project.EulerGridStep.RecyclingState
import Project.EulerGridStep.RecycledAdvance

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- State after optional loop-owner cleanup, ready for the next condition check. -/
def RecyclingAfter (base : Nat) (pointer ratio : UInt64) (input output : Array UInt64)
    (index : Nat) (nextRoot : UInt64) (current : Store Unit) : Prop :=
  RecyclingState current base pointer input (Model.advanceAt ratio input output index) (index + 1) nextRoot ∧
  UInt64Array.At current pointer input ∧
  (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At current output.size

/-- The generated cell call followed by its pending conditional release. -/
def RecyclingAdvancePost (m : Wasm.Module) (env : HostEnv Unit) (base : Nat)
    (pointer ratio root : UInt64) (input output : Array UInt64) (index : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ nextRoot : UInt64,
    values = [.i64 nextRoot, .i64 nextRoot] ∧ nextRoot ≠ 0 ∧ root ≠ nextRoot ∧
    nextRoot ≠ arenaRoot base output.size 0 ∧ UInt64Array.At final root output ∧
    (root = arenaRoot base output.size 0 → RecyclingAfter base pointer ratio input output index nextRoot final) ∧
    (root ≠ arenaRoot base output.size 0 →
      TerminatesWith env m 40 final [.i64 root]
        (fun after returned => returned = [] ∧ RecyclingAfter base pointer ratio input output index nextRoot after))

theorem recycling_reused_transition {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (roots : Nat → UInt64)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hPool : RecycledPool initial roots pointer (arenaRoot base output.size 0) input output allocs releases frees)
    (hInitial : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (roots 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (RecyclingAdvancePost m env base pointer ratio (roots 0) input output index) := by
  apply (recycled_advance layout env initial roots ratio inputUnused pointer unused
    (arenaRoot base output.size 0) allocs releases frees input output (Array.replicate output.size 0)
    index hInput hi hSize hPool hInitial).mono
  rintro final values ⟨nextRoots, hv, hNonzero, hNe, hNeInitial, hOld, hCleanup⟩
  refine ⟨nextRoots 0, hv, hNonzero, hNe, hNeInitial, hOld, ?_, fun _ => ?_⟩
  · intro hEq
    exact False.elim (objectsSeparate_ne (hPool.initialSeparate 0 (by decide)) hEq)
  · apply hCleanup.mono
    rintro after returned ⟨hr, a, r, f, hNext, _, hin, hinit⟩
    refine ⟨hr, ?_, hin, hinit⟩
    apply RecycledPool.recyclingState
    simpa only [advanceAt_size] using hNext

#print axioms recycling_reused_transition
end Project.EulerGridStep.Execution
