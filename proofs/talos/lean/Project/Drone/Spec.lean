import Project.Drone.ExecutionCompute
import Project.Drone.WholeFlight

namespace Project.Drone.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Examples.Drone

/-- The returned WASM pointer contains exactly the source output. The borrowed
terrain remains intact, and total linear memory stays within 64 MiB. -/
def ResultAt (terrainPointer : UInt64) (terrain : Array UInt64)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ pointer : UInt64, values = [.i64 pointer] ∧
    UInt64Array.At final pointer (compute terrain) ∧
    UInt64Array.At final terrainPointer terrain ∧ final.mem.pages * 65536 ≤ 67108864

/-- All input sizes and height words are covered, including rejection. The
preconditions describe a valid caller heap, a borrowed input array, and enough
headroom for the checked worst-case allocation budget within 1,024 WASM pages. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (source : FreeNode) (terrain : Array UInt64),
    heap.At store → Execution.BorrowedWords heap store source terrain →
    OutputBudget store heap 37580992 1024 m →
    TerminatesWith env m 25 store [.i64 source.root] (ResultAt source.root terrain)

theorem compute_correct : ExactSpecFor Project.Drone.«module» := by
  intro env store heap source terrain hHeap hTerrain hBudget
  apply (Execution.compute_exact env store heap source terrain 0 1024 hTerrain hHeap
    (by simpa only [Nat.add_zero] using hBudget)).mono
  rintro final values ⟨root, rfl, nextHeap, node, _, hFinalBudget, hOutput, hPreserve, _, hValues⟩
  have hRoot : root = node.root := by simpa using hValues
  subst root
  refine ⟨node.root, rfl, (Execution.borrow_owned hOutput).values,
    (hPreserve.borrowed source terrain hTerrain).values, ?_⟩
  have hPages := hFinalBudget.pages
  omega

/-- Exact memory agreement transfers the source whole-flight guarantees to the
compiled result, under the same point-mass model and accepted-input assumptions. -/
noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (source : FreeNode) (terrain : Array UInt64),
    heap.At store → Execution.BorrowedWords heap store source terrain →
    OutputBudget store heap 37580992 1024 m → Feasibility.terrainBound terrain → 0 < terrain.size →
    TerminatesWith env m 25 store [.i64 source.root]
      (fun final values => ResultAt source.root terrain final values ∧ WholeFlight.Safe terrain)

theorem compute_safe : SafeSpecFor Project.Drone.«module» := by
  intro env store heap source terrain hHeap hTerrain hBudget hBound hPositive
  apply (compute_correct env store heap source terrain hHeap hTerrain hBudget).mono
  intro final values hResult
  exact ⟨hResult, WholeFlight.compute_safe terrain hBound hPositive⟩

#print axioms compute_correct
#print axioms compute_safe
end Project.Drone.Spec
