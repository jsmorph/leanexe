import Project.EulerGridStep.GridInitialFacts
import Project.EulerGridStep.RecyclingFinishCode
import Project.EulerGridStep.RecyclingLoop

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Complete valid branch: allocation, initialization, every cell, and final release. -/
theorem recycling_valid_body_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer allocs releases frees : UInt64)
    (base : Nat) (input target : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hCells : 0 < input.size / 3)
    (hPages : initial.mem.pages ≤ 65536)
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ initial.mem.pages * 65536)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base (1 + 6 * (input.size / 3)) 0)))
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base (1 + 6 * (input.size / 3)) slot) (1 + 6 * (input.size / 3)) pointer input.size)
    (hTarget : target = Model.fill ratio input 0 (Array.replicate (1 + 6 * (input.size / 3)) 0) (input.size / 3))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (index : Nat) (output : Array UInt64) (root : UInt64) (scratch : GridScratch),
      target = output → UInt64Array.At final root output →
      wp m rest Q final (recyclingFinishFrame ratio pointer (arenaRoot base output.size 0) root (input.size / 3) index scratch) env) :
    wp m (gridValidBody ++ rest) Q initial (gridValidEntryFrame ratio pointer input.size) env := by
  rw [grid_valid_regions]
  simp only [List.append_assoc]
  apply initial_arena_spec m env initial (gridValidEntryFrame ratio pointer input.size)
    pointer allocs releases frees base input
    (grid_guard_params ratio pointer input.size) (grid_guard_locals ratio pointer input.size) rfl rfl
    hInput hCells hPages layout.memory32 hBudget hHeap hFree hAllocs hReleases hFrees (hSeparate 0 (by omega))
  intro initialized hBuffers hInitializedHeap hInitializedPages hInitializedInput
  have hState : GridLoopStorage initialized base (input.size / 3) 0
      (Array.replicate (1 + 6 * (input.size / 3)) 0) (allocs + 1) releases frees :=
    .initial _ _ _ hBuffers hInitializedHeap (by rw [hInitializedPages]; exact hBudget)
  have hOwned := hBuffers.liveAt
    ⟨arenaRoot base (1 + 6 * (input.size / 3)) 0, Array.replicate (1 + 6 * (input.size / 3)) 0⟩ (by simp)
  obtain ⟨hp, hl, hv, hr⟩ := initial_grid_frame_facts ratio pointer base input.size
  apply grid_setup_spec m env initialized
    (initialGridFrame (gridValidEntryFrame ratio pointer input.size) pointer base input.size)
    (arenaRoot base (1 + 6 * (input.size / 3)) 0) hp hl hv hr
  rw [initial_grid_setup_frame]
  have hLoop := recycling_loop_spec layout env initialized ratio pointer
    (arenaRoot base (1 + 6 * (input.size / 3)) 0) input
    (Array.replicate (1 + 6 * (input.size / 3)) 0) base 0
    hInitializedInput (by omega) (by simp) (by simpa only [Array.size_replicate] using recycling_initial_state (pointer := pointer) hState)
    (by right; simp) hCells
    (by simpa only [Array.size_replicate] using hOwned)
    hSeparate (gridInitialScratch ratio base input.size) target
    (by simpa only [gridRemaining, Nat.sub_zero] using hTarget)
    Q (gridValidBody.drop 93 ++ rest) (by
      intro current i out nextRoot sc hGrid hPositive hi hsz hStore hOwn hDone ht
      apply recycling_finish_spec layout env current ratio pointer (arenaRoot base out.size 0) nextRoot
        (input.size / 3) i out (Array.replicate out.size 0) (hStore.finish hPositive) hOwn sc Q rest
      intro final hOutput
      exact hNext final i out nextRoot sc ht hOutput)
  simpa only [Array.size_replicate] using hLoop

#print axioms recycling_valid_body_spec
end Project.EulerGridStep.Execution
