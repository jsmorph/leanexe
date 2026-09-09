import Project.EulerGridStep.GridFinalRelease
import Project.EulerGridStep.GridLoop

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def gridFinishFrame (ratio pointer : UInt64) (base cells index : Nat) (output : Array UInt64)
    (scratch : GridScratch) : Locals :=
  let root := gridLoopRoot base output.size index output[0]!
  let frame := gridLoopFrame ratio pointer (arenaRoot base output.size 0) root cells index scratch
  { frame with locals := (frame.locals.set 29 (.i64 root)).set 30 (.i64 root), values := [] }

/-- Exact post-loop return staging and guarded release of the initial array. -/
theorem grid_finish_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer : UInt64)
    (base cells index : Nat) (output : Array UInt64) (allocs releases frees : UInt64)
    (hPositive : 0 < index) (hIndex : index ≤ cells)
    (hStorage : GridLoopStorage initial base cells index output allocs releases frees)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (scratch : GridScratch) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, UInt64Array.At final (gridLoopRoot base output.size index output[0]!) output →
      wp m rest Q final (gridFinishFrame ratio pointer base cells index output scratch) env) :
    wp m (gridValidBody.drop 93 ++ rest) Q initial
      (gridLoopFrame ratio pointer (arenaRoot base output.size 0)
        (gridLoopRoot base output.size index output[0]!) cells index scratch) env := by
  have hBudget := hStorage.budget
  have hPages := hStorage.buffers.pages
  have hBudget32 : base + (cells + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hRootNat := arena_root_toNat_of_lt base output.size 0 (cells + 6) (by omega) hBudget32
  have hRootNonzero : arenaRoot base output.size 0 ≠ 0 := by
    intro h
    have hn := congrArg UInt64.toNat h
    rw [hRootNat, UInt64.toNat_zero] at hn
    omega
  have hCall := grid_final_release layout env initial base cells index output allocs releases frees
    hPositive hIndex hStorage hProtected
  unfold gridValidBody func36
  simp only [List.drop, List.cons_append, List.nil_append]
  grid_loop_peel
  simp only [List.cons_append, List.nil_append]
  grid_loop_peel
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hOutput, hBuffers, hHeap, hFinalPages⟩
  grid_loop_peel
  simpa [gridFinishFrame, gridLoopFrame] using hNext final hOutput

#print axioms grid_finish_spec
end Project.EulerGridStep.Execution
