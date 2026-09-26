import Project.EulerGridStep.RecyclingFrameTactic
import Project.EulerGridStep.RecyclingFinish
import Project.EulerGridStep.RecyclingStateFacts

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def recyclingFinishFrame (ratio pointer initialRoot root : UInt64) (cells index : Nat)
    (scratch : GridScratch) : Locals :=
  let frame := gridLoopFrame ratio pointer initialRoot root cells index scratch
  { frame with
    locals := ((((((frame.locals.set 30 (.i64 root)).set 31 (.i64 root)).set
      32 (.i64 (UInt64.ofNat index))).set 33 (.i64 root)).set 34 (.i64 root)).set 35 (.i64 root)).set 36 (.i64 root)
    values := [] }

/-- Exact post-loop owner copies, alias guard, and release of the initial array. -/
theorem recycling_finish_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer initialRoot root : UInt64)
    (cells index : Nat) (output initialOutput : Array UInt64)
    (hReady : GridFinishReady initial root initialRoot output)
    (hInitial : (⟨initialRoot, initialOutput⟩ : LiveBuffer).At initial output.size)
    (scratch : GridScratch) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, UInt64Array.At final root output →
      wp m rest Q final (recyclingFinishFrame ratio pointer initialRoot root cells index scratch) env) :
    wp m (gridValidBody.drop 93 ++ rest) Q initial
      (gridLoopFrame ratio pointer initialRoot root cells index scratch) env := by
  have hRootNonzero : initialRoot ≠ 0 := liveBuffer_root_nonzero hInitial
  have hDifferent : initialRoot ≠ root := (objectsSeparate_ne hReady.separate).symm
  have hCall := recycling_final_release layout env initial root initialRoot output initialOutput hReady hInitial
  unfold gridValidBody func36
  simp only [List.drop, List.cons_append, List.nil_append]
  recycling_loop_peel
  simp only [List.cons_append, List.nil_append]
  recycling_loop_peel
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hOutput⟩
  recycling_loop_peel
  simpa [recyclingFinishFrame, gridLoopFrame] using hNext final hOutput

#print axioms recycling_finish_spec
end Project.EulerGridStep.Execution
