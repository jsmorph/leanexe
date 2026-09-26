import Project.Beck.ExecutionDetCall

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def determinantStageScratch (tailOwner tailPointer acc : UInt64) (index count : Nat)
    (scratch : DeterminantReadScratch) : DeterminantReadScratch := fun k =>
  if k.val = 15 then .i64 acc else determinantLoopLocal tailOwner tailPointer acc index count scratch k

theorem determinant_stage_shape : (determinantLoop.drop 4).take 4 =
    [.localGet 45, .localSet 22, .localGet 21, .localSet 23] := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem determinantStage_exact (env : HostEnv Unit) (initial : Store Unit)
    (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
      tailOwner tailPointer acc : UInt64) (index count : Nat) (scratch : DeterminantReadScratch)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (determinantReadFrame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        index (determinantStageScratch tailOwner tailPointer acc index count scratch) []) env) :
    wp Project.Beck.«module» ((determinantLoop.drop 4).take 4 ++ rest) Q initial
      (determinantLoopFrame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        tailOwner tailPointer acc index count scratch) env := by
  rw [determinant_stage_shape]
  simp only [determinantLoopFrame, determinant_locals_expanded,
    determinantLoopLocal, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte,
    determinantParams, List.cons_append, List.nil_append]
  wp_fixed_frame
  simpa only [determinantReadFrame, determinantParams, determinantStageScratch, determinantLoopLocal,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte] using next

#print axioms determinantStage_exact

end Project.Beck.Execution
