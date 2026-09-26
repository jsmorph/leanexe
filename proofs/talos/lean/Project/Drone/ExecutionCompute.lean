import Project.Drone.ExecutionComputeAccept
import Project.Drone.ExecutionComputeGuard
import Project.Drone.ExecutionComputeValidate
import Project.Drone.ExecutionComputeReject

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def ComputeResult (heap : Heap) (store : Store Unit) (terrain : Array UInt64) (remaining pageLimit : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ root : UInt64, values = [.i64 root] ∧
    FreshArrayResult heap store (compute terrain) remaining pageLimit final [.i64 root, .i64 root]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem compute_exact (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (terrainNode : FreeNode) (terrain : Array UInt64) (remaining pageLimit : Nat)
    (hTerrain : BorrowedWords heap store terrainNode terrain) (hHeap : heap.At store)
    (hBudget : Budget store heap (37580992 + remaining) pageLimit) :
    TerminatesWith env Project.Drone.«module» 25 store [.i64 terrainNode.root]
      (ComputeResult heap store terrain remaining pageLimit) := by
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_
  change wp Project.Drone.«module» func25 _ store
    (computeFrame terrainNode.root (List.replicate 30 (.i64 0)) zeroPushScratch) env
  have hCode : func25 = func25.take 19 ++ [.iff 0 0 computeReject computeValidate] ++ func25.drop 20 := rfl
  rw [hCode, List.append_assoc]
  apply compute_guard_spec env store terrainNode.root (List.replicate 30 (.i64 0)) zeroPushScratch terrain rfl hTerrain.values
  refine wp_iff_cons rfl ?_
  by_cases hReject : terrain.size = 0 ∨ 64 < terrain.size
  · simp only [hReject, ↓reduceIte, ne_eq, show (1 : UInt32) ≠ 0 by decide]
    change wp Project.Drone.«module» (computeReject ++ []) _ store _ env
    apply compute_reject_spec env store heap false terrainNode.root (List.replicate 30 (.i64 0))
      { zeroPushScratch with counter := terrainNode.root } remaining pageLimit rfl hHeap (hBudget.mono (by omega))
    intro final root aux s hAux hTarget hResult
    wp_compute_frame [func25, List.drop, func25Def, hAux, hTarget]
    change wp Project.Drone.«module» [.localGet 35] _ final _ env
    wp_compute_frame [func25Def, hAux, hTarget]
    refine ⟨root, rfl, ?_⟩
    have hEmpty : compute terrain = #[] := by
      rcases hReject with hz | hl
      · simp [compute, hz]
      · simp [compute, hl]
    simpa only [hEmpty] using hResult
  · simp only [hReject, ↓reduceIte, ne_eq, eq_self_iff_true, not_true_eq_false]
    have hPositive : 0 < terrain.size := by omega
    have hSize : terrain.size ≤ 64 := by omega
    have hValidate : computeValidate = computeValidate.take 22 ++ [.iff 0 0 computeAccept computeBadHeight] := rfl
    rw [hValidate]
    apply compute_validate_spec env store terrainNode.root (List.replicate 30 (.i64 0))
      { zeroPushScratch with counter := terrainNode.root } terrain rfl hTerrain.values
    intro validated hValidated
    refine wp_iff_cons rfl ?_
    cases hValid : validHeights terrain.size terrain with
    | false =>
      simp only [hValid, Bool.false_eq_true, ↓reduceIte, ne_eq, eq_self_iff_true, not_true_eq_false]
      change wp Project.Drone.«module» (computeBadHeight ++ []) _ store _ env
      apply compute_reject_spec env store heap true terrainNode.root validated
        { zeroPushScratch with counter := terrainNode.root } remaining pageLimit hValidated hHeap (hBudget.mono (by omega))
      intro final root aux s hAux hTarget hResult
      wp_compute_frame [func25, List.drop, func25Def, hAux, hTarget]
      change wp Project.Drone.«module» [.localGet 35] _ final _ env
      wp_compute_frame [func25Def, hAux, hTarget]
      refine ⟨root, rfl, ?_⟩
      simpa [compute, show terrain.size ≠ 0 by omega, show ¬terrain.size > 64 by omega,
        hValid, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte] using hResult
    | true =>
      simp only [hValid, ↓reduceIte, ne_eq, show (1 : UInt32) ≠ 0 by decide]
      change wp Project.Drone.«module» (computeAccept ++ []) _ store _ env
      apply compute_accept_spec env store heap terrainNode terrain validated
        { zeroPushScratch with counter := terrainNode.root } remaining pageLimit hValidated hPositive hTerrain hHeap
        (hBudget.mono (Nat.add_le_add_right (computeCost_bound terrain.size hSize) remaining))
      intro final root aux s hAux hTarget hResult
      wp_compute_frame [func25, List.drop, func25Def, hAux, hTarget]
      change wp Project.Drone.«module» [.localGet 35] _ final _ env
      wp_compute_frame [func25Def, hAux, hTarget]
      refine ⟨root, rfl, ?_⟩
      simpa [compute, show terrain.size ≠ 0 by omega, show ¬terrain.size > 64 by omega,
        hValid, decide_false, Bool.false_or, ↓reduceIte] using hResult

#print axioms compute_exact
end Project.Drone.Execution
