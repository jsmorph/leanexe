import Project.EulerReconstruction.LimitReturn

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction

theorem limit_exact (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64)
    (center delta : State) (factor : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 38 initial
      ([.i64 factor] ++ stateValues delta ++ stateValues center ++ [.i64 fuel])
      (fun final values => final = initial ∧
        values = facesValues (limit fuel.toNat center delta factor)) := by
  let entry := func38Def.toLocals (limitParams fuel center delta factor)
  have hStart : LimitFrameAt entry fuel center delta factor (constantFaces zeroState) false := by
    constructor <;> rfl
  have hInv : limitInvariant initial center delta (limit fuel.toNat center delta factor)
      initial entry := ⟨rfl, fuel, factor, constantFaces zeroState, false, hStart, rfl⟩
  refine TerminatesWith.of_wp_entry_for (f := func38Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func38 _ initial entry env
  rw [limit_loop_shape, List.append_assoc]
  have hEntry : func38.take 2 = [.constI64 0, .localSet 20] := rfl
  rw [hEntry]
  wp_run [entry, func38Def, limitParams, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp Project.EulerReconstruction.«module»
    ([.block 0 0 [.loop 0 0 limitLoop]] ++ func38.drop 3) _ initial entry env
  apply limit_loop_spec env initial initial entry center delta
    (limit fuel.toNat center delta factor) hInv
  intro current currentFrame hExit
  obtain ⟨hStore, nextFuel, nextFactor, output, done, hFrame, _, hExpected⟩ := hExit
  subst current
  refine wp.conseq ?_
    (limit_return_spec env initial currentFrame nextFuel center delta nextFactor output done hFrame)
  intro control hResult
  cases control <;> simp only [facesPost] at hResult
  rename_i final finalFrame
  obtain ⟨hStore, hValues⟩ := hResult
  rw [← hExpected] at hValues
  simp [hStore, hValues, facesValues, stateValues]

#print axioms limit_exact

end Project.EulerReconstruction.Execution
