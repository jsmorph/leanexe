import Project.Beck.ExecutionRounds

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem rounds_zero_exact (env : HostEnv Unit) (initial : Store Unit)
    (input : Input) (point : Point) (inputOwner inputRoot pointOwner pointRoot : UInt64)
    (represented : UInt64Array.At initial pointRoot point.numerators) (frozen : allFrozen point = true) :
    TerminatesWith env Project.Beck.«module» 34 initial
      (roundsParams (inputOwner := inputOwner) 0 input point inputRoot pointOwner pointRoot).reverse
      (fun final values => final = initial ∧ values = pointValues point pointOwner pointRoot) := by
  let params := roundsParams (inputOwner := inputOwner) 0 input point inputRoot pointOwner pointRoot
  let locals : List Value := List.replicate 61 (.i64 0)
  let ready : Locals := { params := params, locals := locals }
  have paramsSize : params.length = 10 := by simp [params, roundsParams, matrixParams, inputValues, pointValues]
  have state := roundsEntry_state point pointOwner pointRoot
  refine TerminatesWith.of_wp_entry_for (f := func34Def) rfl ?_
  change wp Project.Beck.«module» func34 _ initial ready env
  rw [rounds_function_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = ready) ?_ ?_
  · exact roundsEntry_exact env initial params paramsSize _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply BlockLoop.program_spec Project.Beck.«module» env initial ready roundsBody
    (fun store frame => store = initial ∧ frame = ready)
    (fun store frame => store = initial ∧ frame = ready) (fun _ _ => 0)
  · rintro store frame ⟨_, rfl⟩
    rfl
  · rintro store frame ⟨_, rfl⟩
    rfl
  · exact ⟨rfl, rfl⟩
  · rintro store frame ⟨same, frameSame⟩
    subst store frame
    apply roundsGuard_exact (inputOwner := inputOwner) env initial locals 0 input point inputRoot pointOwner pointRoot 0 false
      (by decide) state
    · intro nonzero
      exact False.elim (nonzero rfl)
    · intro _
      exact ⟨rfl, rfl⟩
  · rintro store frame ⟨same, frameSame⟩
    subst store frame
    apply roundsReturn_exact (inputOwner := inputOwner) env initial locals 0 input point inputRoot pointOwner pointRoot 0 false
      state represented frozen
    intro finalFrame correct
    refine ⟨rfl, ?_⟩
    simp only [func34Def, correct, pointValues]
    rfl

#print axioms rounds_zero_exact

end Project.Beck.Execution
