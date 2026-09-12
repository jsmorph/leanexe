import Project.EulerRiemann.ExecutionInitialScalars
import Project.EulerRiemann.ExecutionInputs

namespace Project.EulerRiemann.Execution
open Wasm

local macro "initial_quadrant" fDef:ident "unfolding" f:ident : tactic => `(tactic|
  (refine TerminatesWith.of_wp_entry_for (f := $fDef) rfl ?_ (by decide)
   change wp Project.EulerRiemann.«module» $f _ _ (($fDef).toLocals []) _
   unfold $f
   wp_run [$fDef:ident, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
   refine wp_call_tw (conservative_exact _ _ _ _ _ _) ?_
   rintro current values ⟨hStore, hValues⟩
   subst current
   subst values
   wp_run [$fDef:ident, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
   simp [stateValues, Initial.bottomLeft, Initial.bottomRight, Initial.topLeft, Initial.topRight]))

theorem bottomLeft_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 82 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.bottomLeft) := by
  initial_quadrant func82Def unfolding func82

theorem bottomRight_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 83 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.bottomRight) := by
  initial_quadrant func83Def unfolding func83

theorem topLeft_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 84 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.topLeft) := by
  initial_quadrant func84Def unfolding func84

theorem topRight_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 85 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.topRight) := by
  initial_quadrant func85Def unfolding func85

#print axioms bottomLeft_exact
#print axioms bottomRight_exact
#print axioms topLeft_exact
#print axioms topRight_exact

end Project.EulerRiemann.Execution
