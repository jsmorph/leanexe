import Project.EulerRiemann.FrozenExecutionInitialScalars
import Project.EulerRiemann.FrozenExecutionInputs

namespace Project.EulerRiemann.Frozen.Execution
open Wasm

local macro "initial_quadrant" fDef:ident "unfolding" f:ident : tactic => `(tactic|
  (refine TerminatesWith.of_wp_entry_for (f := $fDef) rfl ?_ (by decide)
   change wp Project.EulerRiemann.Frozen.«module» $f _ _ (($fDef).toLocals []) _
   unfold $f
   wp_run [$fDef:ident, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
   refine wp_call_tw (conservative_exact _ _ _ _ _ _) ?_
   rintro current values ⟨hStore, hValues⟩
   subst current
   subst values
   wp_run [$fDef:ident, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
   simp [stateValues, Initial.bottomLeft, Initial.bottomRight, Initial.topLeft, Initial.topRight]))

theorem bottomLeft_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 89 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.bottomLeft) := by
  initial_quadrant func89Def unfolding func89

theorem bottomRight_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 90 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.bottomRight) := by
  initial_quadrant func90Def unfolding func90

theorem topLeft_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 91 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.topLeft) := by
  initial_quadrant func91Def unfolding func91

theorem topRight_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 92 initial []
      (fun final values => final = initial ∧ values = stateValues Initial.topRight) := by
  initial_quadrant func92Def unfolding func92

#print axioms bottomLeft_exact
#print axioms bottomRight_exact
#print axioms topLeft_exact
#print axioms topRight_exact

end Project.EulerRiemann.Frozen.Execution
