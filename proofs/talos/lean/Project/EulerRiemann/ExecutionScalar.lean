import Project.EulerRiemann.Program
import Project.EulerDynamicFlux.Component
import Project.EulerCellStep.Update
import Project.FunctionRegion.Exec

namespace Project.EulerRiemann.Execution
open Wasm Project.FunctionRegion

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def componentDomain (index : Nat) : Prop :=
  index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 8 ∨ index = 9

def componentRename (index : Nat) : Nat :=
  if index < 3 then index + 34 else index + 29

theorem componentShift :
    Shift Project.EulerDynamicFlux.«module» Project.EulerRiemann.«module»
      componentRename componentRename componentDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals simp [componentDomain]

theorem component_core_exact (env : HostEnv Unit) (initial : Store Unit)
    (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 38 initial
      [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧
        values = Project.EulerDynamicFlux.Execution.componentValues alpha fluxL fluxR stateL stateR) :=
  Project.FunctionRegion.terminatesWith componentShift 9 (by simp [componentDomain])
    (Project.EulerDynamicFlux.Execution.componentCheckedBits_exact_in_module
      Project.EulerDynamicFlux.Execution.concreteLayout env initial alpha fluxL fluxR stateL stateR)

theorem component_exact (env : HostEnv Unit) (initial : Store Unit)
    (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 39 initial
      [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧
        values = Project.EulerDynamicFlux.Execution.componentValues alpha fluxL fluxR stateL stateR) := by
  refine TerminatesWith.of_wp_entry_for (f := func39Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func39 _ initial
    (func39Def.toLocals [.i64 alpha, .i64 fluxL, .i64 fluxR, .i64 stateL, .i64 stateR]) env
  unfold func39
  wp_run [func39Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (component_core_exact env initial alpha fluxL fluxR stateL stateR) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_run [func39Def, Project.EulerDynamicFlux.Execution.componentValues, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp

def updateDomain (index : Nat) : Prop :=
  index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 8 ∨ index = 19

def updateRename (index : Nat) : Nat :=
  if index = 19 then 50 else componentRename index

theorem updateShift :
    Shift Project.EulerCellStep.«module» Project.EulerRiemann.«module»
      updateRename updateRename updateDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals simp [updateDomain]

theorem update_core_exact (env : HostEnv Unit) (initial : Store Unit)
    (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 50 initial
      [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR) :=
  Project.FunctionRegion.terminatesWith updateShift 19 (by simp [updateDomain])
    (Project.EulerCellStep.Execution.updateCheckedBits_exact_in_module
      Project.EulerCellStep.Execution.concreteLayout env initial ratio state fluxL fluxR)

theorem update_exact (env : HostEnv Unit) (initial : Store Unit)
    (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 51 initial
      [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR) := by
  refine TerminatesWith.of_wp_entry_for (f := func51Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func51 _ initial
    (func51Def.toLocals [.i64 ratio, .i64 state, .i64 fluxL, .i64 fluxR]) env
  unfold func51
  wp_run [func51Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (update_core_exact env initial ratio state fluxL fluxR) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_run [func51Def, Project.EulerCellStep.Execution.updateValues, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp

#print axioms componentShift
#print axioms component_core_exact
#print axioms component_exact
#print axioms updateShift
#print axioms update_core_exact
#print axioms update_exact

end Project.EulerRiemann.Execution
