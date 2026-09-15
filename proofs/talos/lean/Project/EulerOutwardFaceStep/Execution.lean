import Project.EulerOutwardFaceStep.Advance
import Project.EulerRiemann.OutwardFaceStep

namespace Project.EulerOutwardFaceStep.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.OutwardNumerics

set_option maxRecDepth 32768

def arguments (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) : List Value :=
  [.i64 rightOuter.energy, .i64 rightOuter.my, .i64 rightOuter.mx, .i64 rightOuter.density,
   .i64 rightInner.energy, .i64 rightInner.my, .i64 rightInner.mx, .i64 rightInner.density,
   .i64 leftInner.energy, .i64 leftInner.my, .i64 leftInner.mx, .i64 leftInner.density,
   .i64 leftOuter.energy, .i64 leftOuter.my, .i64 leftOuter.mx, .i64 leftOuter.density,
   .i64 center.energy, .i64 center.my, .i64 center.mx, .i64 center.density, .i64 ratio]

theorem face_step_exact (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 70 initial
      (arguments ratio center leftOuter leftInner rightInner rightOuter)
      (fun final values => final = initial ∧
        values = cellValues (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter)) := by
  have leftCall := flux_exact env initial
    leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy
  have rightCall := flux_exact env initial
    rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy
  dsimp only [Project.EulerOutwardFlux.Execution.fluxValues] at leftCall rightCall
  unfold arguments
  refine TerminatesWith.of_wp_entry_for (f := func70Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardFaceStep.«module» func70 _ initial
    (func70Def.toLocals [.i64 ratio, .i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
      .i64 leftOuter.density, .i64 leftOuter.mx, .i64 leftOuter.my, .i64 leftOuter.energy,
      .i64 leftInner.density, .i64 leftInner.mx, .i64 leftInner.my, .i64 leftInner.energy,
      .i64 rightInner.density, .i64 rightInner.mx, .i64 rightInner.my, .i64 rightInner.energy,
      .i64 rightOuter.density, .i64 rightOuter.mx, .i64 rightOuter.my, .i64 rightOuter.energy]) env
  unfold func70
  wp_run [func70Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw leftCall ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  dynamic_peel
  refine wp_call_tw rightCall ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  dynamic_peel
  refine wp_call_tw (advance_exact env initial ratio center.density center.mx center.my center.energy _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  dsimp only [cellValues]
  dynamic_peel
  simp [faceStepCheckedBits]

#print axioms face_step_exact
end Project.EulerOutwardFaceStep.Execution
