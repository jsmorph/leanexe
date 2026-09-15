import Project.EulerOutwardFaceStep.Scalar
import Project.EulerRiemann.OutwardAdvance

namespace Project.EulerOutwardFaceStep.Execution
open Wasm
open Project.Euler2DDynamicFlux.Model (CheckedFlux)
open Project.Euler2DCellStep.Model (CheckedCell updateCheckedBits)
open Project.EulerRiemann.OutwardNumerics (advanceCheckedBits sideCheckedBits)
open Project.Euler2DConservative.Model (positiveBits)

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def cellValues (out : CheckedCell) : List Value :=
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy,
   .i64 out.transverse, .i64 out.momentum, .i64 out.density, .i64 out.status]

def advanceArguments (ratio rho mx my energy : UInt64) (left right : CheckedFlux) : List Value :=
  [.i64 right.alpha, .i64 right.energy, .i64 right.transverse, .i64 right.momentum,
   .i64 right.mass, .i64 right.status, .i64 left.alpha, .i64 left.energy,
   .i64 left.transverse, .i64 left.momentum, .i64 left.mass, .i64 left.status,
   .i64 energy, .i64 my, .i64 mx, .i64 rho, .i64 ratio]

macro "advance_guard" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (by_cases hcheck : $checkCond
     case neg =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, rfl⟩
       subst st
       dynamic_peel
       simp_all +zetaDelta [cellValues, advanceCheckedBits,
         Project.Euler2DCellStep.Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

macro "advance_bool" checkedCall:term "when" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (refine wp_call_tw $checkedCall ?_
     rintro st values ⟨hst, rfl⟩
     subst st
     cases hcheck : $checkCond
     case false =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, rfl⟩
       subst st
       dynamic_peel
       simp_all +zetaDelta [cellValues, advanceCheckedBits,
         Project.Euler2DCellStep.Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

theorem advance_exact (env : HostEnv Unit) (initial : Store Unit)
    (ratio rho mx my energy : UInt64) (left right : CheckedFlux) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 69 initial
      (advanceArguments ratio rho mx my energy left right)
      (fun final values => final = initial ∧
        values = cellValues (advanceCheckedBits ratio rho mx my energy left right)) := by
  have rejectCall := rejectedCell_exact env initial
  unfold advanceArguments
  refine TerminatesWith.of_wp_entry_for (f := func69Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardFaceStep.«module» func69 _ initial
    (func69Def.toLocals [.i64 ratio, .i64 rho, .i64 mx, .i64 my, .i64 energy,
      .i64 left.status, .i64 left.mass, .i64 left.momentum, .i64 left.transverse,
      .i64 left.energy, .i64 left.alpha, .i64 right.status, .i64 right.mass,
      .i64 right.momentum, .i64 right.transverse, .i64 right.energy, .i64 right.alpha]) env
  unfold func69
  wp_run [func69Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  advance_bool (positive_exact env initial ratio) when (positiveBits ratio) reject rejectCall
  advance_guard (left.status = 0) reject rejectCall
  advance_guard (right.status = 0) reject rejectCall
  let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
  by_cases hspeed : left.alpha ≤ right.alpha
  all_goals
    dynamic_peel
    have alphaCall := positive_exact env initial alpha
    simp only [alpha, hspeed, ite_true, ite_false] at alphaCall
    refine wp_call_tw alphaCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases hpositive : positiveBits alpha
    all_goals simp only [alpha, hspeed, ite_true, ite_false] at hpositive
    case false =>
      dynamic_peel
      refine wp_call_tw rejectCall ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      dynamic_peel
      simp_all +zetaDelta [cellValues, advanceCheckedBits,
        Project.Euler2DCellStep.Model.rejectedCell, -UInt64.not_le]
    all_goals dynamic_peel
    let courant := Project.ProofKit.F64Outward.mul true ratio alpha
    have courantCall := mul_exact env initial true ratio alpha
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 25 initial
      [.i64 alpha, .i64 ratio, .i64 1]
      (fun final values => final = initial ∧ values = [.i64 courant.value, .i64 courant.status]) at courantCall
    simp only [alpha, hspeed, ite_true, ite_false] at courantCall
    refine wp_call_tw courantCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    advance_guard (courant.status = 0) reject rejectCall
    advance_guard (courant.value ≤ 0x3FE0000000000000) reject rejectCall
    let density := updateCheckedBits ratio rho left.mass right.mass
    have densityCall := update_exact env initial ratio rho left.mass right.mass
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 62 initial
      [.i64 right.mass, .i64 left.mass, .i64 rho, .i64 ratio]
      (fun final values => final = initial ∧ values = [.i64 density.value, .i64 density.status]) at densityCall
    refine wp_call_tw densityCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    let momentum := updateCheckedBits ratio mx left.momentum right.momentum
    have momentumCall := update_exact env initial ratio mx left.momentum right.momentum
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 62 initial
      [.i64 right.momentum, .i64 left.momentum, .i64 mx, .i64 ratio]
      (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
    refine wp_call_tw momentumCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    let transverse := updateCheckedBits ratio my left.transverse right.transverse
    have transverseCall := update_exact env initial ratio my left.transverse right.transverse
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 62 initial
      [.i64 right.transverse, .i64 left.transverse, .i64 my, .i64 ratio]
      (fun final values => final = initial ∧ values = [.i64 transverse.value, .i64 transverse.status]) at transverseCall
    refine wp_call_tw transverseCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
    have energyCall := update_exact env initial ratio energy left.energy right.energy
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 62 initial
      [.i64 right.energy, .i64 left.energy, .i64 energy, .i64 ratio]
      (fun final values => final = initial ∧ values = [.i64 nextEnergy.value, .i64 nextEnergy.status]) at energyCall
    refine wp_call_tw energyCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    advance_guard (density.status = 0) reject rejectCall
    advance_guard (momentum.status = 0) reject rejectCall
    advance_guard (transverse.status = 0) reject rejectCall
    advance_guard (nextEnergy.status = 0) reject rejectCall
    let side := sideCheckedBits density.value momentum.value transverse.value nextEnergy.value
    have sideCall := side_exact env initial density.value momentum.value transverse.value nextEnergy.value
    change TerminatesWith env Project.EulerOutwardFaceStep.«module» 38 initial
      [.i64 nextEnergy.value, .i64 transverse.value, .i64 momentum.value, .i64 density.value]
      (fun final values => final = initial ∧ values =
        [.i64 side.energyFlux, .i64 side.transverseFlux, .i64 side.momentumFlux, .i64 side.massFlux,
         .i64 side.speed, .i64 side.pressure, .i64 side.velocity, .i64 side.status]) at sideCall
    refine wp_call_tw sideCall ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    advance_guard (side.status = 0) reject rejectCall
    simp_all +zetaDelta [cellValues, advanceCheckedBits, -UInt64.not_le]

#print axioms advance_exact
end Project.EulerOutwardFaceStep.Execution
