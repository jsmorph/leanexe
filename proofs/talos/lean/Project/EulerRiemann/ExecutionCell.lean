import Project.EulerRiemann.ExecutionFlux
import Project.Euler2DCellStep.Execution

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def cellStepValues (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) : List Wasm.Value :=
  let out := Numerics.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy, .i64 out.transverse, .i64 out.momentum, .i64 out.density, .i64 out.status]

macro "riemann_cell_guard" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (by_cases hcheck : $checkCond
     case neg =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       dynamic_peel
       simp_all +zetaDelta [cellStepValues, Numerics.cellCheckedBits, Project.Euler2DCellStep.Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

macro "riemann_cell_bool" checkedCall:term "when" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (refine wp_call_tw $checkedCall ?_
     rintro st values ⟨hst, hvalues⟩
     subst st
     subst values
     cases hcheck : $checkCond
     case false =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       dynamic_peel
       simp_all +zetaDelta [cellStepValues, Numerics.cellCheckedBits, Project.Euler2DCellStep.Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

theorem positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 2 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.EulerConservative.Execution.boolWord
          (Project.Euler2DConservative.Model.positiveBits word))]) :=
  side_positive_exact env initial word

theorem rejectedCell_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 64 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func64Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func64 _ initial (func64Def.toLocals []) env
  unfold func64
  wp_run
  simp [func64Def, List.set]

theorem cell_exact
    (env : HostEnv Unit) (initial : Store Unit) (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 65 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 transverse, .i64 momentum, .i64 rho, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL, .i64 ratio]
      (fun final values => final = initial ∧ values = cellStepValues ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR) := by
  let left := Numerics.fluxCheckedBits rhoL momentumL transverseL energyL rho momentum transverse energy
  have leftCall := flux_exact env initial rhoL momentumL transverseL energyL rho momentum transverse energy
  change TerminatesWith env Project.EulerRiemann.«module» 54 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.alpha, .i64 left.energy, .i64 left.transverse, .i64 left.momentum, .i64 left.mass, .i64 left.status]) at leftCall
  let right := Numerics.fluxCheckedBits rho momentum transverse energy rhoR momentumR transverseR energyR
  have rightCall := flux_exact env initial rho momentum transverse energy rhoR momentumR transverseR energyR
  change TerminatesWith env Project.EulerRiemann.«module» 54 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
    (fun final values => final = initial ∧ values = [.i64 right.alpha, .i64 right.energy, .i64 right.transverse, .i64 right.momentum, .i64 right.mass, .i64 right.status]) at rightCall
  let nextDensity := Project.Euler2DCellStep.Model.updateCheckedBits ratio rho left.mass right.mass
  have nextDensityCall := update_exact env initial ratio rho left.mass right.mass
  change TerminatesWith env Project.EulerRiemann.«module» 58 initial [.i64 right.mass, .i64 left.mass, .i64 rho, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextDensity.value, .i64 nextDensity.status]) at nextDensityCall
  let nextMomentum := Project.Euler2DCellStep.Model.updateCheckedBits ratio momentum left.momentum right.momentum
  have nextMomentumCall := update_exact env initial ratio momentum left.momentum right.momentum
  change TerminatesWith env Project.EulerRiemann.«module» 58 initial [.i64 right.momentum, .i64 left.momentum, .i64 momentum, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextMomentum.value, .i64 nextMomentum.status]) at nextMomentumCall
  let nextTransverse := Project.Euler2DCellStep.Model.updateCheckedBits ratio transverse left.transverse right.transverse
  have nextTransverseCall := update_exact env initial ratio transverse left.transverse right.transverse
  change TerminatesWith env Project.EulerRiemann.«module» 58 initial [.i64 right.transverse, .i64 left.transverse, .i64 transverse, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextTransverse.value, .i64 nextTransverse.status]) at nextTransverseCall
  let nextEnergy := Project.Euler2DCellStep.Model.updateCheckedBits ratio energy left.energy right.energy
  have nextEnergyCall := update_exact env initial ratio energy left.energy right.energy
  change TerminatesWith env Project.EulerRiemann.«module» 58 initial [.i64 right.energy, .i64 left.energy, .i64 energy, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextEnergy.value, .i64 nextEnergy.status]) at nextEnergyCall
  let nextSide := Numerics.sideCheckedBits nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
  have nextSideCall := side_exact env initial nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
  change TerminatesWith env Project.EulerRiemann.«module» 22 initial [.i64 nextEnergy.value, .i64 nextTransverse.value, .i64 nextMomentum.value, .i64 nextDensity.value]
    (fun final values => final = initial ∧ values = [.i64 nextSide.energyFlux, .i64 nextSide.transverseFlux, .i64 nextSide.momentumFlux, .i64 nextSide.massFlux, .i64 nextSide.speed, .i64 nextSide.pressure, .i64 nextSide.velocity, .i64 nextSide.status]) at nextSideCall
  refine TerminatesWith.of_wp_entry_for (f := func65Def)
    rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func65 _ initial (func65Def.toLocals [.i64 ratio, .i64 rhoL, .i64 momentumL, .i64 transverseL, .i64 energyL, .i64 rho, .i64 momentum, .i64 transverse, .i64 energy, .i64 rhoR, .i64 momentumR, .i64 transverseR, .i64 energyR]) env
  unfold func65
  wp_run [func65Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  riemann_cell_bool (positive_exact env initial ratio)
    when (Project.Euler2DConservative.Model.positiveBits ratio) reject (rejectedCell_exact env initial)
  refine wp_call_tw leftCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  riemann_cell_guard (left.status = 0) reject (rejectedCell_exact env initial)
  refine wp_call_tw rightCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  riemann_cell_guard (right.status = 0) reject (rejectedCell_exact env initial)
  by_cases hspeed : left.alpha ≤ right.alpha
  · dynamic_peel
    let courant := Wasm.IEEE64.mul ratio right.alpha
    riemann_cell_bool (positive_exact env initial courant)
      when (Project.Euler2DConservative.Model.positiveBits courant) reject (rejectedCell_exact env initial)
    riemann_cell_guard (Wasm.IEEE64.mul ratio right.alpha ≤ 0x3FE0000000000000) reject (rejectedCell_exact env initial)
    refine wp_call_tw nextDensityCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextMomentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextTransverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextEnergyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    riemann_cell_guard (nextDensity.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextMomentum.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextTransverse.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextEnergy.status = 0) reject (rejectedCell_exact env initial)
    refine wp_call_tw nextSideCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    riemann_cell_guard (nextSide.status = 0) reject (rejectedCell_exact env initial)
    simp_all +zetaDelta [cellStepValues, Numerics.cellCheckedBits, -UInt64.not_le]
  · dynamic_peel
    let courant := Wasm.IEEE64.mul ratio left.alpha
    riemann_cell_bool (positive_exact env initial courant)
      when (Project.Euler2DConservative.Model.positiveBits courant) reject (rejectedCell_exact env initial)
    riemann_cell_guard (Wasm.IEEE64.mul ratio left.alpha ≤ 0x3FE0000000000000) reject (rejectedCell_exact env initial)
    refine wp_call_tw nextDensityCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextMomentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextTransverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextEnergyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    riemann_cell_guard (nextDensity.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextMomentum.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextTransverse.status = 0) reject (rejectedCell_exact env initial)
    riemann_cell_guard (nextEnergy.status = 0) reject (rejectedCell_exact env initial)
    refine wp_call_tw nextSideCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    riemann_cell_guard (nextSide.status = 0) reject (rejectedCell_exact env initial)
    simp_all +zetaDelta [cellStepValues, Numerics.cellCheckedBits, -UInt64.not_le]


#print axioms positive_exact
#print axioms rejectedCell_exact
#print axioms cell_exact

end Project.EulerRiemann.Execution
