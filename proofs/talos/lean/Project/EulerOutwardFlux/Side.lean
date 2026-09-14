import Project.EulerOutwardFlux.Scalar
import Project.EulerRiemann.OutwardSide
import Project.Euler2DConservative.Execution

namespace Project.EulerOutwardFlux.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def sideValues (rho momentum transverse energy : UInt64) : List Wasm.Value :=
  let out := Project.EulerRiemann.OutwardNumerics.sideCheckedBits rho momentum transverse energy
  [.i64 out.energyFlux, .i64 out.transverseFlux, .i64 out.momentumFlux, .i64 out.massFlux,
    .i64 out.speed, .i64 out.pressure, .i64 out.velocity, .i64 out.status]

macro "outward_side_checked" call:term "condition" predicate:term "reject" rejection:term : tactic =>
  `(tactic|
    (refine wp_call_tw $call ?_
     rintro st values ⟨hst, hvalues⟩
     subst st
     subst values
     cases hcheck : $predicate
     case false =>
       side_fp_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       side_fp_peel
       simp_all +zetaDelta [sideValues, Project.EulerRiemann.OutwardNumerics.sideCheckedBits, Project.Euler2DConservative.Model.rejectedSide]
     all_goals side_fp_peel))

theorem side_exact
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 38 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = sideValues rho momentum transverse energy) := by
  let velocity := Wasm.IEEE64.div momentum rho
  let transport := Wasm.IEEE64.mul momentum velocity
  let transverseVelocity := Wasm.IEEE64.div transverse rho
  let transverseTransport := Wasm.IEEE64.mul transverse transverseVelocity
  let kineticSum := Wasm.IEEE64.add transport transverseTransport
  let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 kineticSum
  let internal := Wasm.IEEE64.sub energy halfKinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let speed := Project.EulerRiemann.OutwardSpeed.speedUpper rho momentum transverse energy
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let transverseFlux := Wasm.IEEE64.mul transverse velocity
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  have rejectCall := rejected_side_exact env initial
  have speedCall := speed_exact env initial rho momentum transverse energy
  change TerminatesWith env Project.EulerOutwardFlux.«module» 36 initial
    [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
    (fun final values => final = initial ∧ values = [.i64 speed.value, .i64 speed.status]) at speedCall
  refine TerminatesWith.of_wp_entry_for (f := func38Def)
    rfl ?_ (by decide)
  change wp Project.EulerOutwardFlux.«module» func38 _ initial (func38Def.toLocals [.i64 rho, .i64 momentum, .i64 transverse, .i64 energy]) env
  unfold func38
  wp_run [func38Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw speedCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  by_cases hs : speed.status = 0
  case neg =>
    side_fp_peel
    refine wp_call_tw rejectCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    side_fp_peel
    simp_all +zetaDelta [sideValues, Project.EulerRiemann.OutwardNumerics.sideCheckedBits,
      Project.Euler2DConservative.Model.rejectedSide]
  side_fp_peel
  outward_side_checked (side_finite_exact env initial velocity)
    condition (Project.Euler2DConservative.Model.finiteBits velocity) reject rejectCall
  outward_side_checked (side_finite_exact env initial transport)
    condition (Project.Euler2DConservative.Model.finiteBits transport) reject rejectCall
  outward_side_checked (side_finite_exact env initial transverseVelocity)
    condition (Project.Euler2DConservative.Model.finiteBits transverseVelocity) reject rejectCall
  outward_side_checked (side_finite_exact env initial transverseTransport)
    condition (Project.Euler2DConservative.Model.finiteBits transverseTransport) reject rejectCall
  outward_side_checked (side_finite_exact env initial kineticSum)
    condition (Project.Euler2DConservative.Model.finiteBits kineticSum) reject rejectCall
  outward_side_checked (side_finite_exact env initial halfKinetic)
    condition (Project.Euler2DConservative.Model.finiteBits halfKinetic) reject rejectCall
  outward_side_checked (side_positive_exact env initial internal)
    condition (Project.Euler2DConservative.Model.positiveBits internal) reject rejectCall
  outward_side_checked (side_positive_exact env initial pressure)
    condition (Project.Euler2DConservative.Model.positiveBits pressure) reject rejectCall
  outward_side_checked (side_finite_exact env initial momentumFlux)
    condition (Project.Euler2DConservative.Model.finiteBits momentumFlux) reject rejectCall
  outward_side_checked (side_finite_exact env initial transverseFlux)
    condition (Project.Euler2DConservative.Model.finiteBits transverseFlux) reject rejectCall
  outward_side_checked (side_finite_exact env initial enthalpy)
    condition (Project.Euler2DConservative.Model.finiteBits enthalpy) reject rejectCall
  outward_side_checked (side_finite_exact env initial energyFlux)
    condition (Project.Euler2DConservative.Model.finiteBits energyFlux) reject rejectCall
  simp_all +zetaDelta [sideValues, Project.EulerRiemann.OutwardNumerics.sideCheckedBits]

#print axioms side_exact
end Project.EulerOutwardFlux.Execution
