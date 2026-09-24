import Project.EulerRiemann.FrozenExecutionGuard
import Project.Euler2DConservative.Execution

namespace Project.EulerRiemann.Frozen.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def sideValues (rho momentum transverse energy : UInt64) : List Wasm.Value :=
  let out := Numerics.sideCheckedBits rho momentum transverse energy
  [.i64 out.energyFlux, .i64 out.transverseFlux, .i64 out.momentumFlux, .i64 out.massFlux,
    .i64 out.speed, .i64 out.pressure, .i64 out.velocity, .i64 out.status]

macro "riemann_side_checked" call:term "condition" predicate:term "reject" rejection:term : tactic =>
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
       simp_all +zetaDelta [sideValues, Numerics.sideCheckedBits, Project.Euler2DConservative.Model.rejectedSide]
     all_goals side_fp_peel))

theorem side_exact
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 22 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = sideValues rho momentum transverse energy) := by
  let velocity := Wasm.IEEE64.div momentum rho
  let transport := Wasm.IEEE64.mul momentum velocity
  let transverseVelocity := Wasm.IEEE64.div transverse rho
  let transverseTransport := Wasm.IEEE64.mul transverse transverseVelocity
  let kineticSum := Wasm.IEEE64.add transport transverseTransport
  let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 kineticSum
  let internal := Wasm.IEEE64.sub energy halfKinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let pressureOverDensity := Wasm.IEEE64.div pressure rho
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 pressureOverDensity
  let soundSpeed := Wasm.IEEE64.sqrt radicand
  let speed := Wasm.IEEE64.add (Project.Euler2DConservative.Model.absBits velocity) soundSpeed
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let transverseFlux := Wasm.IEEE64.mul transverse velocity
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  have rejectCall := rejected_side_exact env initial
  refine TerminatesWith.of_wp_entry_for (f := func22Def)
    rfl ?_ (by decide)
  change wp Project.EulerRiemann.Frozen.«module» func22 _ initial (func22Def.toLocals [.i64 rho, .i64 momentum, .i64 transverse, .i64 energy]) env
  unfold func22
  wp_run [func22Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  riemann_side_checked (state_guard_exact env initial rho momentum transverse energy)
    condition (Numerics.stateGuard rho momentum transverse energy) reject rejectCall
  riemann_side_checked (side_finite_exact env initial velocity)
    condition (Project.Euler2DConservative.Model.finiteBits velocity) reject rejectCall
  riemann_side_checked (side_finite_exact env initial transport)
    condition (Project.Euler2DConservative.Model.finiteBits transport) reject rejectCall
  riemann_side_checked (side_finite_exact env initial transverseVelocity)
    condition (Project.Euler2DConservative.Model.finiteBits transverseVelocity) reject rejectCall
  riemann_side_checked (side_finite_exact env initial transverseTransport)
    condition (Project.Euler2DConservative.Model.finiteBits transverseTransport) reject rejectCall
  riemann_side_checked (side_finite_exact env initial kineticSum)
    condition (Project.Euler2DConservative.Model.finiteBits kineticSum) reject rejectCall
  riemann_side_checked (side_finite_exact env initial halfKinetic)
    condition (Project.Euler2DConservative.Model.finiteBits halfKinetic) reject rejectCall
  riemann_side_checked (side_positive_exact env initial internal)
    condition (Project.Euler2DConservative.Model.positiveBits internal) reject rejectCall
  riemann_side_checked (side_positive_exact env initial pressure)
    condition (Project.Euler2DConservative.Model.positiveBits pressure) reject rejectCall
  riemann_side_checked (side_positive_exact env initial pressureOverDensity)
    condition (Project.Euler2DConservative.Model.positiveBits pressureOverDensity) reject rejectCall
  riemann_side_checked (side_positive_exact env initial radicand)
    condition (Project.Euler2DConservative.Model.positiveBits radicand) reject rejectCall
  refine wp_call_tw (side_abs_exact env initial velocity) ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  side_fp_peel
  riemann_side_checked (side_positive_exact env initial soundSpeed)
    condition (Project.Euler2DConservative.Model.positiveBits soundSpeed) reject rejectCall
  riemann_side_checked (side_positive_exact env initial speed)
    condition (Project.Euler2DConservative.Model.positiveBits speed) reject rejectCall
  riemann_side_checked (side_finite_exact env initial momentumFlux)
    condition (Project.Euler2DConservative.Model.finiteBits momentumFlux) reject rejectCall
  riemann_side_checked (side_finite_exact env initial transverseFlux)
    condition (Project.Euler2DConservative.Model.finiteBits transverseFlux) reject rejectCall
  riemann_side_checked (side_finite_exact env initial enthalpy)
    condition (Project.Euler2DConservative.Model.finiteBits enthalpy) reject rejectCall
  riemann_side_checked (side_finite_exact env initial energyFlux)
    condition (Project.Euler2DConservative.Model.finiteBits energyFlux) reject rejectCall
  simp_all +zetaDelta [sideValues, Numerics.sideCheckedBits]

#print axioms side_exact
end Project.EulerRiemann.Frozen.Execution
