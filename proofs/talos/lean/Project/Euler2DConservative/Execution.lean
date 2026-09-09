import Project.Euler2DConservative.StateGuard
import Project.EulerConservative.Execution

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (rho momentum transverse energy : UInt64) : List Wasm.Value :=
  let out := Model.sideCheckedBits rho momentum transverse energy
  [.i64 out.energyFlux, .i64 out.transverseFlux, .i64 out.momentumFlux, .i64 out.massFlux,
    .i64 out.speed, .i64 out.pressure, .i64 out.velocity, .i64 out.status]

/-- Discharge the rejected continuation once; keep the accepted guard for the next call. -/
macro "side_checked" call:term "condition" condition:term "reject" rejection:term : tactic =>
  `(tactic|
    (refine wp_call_tw $call ?_
     rintro st values ⟨hst, hvalues⟩
     subst st
     subst values
     cases hcheck : $condition
     case false =>
       side_fp_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       side_fp_peel
       simp_all +zetaDelta [resultValues, Model.sideCheckedBits, Model.rejectedSide]
     all_goals side_fp_peel))

theorem sideCheckedBits_exact_in_module {m : Wasm.Module}
    (layout : HelperLayout m) (hside : m.funcs[5]? = some func5Def)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64) :
    TerminatesWith env m 5 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum transverse energy) := by
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
  let speed := Wasm.IEEE64.add (Model.absBits velocity) soundSpeed
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let transverseFlux := Wasm.IEEE64.mul transverse velocity
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  have rejectCall := rejectedSide_exact layout env initial
  refine TerminatesWith.of_wp_entry_for (f := func5Def)
    (by simpa [layout.noImports] using hside) ?_ (by simp [layout.noImports])
  change wp m func5 _ initial (func5Def.toLocals [.i64 rho, .i64 momentum, .i64 transverse, .i64 energy]) env
  unfold func5
  wp_run [func5Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  side_checked (stateGuard_exact layout env initial rho momentum transverse energy)
    condition (Model.stateGuard rho momentum transverse energy) reject rejectCall
  side_checked (finiteBits_exact layout env initial velocity)
    condition (Model.finiteBits velocity) reject rejectCall
  side_checked (finiteBits_exact layout env initial transport)
    condition (Model.finiteBits transport) reject rejectCall
  side_checked (finiteBits_exact layout env initial transverseVelocity)
    condition (Model.finiteBits transverseVelocity) reject rejectCall
  side_checked (finiteBits_exact layout env initial transverseTransport)
    condition (Model.finiteBits transverseTransport) reject rejectCall
  side_checked (finiteBits_exact layout env initial kineticSum)
    condition (Model.finiteBits kineticSum) reject rejectCall
  side_checked (finiteBits_exact layout env initial halfKinetic)
    condition (Model.finiteBits halfKinetic) reject rejectCall
  side_checked (positiveBits_exact layout env initial internal)
    condition (Model.positiveBits internal) reject rejectCall
  side_checked (positiveBits_exact layout env initial pressure)
    condition (Model.positiveBits pressure) reject rejectCall
  side_checked (positiveBits_exact layout env initial pressureOverDensity)
    condition (Model.positiveBits pressureOverDensity) reject rejectCall
  side_checked (positiveBits_exact layout env initial radicand)
    condition (Model.positiveBits radicand) reject rejectCall
  refine wp_call_tw (absBits_exact layout env initial velocity) ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  side_fp_peel
  side_checked (positiveBits_exact layout env initial soundSpeed)
    condition (Model.positiveBits soundSpeed) reject rejectCall
  side_checked (positiveBits_exact layout env initial speed)
    condition (Model.positiveBits speed) reject rejectCall
  side_checked (finiteBits_exact layout env initial momentumFlux)
    condition (Model.finiteBits momentumFlux) reject rejectCall
  side_checked (finiteBits_exact layout env initial transverseFlux)
    condition (Model.finiteBits transverseFlux) reject rejectCall
  side_checked (finiteBits_exact layout env initial enthalpy)
    condition (Model.finiteBits enthalpy) reject rejectCall
  side_checked (finiteBits_exact layout env initial energyFlux)
    condition (Model.finiteBits energyFlux) reject rejectCall
  simp_all +zetaDelta [resultValues, Model.sideCheckedBits]

#print axioms sideCheckedBits_exact_in_module
end Project.Euler2DConservative.Execution
