import Project.EulerCertificateFlux.Interface
import Project.EulerCertificate.FluxSpec

namespace Project.EulerCertificateFlux.Spec
open Wasm
open Project.ProofKit.F64Interval
open Project.EulerCertificate.Flux
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)
open Project.EulerRiemann

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (alpha : UInt64) (left right : State),
    TerminatesWith env m 35 initial
      [.i64 right.energy, .i64 right.my, .i64 right.mx, .i64 right.density,
        .i64 left.energy, .i64 left.my, .i64 left.mx, .i64 left.density, .i64 alpha]
      (fun final values => final = initial ∧
        values = Execution.vectorValues (interface alpha left right))

def Enclosure (alpha : UInt64) (left right : State) (values : List Value) : Prop :=
  ∃ result : Project.EulerCertificate.Flux.Vector,
    values = Execution.vectorValues result ∧
      ∀ i : Fin 4, Valid (get result i)
        (RealRusanov.interfaceFlux (CodeLib.IEEE64.value alpha)
          (decodedState left.density left.mx left.my left.energy)
          (decodedState right.density right.mx right.my right.energy) i)

def EnclosureSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (alpha : UInt64) (left right : State),
    TerminatesWith env m 35 initial
      [.i64 right.energy, .i64 right.my, .i64 right.mx, .i64 right.density,
        .i64 left.energy, .i64 left.my, .i64 left.mx, .i64 left.density, .i64 alpha]
      (fun final values => final = initial ∧ Enclosure alpha left right values)

theorem interface_exact : ExactSpecFor «module» := Execution.interface_exact

theorem interface_enclosure : EnclosureSpecFor «module» := by
  intro env initial alpha left right
  refine TerminatesWith.mono (interface_exact env initial alpha left right) ?_
  rintro final values ⟨hfinal, rfl⟩
  exact ⟨hfinal, interface alpha left right, rfl, interface_valid alpha left right⟩

#print axioms interface_exact
#print axioms interface_enclosure
end Project.EulerCertificateFlux.Spec
