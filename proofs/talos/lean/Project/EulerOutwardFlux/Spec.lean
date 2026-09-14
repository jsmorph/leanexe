import Project.EulerOutwardFlux.Execution
import Project.EulerOutwardFlux.AnnotationMatches
import Project.EulerRiemann.OutwardFluxResidual

namespace Project.EulerOutwardFlux.Spec
open Wasm CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DDynamicFlux.Model (CheckedFlux rejectedFlux)
open Project.Euler2DConservative.Guard (decodedState)
open Project.EulerRiemann
open Project.EulerRiemann.Numerics (fluxWords)
open Project.EulerRiemann.OutwardMaximum (Bounds)

def arguments (left right : State) : List Value :=
  [.i64 right.energy, .i64 right.my, .i64 right.mx, .i64 right.density,
   .i64 left.energy, .i64 left.my, .i64 left.mx, .i64 left.density]

def results (flux : CheckedFlux) : List Value :=
  [.i64 flux.alpha, .i64 flux.energy, .i64 flux.transverse, .i64 flux.momentum,
   .i64 flux.mass, .i64 flux.status]

def computedFlux (left right : State) : CheckedFlux :=
  OutwardNumerics.fluxCheckedBits left.density left.mx left.my left.energy
    right.density right.mx right.my right.energy

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : State),
    TerminatesWith env m 54 initial (arguments left right)
      (fun final values => final = initial ∧ values = results (computedFlux left right))

def Behavior (left right : State) (values : List Value) : Prop :=
  values = results rejectedFlux ∨
    ∃ flux : CheckedFlux, values = results flux ∧ flux.status = 0 ∧
      Finite flux.alpha ∧ 0 < value flux.alpha ∧
      Bounds left flux.alpha ∧ Bounds right flux.alpha ∧
      ∀ i : Fin 4, Finite (fluxWords flux i)

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : State),
    TerminatesWith env m 54 initial (arguments left right)
      (fun final values => final = initial ∧ Behavior left right values)

def Residual (left right : State) (flux : CheckedFlux) : Prop :=
  flux.status = 0 → ∀ i : Fin 4,
    |value (fluxWords flux i) - RealRusanov.interfaceFlux (value flux.alpha)
      (decodedState left.density left.mx left.my left.energy)
      (decodedState right.density right.mx right.my right.energy) i| ≤
      OutwardNumerics.interfaceErrorBounds left.density left.mx left.my left.energy
        right.density right.mx right.my right.energy i

def ResidualSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : State),
    TerminatesWith env m 54 initial (arguments left right)
      (fun final values => final = initial ∧
        ∃ flux : CheckedFlux, values = results flux ∧ Residual left right flux)

theorem fluxCheckedBits_exact : ExactSpecFor module := by
  intro env initial left right
  exact Execution.flux_exact env initial left.density left.mx left.my left.energy
    right.density right.mx right.my right.energy

theorem fluxCheckedBits_behavior : BehaviorSpecFor module := by
  intro env initial left right
  refine TerminatesWith.mono (fluxCheckedBits_exact env initial left right) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases OutwardNumerics.flux_behavior left.density left.mx left.my left.energy
      right.density right.mx right.my right.energy with hr | hs
  · exact Or.inl (congrArg results hr)
  · exact Or.inr ⟨computedFlux left right, rfl, hs⟩

theorem fluxCheckedBits_residual : ResidualSpecFor module := by
  intro env initial left right
  refine TerminatesWith.mono (fluxCheckedBits_exact env initial left right) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, computedFlux left right, rfl, ?_⟩
  intro h i
  exact OutwardNumerics.accepted_interface_reference_bound left.density left.mx left.my left.energy
    right.density right.mx right.my right.energy h i

#print axioms fluxCheckedBits_exact
#print axioms fluxCheckedBits_behavior
#print axioms fluxCheckedBits_residual
end Project.EulerOutwardFlux.Spec
