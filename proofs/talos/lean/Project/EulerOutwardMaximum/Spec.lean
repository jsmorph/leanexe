import Project.EulerOutwardMaximum.Merge
import Project.EulerOutwardMaximum.AnnotationMatches
import Project.EulerRiemann.OutwardMaximumBounds

namespace Project.EulerOutwardMaximum.Spec
open Wasm CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Order (positiveBits)
open Project.ProofKit.F64Outward (rejected)
open Project.EulerRiemann.OutwardMaximum

def arguments (left right : State) : List Value :=
  [.i64 right.energy, .i64 right.my, .i64 right.mx, .i64 right.density,
   .i64 left.energy, .i64 left.my, .i64 left.mx, .i64 left.density]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : State),
    TerminatesWith env m 42 initial (arguments left right)
      (fun final values => final = initial ∧ values = checkedValues (interfaceUpper left right))

def Behavior (left right : State) (values : List Value) : Prop :=
  values = [.i64 0, .i64 1] ∨
    ∃ alpha : UInt64, values = [.i64 alpha, .i64 0] ∧
      Finite alpha ∧ positiveBits alpha = true ∧ Bounds left alpha ∧ Bounds right alpha

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : State),
    TerminatesWith env m 42 initial (arguments left right)
      (fun final values => final = initial ∧ Behavior left right values)

theorem interfaceUpper_exact : ExactSpecFor module := by
  intro env initial left right
  unfold arguments
  refine TerminatesWith.of_wp_entry_for (f := func42Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardMaximum.«module» func42 _ initial
    (func42Def.toLocals [.i64 left.density, .i64 left.mx, .i64 left.my, .i64 left.energy,
      .i64 right.density, .i64 right.mx, .i64 right.my, .i64 right.energy]) env
  unfold func42
  wp_run [func42Def]
  outward_call (Execution.speed_exact env initial left.density left.mx left.my left.energy)
  outward_call (Execution.speed_exact env initial right.density right.mx right.my right.energy)
  outward_call (Execution.merge_exact env initial
    (Project.EulerRiemann.OutwardSpeed.speedUpper left.density left.mx left.my left.energy)
    (Project.EulerRiemann.OutwardSpeed.speedUpper right.density right.mx right.my right.energy))
  simp [interfaceUpper, checkedValues]

theorem interfaceUpper_behavior : BehaviorSpecFor module := by
  intro env initial left right
  refine TerminatesWith.mono (interfaceUpper_exact env initial left right) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases interface_behavior left right with hr | hs
  · exact Or.inl (by simp [hr, checkedValues, rejected])
  · exact Or.inr ⟨(interfaceUpper left right).value,
      by simp [checkedValues, hs.1], hs.2.1,
      (interface_bounds left right hs.1).1, hs.2.2⟩

#print axioms interfaceUpper_exact
#print axioms interfaceUpper_behavior
end Project.EulerOutwardMaximum.Spec
