import Project.Euler2DCellStep.Spec
import Project.Euler2DCellStep.SweepModel

namespace Project.Euler2DCellStep.Sweep
open Wasm

noncomputable def CellSafe (out : Model.CheckedCell) : Prop :=
  Safety.StateSafety out.density out.momentum out.transverse out.energy out.pressure ∧
  (CodeLib.IEEE64.Finite out.courant ∧ 0 < CodeLib.IEEE64.value out.courant ∧
    CodeLib.IEEE64.value out.courant ≤ (1 : ℝ)/2) ∧
  Project.Euler2DConservative.Model.positiveBits out.alpha = true

theorem evaluate_safe (ratio : UInt64) (q : Inputs)
    (h : (evaluate ratio q).status = 0) : CellSafe (evaluate ratio q) :=
  ⟨Safety.accepted_state _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Safety.accepted_courant _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Safety.accepted_alpha _ _ _ _ _ _ _ _ _ _ _ _ _ h⟩

theorem nextGrid_safe {nx ny : Nat} (ratio : UInt64) (axis : Bool) (grid : Grid nx ny)
    (h : Accepted (outputs ratio axis grid)) : GridSafe (nextGrid axis (outputs ratio axis grid)) := by
  intro j i
  have hs := (evaluate_safe ratio (inputs axis grid j i) (h j i)).1
  exact orient_safe axis _ ⟨hs.bounds, hs.admissible⟩

def inputValues (ratio : UInt64) (q : Inputs) : List Value :=
  [.i64 q.right.energy, .i64 q.right.my, .i64 q.right.mx, .i64 q.right.density,
   .i64 q.center.energy, .i64 q.center.my, .i64 q.center.mx, .i64 q.center.density,
   .i64 q.left.energy, .i64 q.left.my, .i64 q.left.mx, .i64 q.left.density, .i64 ratio]

def outputValues (out : Model.CheckedCell) : List Value :=
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy,
   .i64 out.transverse, .i64 out.momentum, .i64 out.density, .i64 out.status]

noncomputable def Executes {nx ny : Nat} (m : Wasm.Module) (ratio : UInt64)
    (axis : Bool) (grid : Grid nx ny) : Prop :=
  ∀ j i (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 35 initial (inputValues ratio (inputs axis grid j i))
      (fun final values => final = initial ∧
        values = outputValues (outputs ratio axis grid j i) ∧
        CellSafe (outputs ratio axis grid j i))

theorem executes {m : Wasm.Module} (hSpec : Spec.SafeSpecFor m)
    {nx ny : Nat} (ratio : UInt64) (axis : Bool) (grid : Grid nx ny)
    (h : Accepted (outputs ratio axis grid)) : Executes m ratio axis grid := by
  intro j i env initial
  let q := inputs axis grid j i
  have hc := hSpec env initial ratio q.left.density q.left.mx q.left.my q.left.energy
    q.center.density q.center.mx q.center.my q.center.energy
    q.right.density q.right.mx q.right.my q.right.energy
  refine TerminatesWith.mono hc ?_
  rintro final values ⟨hs, hv, _⟩
  exact ⟨hs, hv, evaluate_safe ratio q (h j i)⟩

#print axioms orient_safe
#print axioms evaluate_safe
#print axioms nextGrid_safe
#print axioms executes
end Project.Euler2DCellStep.Sweep
