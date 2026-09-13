import Project.EulerRiemann.NumericsSafety
import Project.Euler2DCellStep.SweepModel

namespace Project.EulerRiemann.Numerics
open Project.Euler2DCellStep.Sweep

def evaluate (ratio : UInt64) (q : Inputs) : Project.Euler2DCellStep.Model.CheckedCell :=
  cellCheckedBits ratio q.left.density q.left.mx q.left.my q.left.energy
    q.center.density q.center.mx q.center.my q.center.energy
    q.right.density q.right.mx q.right.my q.right.energy

def outputs {nx ny : Nat} (ratio : UInt64) (axis : Bool) (grid : Grid nx ny) : Outputs nx ny :=
  fun j i => evaluate ratio (inputs axis grid j i)

def step {nx ny : Nat} (ratio : UInt64) (grid : Grid nx ny) : Option (Grid nx ny) :=
  let x := outputs ratio false grid
  if Accepted x then
    let middle := nextGrid false x
    let y := outputs ratio true middle
    if Accepted y then some (nextGrid true y) else none
  else none

theorem evaluate_state (ratio : UInt64) (q : Inputs)
    (h : (evaluate ratio q).status = 0) :
    let out := evaluate ratio q
    Project.Euler2DCellStep.Safety.StateSafety out.density out.momentum out.transverse
      out.energy out.pressure :=
  cell_state _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem nextGrid_safe {nx ny : Nat} (ratio : UInt64) (axis : Bool) (grid : Grid nx ny)
    (h : Accepted (outputs ratio axis grid)) : GridSafe (nextGrid axis (outputs ratio axis grid)) := by
  intro j i
  have hs := evaluate_state ratio (inputs axis grid j i) (h j i)
  exact orient_safe axis _ ⟨hs.bounds, hs.admissible⟩

#print axioms evaluate_state
#print axioms nextGrid_safe
end Project.EulerRiemann.Numerics
