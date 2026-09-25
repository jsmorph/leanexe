import Project.EulerReconstructed.FrozenTraversalSafety
import Project.EulerRiemann.FrozenOutwardFaceRowBalance

namespace Project.EulerReconstructed.Frozen.Numerics
open Project.Euler2DCellStep.Sweep
open Project.Euler2DCellStep.Model (CheckedCell)
open Project.EulerRiemann.Frozen.OutwardNumerics
open Traversal (Stencil)

def inputs {n : Nat} (axis : Bool) (grid : Grid n n) (j i : Fin n) : Stencil :=
  if axis then
    ⟨orient axis (grid (previous (previous j)) i), orient axis (grid (previous j) i),
      orient axis (grid j i), orient axis (grid (following j) i),
      orient axis (grid (following (following j)) i)⟩
  else
    ⟨orient axis (grid j (previous (previous i))), orient axis (grid j (previous i)),
      orient axis (grid j i), orient axis (grid j (following i)),
      orient axis (grid j (following (following i)))⟩

def evaluate (fuel : Nat) (ratio : UInt64) (input : Stencil) : CheckedCell :=
  reconstructedStepCheckedBits fuel ratio input.farLeft input.left input.center
    input.right input.farRight

def outputs {n : Nat} (fuel : Nat) (ratio : UInt64) (axis : Bool)
    (grid : Grid n n) : Outputs n n :=
  fun j i => evaluate fuel ratio (inputs axis grid j i)

def rowInputs (state : Nat → State) (k : Nat) : Stencil :=
  ⟨state k, state (k + 1), state (k + 2), state (k + 3), state (k + 4)⟩

def rowCenter (state : Nat → State) (k : Nat) : State := state (k + 2)

def rowLeft (fuel : Nat) (state : Nat → State) (k : Nat) : State :=
  (Project.EulerRiemann.Frozen.Reconstruction.reconstruct fuel
    (state k) (state (k + 1)) (state (k + 2))).right

def rowRight (fuel : Nat) (state : Nat → State) (k : Nat) : State :=
  (Project.EulerRiemann.Frozen.Reconstruction.reconstruct fuel
    (state (k + 1)) (state (k + 2)) (state (k + 3))).left

theorem accepted_row_evaluate (fuel : Nat) (ratio : UInt64) (state : Nat → State)
    (k : Nat) (h : (evaluate fuel ratio (rowInputs state k)).status = 0) :
    evaluate fuel ratio (rowInputs state k) =
      faceRowStep ratio (rowCenter state) (rowLeft fuel state) (rowRight fuel state) k := by
  have hp := reconstructed_step_parts fuel ratio (state k) (state (k + 1))
    (state (k + 2)) (state (k + 3)) (state (k + 4)) h
  simpa only [evaluate, rowInputs, faceRowStep, rowCenter, rowLeft, rowRight, Nat.add_assoc]
    using hp.2.2.2

#print axioms accepted_row_evaluate
end Project.EulerReconstructed.Frozen.Numerics
