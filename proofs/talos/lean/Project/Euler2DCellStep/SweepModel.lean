import Project.Euler2DCellStep.Model
import Project.Euler2DConservative.Guard

namespace Project.Euler2DCellStep.Sweep

structure State where
  density : UInt64
  mx : UInt64
  my : UInt64
  energy : UInt64
  deriving DecidableEq, Inhabited

/-- False is x, true is y; exchange the two momenta for the y-normal call. -/
def orient (axis : Bool) (q : State) : State :=
  if axis then ⟨q.density, q.my, q.mx, q.energy⟩ else q

noncomputable def StateSafe (q : State) : Prop :=
  Project.Euler2DConservative.Guard.StateBounds q.density q.mx q.my q.energy ∧
  Project.Euler2DConservative.Guard.Admissible
    (Project.Euler2DConservative.Guard.decodedState q.density q.mx q.my q.energy)

theorem orient_safe (axis : Bool) (q : State) (h : StateSafe q) :
    StateSafe (orient axis q) := by
  cases axis
  · exact h
  · obtain ⟨hb, ha⟩ := h
    refine ⟨⟨hb.densityFinite, hb.transverseFinite, hb.momentumFinite,
      hb.energyFinite, hb.densityPositive, hb.energyPositive, ?_⟩, ?_⟩
    · simpa [orient, Project.Euler2DConservative.Guard.internalEnergy,
        Project.Euler2DConservative.Guard.decodedState, add_comm] using hb.internalPositive
    · simpa [orient, Project.Euler2DConservative.Guard.Admissible,
      Project.Euler2DConservative.Guard.pressure,
      Project.Euler2DConservative.Guard.internalEnergy,
      Project.Euler2DConservative.Guard.decodedState, add_comm] using ha

abbrev Grid (nx ny : Nat) := Fin ny → Fin nx → State
abbrev Outputs (nx ny : Nat) := Fin ny → Fin nx → Model.CheckedCell

def previous {n : Nat} (i : Fin n) : Fin n := ⟨i.val - 1, by omega⟩
def following {n : Nat} (i : Fin n) : Fin n := ⟨min (i.val+1) (n-1), by omega⟩

structure Inputs where
  left : State
  center : State
  right : State

def inputs {nx ny : Nat} (axis : Bool) (grid : Grid nx ny)
    (j : Fin ny) (i : Fin nx) : Inputs :=
  ⟨orient axis (if axis then grid (previous j) i else grid j (previous i)),
   orient axis (grid j i),
   orient axis (if axis then grid (following j) i else grid j (following i))⟩

def evaluate (ratio : UInt64) (q : Inputs) : Model.CheckedCell :=
  Model.cellCheckedBits ratio q.left.density q.left.mx q.left.my q.left.energy
    q.center.density q.center.mx q.center.my q.center.energy
    q.right.density q.right.mx q.right.my q.right.energy

def outputs {nx ny : Nat} (ratio : UInt64) (axis : Bool) (grid : Grid nx ny) : Outputs nx ny :=
  fun j i => evaluate ratio (inputs axis grid j i)

def Accepted {nx ny : Nat} (out : Outputs nx ny) : Prop := ∀ j i, (out j i).status = 0

instance {nx ny : Nat} (out : Outputs nx ny) : Decidable (Accepted out) :=
  inferInstanceAs (Decidable (∀ j i, (out j i).status = 0))

def nextGrid {nx ny : Nat} (axis : Bool) (out : Outputs nx ny) : Grid nx ny :=
  fun j i => orient axis ⟨(out j i).density, (out j i).momentum,
    (out j i).transverse, (out j i).energy⟩

noncomputable def GridSafe {nx ny : Nat} (grid : Grid nx ny) : Prop := ∀ j i, StateSafe (grid j i)

#print axioms orient_safe
end Project.Euler2DCellStep.Sweep
