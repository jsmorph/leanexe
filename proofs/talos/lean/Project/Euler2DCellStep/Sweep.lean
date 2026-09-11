import Project.Euler2DCellStep.Spec

namespace Project.Euler2DCellStep.Sweep
open Wasm

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
