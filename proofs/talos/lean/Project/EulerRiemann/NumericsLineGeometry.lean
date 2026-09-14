import Project.EulerRiemann.NumericsCellRowBalance

namespace Project.EulerRiemann.Conservation
open Project.Euler2DCellStep.Sweep
open Numerics (rowCellInputs)

def clamp {n : Nat} (hn : 0 < n) (k : Nat) : Fin n :=
  ⟨min k (n - 1), by omega⟩

theorem clamp_current {n : Nat} (hn : 0 < n) (i : Fin n) :
    clamp hn i.val = i := by
  apply Fin.ext
  simp only [clamp]
  omega

theorem clamp_previous {n : Nat} (hn : 0 < n) (i : Fin n) :
    clamp hn (i.val - 1) = previous i := by
  apply Fin.ext
  simp only [clamp, previous]
  omega

theorem clamp_following {n : Nat} (hn : 0 < n) (i : Fin n) :
    clamp hn (i.val + 1) = following i := rfl

def lineState {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n)
    (line : Fin n) (k : Nat) : State :=
  orient axis (if axis then grid (clamp hn k) line else grid line (clamp hn k))

theorem line_inputs {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n)
    (line i : Fin n) :
    rowCellInputs (lineState hn axis grid line) i.val =
      inputs axis grid (if axis then i else line) (if axis then line else i) := by
  cases axis <;> simp [rowCellInputs, lineState, inputs,
    clamp_current, clamp_previous, clamp_following]

theorem line_accepted {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid))
    (line : Fin n) (k : Nat) (hk : k < n) :
    (Numerics.evaluate ratio (rowCellInputs (lineState hn axis grid line) k)).status = 0 := by
  rw [line_inputs hn axis grid line ⟨k, hk⟩]
  exact h _ _

theorem orient_twice (axis : Bool) (q : State) : orient axis (orient axis q) = q := by
  cases axis <;> rfl

theorem line_next_words {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (line : Fin n) (k : Nat) (hk : k < n) (component : Fin 4) :
    let q := lineState hn axis (nextGrid axis (Numerics.outputs ratio axis grid)) line k
    Numerics.stateWords q.density q.mx q.my q.energy component =
      Numerics.cellWords (Numerics.evaluate ratio
        (rowCellInputs (lineState hn axis grid line) k)) component := by
  rw [line_inputs hn axis grid line ⟨k, hk⟩]
  have hc : clamp hn k = (⟨k, hk⟩ : Fin n) := clamp_current hn ⟨k, hk⟩
  cases axis <;> simp only [lineState, nextGrid, Bool.false_eq_true, ↓reduceIte,
    hc, orient_twice, Numerics.outputs] <;> rfl

#print axioms line_inputs
#print axioms line_accepted
#print axioms line_next_words
end Project.EulerRiemann.Conservation
