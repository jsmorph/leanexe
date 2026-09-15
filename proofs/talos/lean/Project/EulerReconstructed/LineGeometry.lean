import Project.EulerReconstructed.NumericsModel
import Project.EulerRiemann.NumericsLineGeometry

namespace Project.EulerReconstructed.Conservation
open Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Conservation (clamp lineState orient_twice)
open Project.EulerRiemann.Numerics (stateWords cellWords)

def paddedState {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n)
    (line : Fin n) (k : Nat) : State := lineState hn axis grid line (k - 2)

theorem line_inputs {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n)
    (line i : Fin n) :
    Numerics.rowInputs (paddedState hn axis grid line) i.val =
      Numerics.inputs axis grid (if axis then i else line) (if axis then line else i) := by
  have h0 : clamp hn (i.val - 2) = previous (previous i) := by
    apply Fin.ext
    dsimp only [clamp, previous]
    omega
  have h1 : clamp hn (i.val + 1 - 2) = previous i := by
    apply Fin.ext
    dsimp only [clamp, previous]
    omega
  have h2 : clamp hn (i.val + 2 - 2) = i := by
    apply Fin.ext
    dsimp only [clamp]
    omega
  have h3 : clamp hn (i.val + 3 - 2) = following i := by
    apply Fin.ext
    dsimp only [clamp, following]
    omega
  have h4 : clamp hn (i.val + 4 - 2) = following (following i) := by
    apply Fin.ext
    dsimp only [clamp, following]
    omega
  cases axis <;> simp only [Numerics.rowInputs, paddedState, lineState, Numerics.inputs,
    Bool.false_eq_true, ↓reduceIte, h0, h1, h2, h3, h4]

theorem line_accepted {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (k : Nat) (hk : k < n) :
    (Numerics.evaluate fuel ratio (Numerics.rowInputs (paddedState hn axis grid line) k)).status = 0 := by
  rw [line_inputs hn axis grid line ⟨k, hk⟩]
  exact h _ _

theorem line_face_accepted {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (k : Nat) (hk : k < n) :
    (Project.EulerRiemann.OutwardNumerics.faceRowStep ratio
      (Numerics.rowCenter (paddedState hn axis grid line))
      (Numerics.rowLeft fuel (paddedState hn axis grid line))
      (Numerics.rowRight fuel (paddedState hn axis grid line)) k).status = 0 := by
  have ha := line_accepted hn fuel axis ratio grid h line k hk
  rwa [Numerics.accepted_row_evaluate fuel ratio _ k ha] at ha

theorem line_next_words {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (line : Fin n) (k : Nat) (hk : k < n) (component : Fin 4) :
    let q := lineState hn axis (nextGrid axis (Numerics.outputs fuel ratio axis grid)) line k
    stateWords q.density q.mx q.my q.energy component =
      cellWords (Numerics.evaluate fuel ratio
        (Numerics.rowInputs (paddedState hn axis grid line) k)) component := by
  rw [line_inputs hn axis grid line ⟨k, hk⟩]
  have hc : clamp hn k = (⟨k, hk⟩ : Fin n) :=
    Project.EulerRiemann.Conservation.clamp_current hn ⟨k, hk⟩
  cases axis <;> simp only [lineState, nextGrid, Bool.false_eq_true, ↓reduceIte,
    hc, orient_twice, Numerics.outputs] <;> rfl

#print axioms line_inputs
#print axioms line_accepted
#print axioms line_face_accepted
#print axioms line_next_words
end Project.EulerReconstructed.Conservation
