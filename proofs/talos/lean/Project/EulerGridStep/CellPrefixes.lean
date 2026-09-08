import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Intermediate logical outputs after each successive cell-field write. -/
def cellPrefix (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Nat → Array UInt64
  | 0 => output
  | field + 1 => (cellPrefix output index cell field).set! (1 + 6 * index + field)
      ((Model.payload cell).getD field 0)

@[simp] theorem cellPrefix_size (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (count : Nat) :
    (cellPrefix output index cell count).size = output.size := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [cellPrefix] using ih

theorem cellPrefix_six (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    cellPrefix output index cell 6 = Model.putCell output index cell := rfl

/-- Newest clone first; the initial output remains live throughout the six calls. -/
def cellLive (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Nat → List LiveBuffer
  | 0 => [⟨roots 0, output⟩]
  | count + 1 => ⟨roots (count + 1), cellPrefix output index cell (count + 1)⟩ ::
      cellLive roots output index cell count

theorem cellLive_member (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (count : Nat) (buffer : LiveBuffer)
    (hMember : buffer ∈ cellLive roots output index cell count) :
    ∃ k ≤ count, buffer = ⟨roots k, cellPrefix output index cell k⟩ := by
  induction count with
  | zero =>
      have h := List.mem_singleton.mp hMember
      exact ⟨0, by omega, h⟩
  | succ count ih =>
      rcases List.mem_cons.mp hMember with h | h
      · exact ⟨count + 1, by omega, h⟩
      · obtain ⟨k, hk, hBuffer⟩ := ih h
        exact ⟨k, by omega, hBuffer⟩

theorem cellLive_contains (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (count k : Nat) (hk : k ≤ count) :
    (⟨roots k, cellPrefix output index cell k⟩ : LiveBuffer) ∈
      cellLive roots output index cell count := by
  induction count with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp [cellLive, cellPrefix]
  | succ count ih =>
      by_cases h : k = count + 1
      · subst k
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by omega))

theorem cellLive_separate (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (count next : Nat)
    (hSeparate : ∀ k ≤ count, ObjectsSeparate (roots next) output.size (roots k) output.size) :
    ∀ buffer ∈ cellLive roots output index cell count,
      ObjectsSeparate (roots next) output.size buffer.root output.size := by
  intro buffer hBuffer
  obtain ⟨k, hk, rfl⟩ := cellLive_member roots output index cell count buffer hBuffer
  exact hSeparate k hk

#print axioms cellPrefix_size
#print axioms cellPrefix_six
#print axioms cellLive_member
#print axioms cellLive_contains
#print axioms cellLive_separate
end Project.EulerGridStep.Execution
