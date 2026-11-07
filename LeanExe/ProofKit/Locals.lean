import Interpreter.Wasm.Locals

/-!
Reads and writes of a Talos frame's locals by their combined index, as reads and writes of the
parameters followed by the internal locals.  The module declares no `simp` lemmas, so importing
it leaves the simplifier's lemmas unchanged.
-/

namespace LeanExe.ProofKit.Locals

open Wasm

/-- A read of a local, as a read of the parameters followed by the internal locals. -/
theorem get_append (s : Locals) (i : Nat) : s.get i = (s.params ++ s.locals)[i]? := by
  unfold Locals.get
  split
  · rw [List.getElem?_append_left (by assumption)]
  · split
    · rw [List.getElem?_append_right (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega)]

/-- A write of a local within range, as a write of the parameters followed by the internal
locals. -/
theorem set?_append (s : Locals) (i : Nat) (v : Value) (hi : i < (s.params ++ s.locals).length) :
    ∃ s', s.set? i v = some s' ∧ s'.params ++ s'.locals = (s.params ++ s.locals).set i v ∧
      s'.values = s.values := by
  unfold Locals.set?
  split
  · exact ⟨_, rfl, by rw [List.set_append_left _ _ (by assumption)], rfl⟩
  · split
    · exact ⟨_, rfl, by rw [List.set_append_right _ _ (by omega)], rfl⟩
    · simp at hi; omega

end LeanExe.ProofKit.Locals
