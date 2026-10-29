import Interpreter.Wasm.Wp.Loop

namespace Verified.Tail

open Wasm

variable {ι α : Type}

noncomputable def invariantRank (Inv : ι → AssertionF α) (rank : ι → Nat)
    (store : Store α) (s : Locals) : Nat := by
  classical
  exact if h : ∃ n, ∃ state, Inv state store s ∧ rank state = n then Nat.find h else 0

theorem invariantRank_le {Inv : ι → AssertionF α} {rank : ι → Nat}
    {store : Store α} {s : Locals} {state : ι} (h : Inv state store s) :
    invariantRank Inv rank store s ≤ rank state := by
  classical
  have hex : ∃ n, ∃ state, Inv state store s ∧ rank state = n := ⟨_, state, h, rfl⟩
  simp only [invariantRank, dif_pos hex]
  exact Nat.find_min' hex ⟨state, h, rfl⟩

theorem invariantRank_spec {Inv : ι → AssertionF α} {rank : ι → Nat}
    {store : Store α} {s : Locals} (h : ∃ state, Inv state store s) :
    ∃ state, Inv state store s ∧ rank state = invariantRank Inv rank store s := by
  classical
  obtain ⟨state, hi⟩ := h
  have hex : ∃ n, ∃ state, Inv state store s ∧ rank state = n := ⟨_, state, hi, rfl⟩
  simpa only [invariantRank, dif_pos hex] using Nat.find_spec hex

end Verified.Tail
