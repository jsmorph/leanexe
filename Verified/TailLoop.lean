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

theorem wp_loop_indexed {Inv : ι → AssertionF α} {rank : ι → Nat}
    {m : Module} {body rest : Program} {Q : Assertion α} {host : HostEnv α}
    {store : Store α} {s : Locals} {ps rs : Nat} {initial : ι}
    (hInit : Inv initial store s)
    (hStep : ∀ state store s, Inv state store s →
      wp m body (fun cont => match cont with
        | .Fallthrough store' s' =>
          wp m rest Q store' { s' with values := s'.values.take rs ++ s.values.drop ps } host
        | .Break 0 store' s' =>
          ∃ next, Inv next store' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
            rank next < rank state
        | .Break (k + 1) store' s' => Q (.Break k store' s')
        | other => Q other) store s host) :
    wp m (.loop ps rs body :: rest) Q store s host := by
  refine wp_loop_cons (fun store s => ∃ state, Inv state store s)
    (invariantRank Inv rank) ⟨initial, hInit⟩ ?_
  intro store s hi
  obtain ⟨state, hInv, hRank⟩ := invariantRank_spec (rank := rank) hi
  refine wp.conseq ?_ (hStep state store s hInv)
  intro cont hc
  cases cont with
  | Break k store' s' =>
    cases k with
    | zero =>
      obtain ⟨next, hn, hlt⟩ := hc
      exact ⟨⟨next, hn⟩, Nat.lt_of_le_of_lt (invariantRank_le hn) (hRank ▸ hlt)⟩
    | succ k => exact hc
  | _ => exact hc

#print axioms wp_loop_indexed

end Verified.Tail
