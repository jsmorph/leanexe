import Verified.AlignedArgs
import Verified.TailState

/-!
The alignment of a context's values, as a tail loop's state and a function's parameters hold
them.  `Env.AlignedVals.var` is a variable's alignment in an aligned context, as `Env.Rep.var` is
its representation.  `HoldsA.ofEnvAligned` is `HoldsA` of the slots that `paramSlots` assigns to
values held in consecutive locals, as `Holds.ofEnvRep` is `Holds`.  `Env.AlignedVals.step` keeps
the alignment across a step that keeps the blocks of the owned values and the regions of the
borrowed ones, as `Env.Rep.step` keeps the representation.
-/

namespace Verified

open Wasm LeanExe.Pipeline

/-- The words of a variable among the words of an aligned context are aligned in its mode. -/
theorem Env.AlignedVals.var {store : Store Unit} {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    ∀ {modes : Nat → Mode} {ws : List Value} {env : Env Γ}, Env.AlignedVals store modes ws env →
      Ty.AlignedVal (modes x.index) store t ((ws.drop x.offset).take t.width) (env.get x) := by
  induction x with
  | here =>
    intro modes ws env h
    cases env with
    | cons v rest =>
      rw [Var.offset, List.drop_zero]
      exact h.1
  | @there Γ' t' s' y ih =>
    intro modes ws env h
    cases env with
    | cons v rest =>
      have hy := ih h.2
      rw [List.drop_drop] at hy
      exact hy

/-- The invariant of a context whose values are held in consecutive locals from `base` on, in the
slots that `paramSlots` assigns. -/
theorem HoldsA.ofEnvAligned {Γ : List Ty} {modes : List Mode} {heap : Heap} {store : Store Unit}
    {ws : List Value} {env : Env Γ} {s : Locals} {base : Nat}
    (hRep : Env.Rep (paramMode Γ modes) heap store ws env)
    (hold : LocalsHold s base (Γ.flatMap Ty.types) ws) (hHeap : heap.Aligned)
    (hAl : Env.AlignedVals store (paramMode Γ modes) ws env) :
    HoldsA env (paramSlots Γ modes base) (fun _ => true) heap store s := by
  refine ⟨hHeap, fun t x _ wx hwx hlx => ?_⟩
  rw [paramSlots_getD x] at hwx ⊢
  obtain rfl := LocalsHold.unique hwx (hold.var x) (by rw [hlx, (hRep.var x).length])
  exact hAl.var x

/-- The alignment of a context's values persists across a step that keeps the blocks of the
owned values and the regions of the borrowed ones. -/
theorem Env.AlignedVals.step {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (step : Step heap store keep heap' store' fresh)
    {Γ : List Ty} (env : Env Γ) (modes : Nat → Mode) (ws : List Value)
    (rep : Env.Rep modes heap store ws env)
    (owned : ∀ q ∈ Env.moves store modes ws env, keep (block store q))
    (borrowed : ∀ r ∈ Env.reads store modes ws env, keep r)
    (h : Env.AlignedVals store modes ws env) : Env.AlignedVals store' modes ws env := by
  induction env generalizing modes ws with
  | nil => trivial
  | @cons Γ t value env ih =>
    obtain ⟨first, rest, rfl, head, tail⟩ := rep
    have keepHead : ∀ r ∈ t.regions (modes 0) store first value, keep r := by
      intro r hr
      cases hm : modes 0 with
      | borrowed =>
        have hr' : r ∈ t.reads store first value := by simpa [Ty.regions, hm] using hr
        exact borrowed r (by rw [Env.reads_cons head.length, hm]; exact List.mem_append_left _ hr')
      | owned =>
        have hr' : r ∈ (t.pointers store first value).map (block store) := by
          simpa [Ty.regions, hm, Ty.blocks_pointers] using hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
        exact owned q (by rw [Env.moves_cons head.length, hm]; exact List.mem_append_left _ hq)
    simp only [Env.AlignedVals, List.take_left' head.length, List.drop_left' head.length] at h ⊢
    exact ⟨h.1.step step head keepHead, ih (fun i => modes (i + 1)) rest tail
      (fun q hq => owned q (by rw [Env.moves_cons head.length]; exact List.mem_append_right _ hq))
      (fun r hr => borrowed r (by rw [Env.reads_cons head.length]; exact List.mem_append_right _ hr))
      h.2⟩

end Verified
