import Verified.Call

/-! Theorems that carry a module's theorem from one Lean function to another that equals it on the
represented arguments.  `implementsA_congr` carries `ImplementsA`, which also covers arguments that
the caller hands over, such as `Moved (Array UInt64)`.  `call_on` carries `Call` to a function that
equals the first on the represented arguments that meet a predicate `P`, which the new
precondition implies. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- `ImplementsA` for `g` from `ImplementsA` for `f` and the equality of `f` and `g` on the
represented arguments. -/
theorem implementsA_congr {α β : Type} [Represent α] [Represent β] {aborts : Bool} {m : Module}
    {entry : Nat} {f g : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post)
    (hfg : ∀ heap store params x, Represent.borrowed heap store params x → f x = g x) :
    ImplementsA aborts m entry g Pre Post := by
  intro env store heap params x hHeap hPre hArgs hSep hCap
  rw [← hfg heap store params x hArgs]
  exact h env store heap params x hHeap hPre hArgs hSep hCap

/-- `Call` for `g` on the arguments that meet `P`, from `Call` for `f` and the equality of `f` and
`g` on the represented arguments that meet `P`. -/
theorem call_on {α β : Type} [Represent α] [Represent β] {m : Module}
    {tables : List (Array UInt64)} {k : Nat} {f g : α → β}
    {Pre Q : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (P : α → Prop) (h : Call m tables k f Pre Post)
    (hq : ∀ x heap store, Q x heap store → P x ∧ Pre x heap store)
    (hg : ∀ heap store params x, Represent.borrowed heap store params x → P x → f x = g x) :
    Call m tables k g Q Post := by
  intro env heap store params x hR hargs hmoves hQ
  obtain ⟨hp, hpre⟩ := hq x heap store hQ
  rw [← hg heap store params x hargs hp]
  exact h env heap store params x hR hargs hmoves hpre

end Verified
