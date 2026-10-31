import Library.Arrays.BinarySearch.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of binary search.  The compiler translates the tail recursion of
`search` into a loop.  `lowerBound` allocates nothing, so the generated
`compiled.lowerBound.trapFree` requires nothing of the store beyond readiness.  `lowerBound_call`
composes it with `lowerBound_eq`: on a sorted array, function 3 returns `expected`.  The theorem
has the precondition `Sorted` because the search's result on an unsorted array is not specified. -/

namespace Library.Arrays.BinarySearch

open Wasm LeanExe.Pipeline

verified_compile compiled := [search, lowerBound]

theorem lowerBound_export :
    ({ name := "lowerBound", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `Verified.Call` for `g` on the arguments that meet `P`, from `Verified.Call` for `f` and the
equality of `f` and `g` on the represented arguments that meet `P`. -/
theorem call_on {α β : Type} [Represent α] [Represent β] {m : Module}
    {tables : List (Array UInt64)} {k : Nat} {f g : α → β}
    {Pre Q : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (P : α → Prop) (h : Verified.Call m tables k f Pre Post)
    (hq : ∀ x heap store, Q x heap store → P x ∧ Pre x heap store)
    (hg : ∀ heap store params x, Represent.borrowed heap store params x → P x → f x = g x) :
    Verified.Call m tables k g Q Post := by
  intro env heap store params x hR hargs hmoves hQ
  obtain ⟨hp, hpre⟩ := hq x heap store hQ
  rw [← hg heap store params x hargs hp]
  exact h env heap store params x hR hargs hmoves hpre

/-- Function 3, the export `lowerBound`, called from a ready store with a sorted array and a key,
returns without a trap `expected`, the number of elements less than the key, and leaves a ready
store, with `top` risen by at most `compiled.lowerBound.bound`. -/
theorem lowerBound_call :
    Verified.Call compiled.module compiled.tables 3 expected
      (fun x _ _ => Sorted x.1)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.lowerBound.bound x) :=
  call_on (fun x => Sorted x.1)
    (Verified.ImplementsTables.call (.ofA compiled.lowerBound.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ hs => lowerBound_eq x.1 x.2 hs hxs.values.size_lt

#print axioms lowerBound_call

end Library.Arrays.BinarySearch
