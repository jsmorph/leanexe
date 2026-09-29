import Project.TalosPrelude
import Project.Pipeline.Runtime

namespace Project.Pipeline

open Wasm

/-- How a Lean value appears to a compiled function: as WASM values, together
with any heap data they point to.  `borrowed` describes an argument, which the
call may read but must leave intact.  `owned` describes a result, which the
caller owns after the call. -/
class Represent (α : Type) where
  borrowed : Heap → Store Unit → List Value → α → Prop
  owned : Heap → Store Unit → List Value → α → Prop

/-- A value that occupies WASM values only, with no heap data. -/
class Scalar (α : Type) where
  values : α → List Value

instance (priority := low) [Scalar α] : Represent α where
  borrowed _ _ vs x := vs = Scalar.values x
  owned _ _ vs x := vs = Scalar.values x

theorem Scalar.borrowed [Scalar α] {heap : Heap} {store : Store Unit} {params : List Value}
    {x : α} : Represent.borrowed heap store params x ↔ params = Scalar.values x :=
  Iff.rfl

instance : Scalar UInt64 := ⟨fun x => [.i64 x]⟩

instance [Scalar α] [Scalar β] : Scalar (α × β) :=
  ⟨fun p => Scalar.values p.1 ++ Scalar.values p.2⟩

instance : Represent (Array UInt64) where
  borrowed heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Borrowed store ptr xs
  owned heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr xs

/-- Entry `entry` of `m` computes `f` exactly.  From any store that satisfies the
allocator invariant, with arguments `params` (in declaration order) representing
`x` and room for `need x` bytes, the call terminates and returns values that
represent `f x` and that the caller owns.  The arguments still represent `x`, the
allocator invariant holds again, `top` advances by at most `need x` bytes, and
memory grows only as far as the new `top` requires. -/
def Implements [Represent α] [Represent β] (m : Module) (entry : Nat) (f : α → β)
    (need : α → Nat) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Represent.borrowed heap store params x → heap.Room store m (need x) →
    TerminatesWith env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values (f x) ∧
        Represent.borrowed heap' final params x ∧ heap'.top.toNat ≤ heap.top.toNat + need x ∧
        final.mem.pages ≤ max store.mem.pages ((heap.top.toNat + need x + 65535) / 65536)

/-- For every input satisfying `P`, under the premises of `Implements`, the call
returns an owned result `y` with `Q x y`. -/
def Satisfies [Represent α] [Represent β] (m : Module) (entry : Nat) (need : α → Nat)
    (P : α → Prop) (Q : α → β → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    P x → heap.At store → Represent.borrowed heap store params x → heap.Room store m (need x) →
    TerminatesWith env m entry store params.reverse fun final values =>
      ∃ (heap' : Heap) (y : β), heap'.At final ∧ Represent.owned heap' final values y ∧ Q x y

theorem Implements.transfer [Represent α] [Represent β] {m : Module} {entry : Nat}
    {f : α → β} {need : α → Nat} {P : α → Prop} {Q : α → β → Prop}
    (h : Implements m entry f need) (hf : ∀ x, P x → Q x (f x)) :
    Satisfies m entry need P Q := by
  intro env store heap params x hP hHeap hArgs hRoom
  obtain ⟨N, hN⟩ := h env store heap params x hHeap hArgs hRoom
  refine ⟨N, fun fuel hFuel => ?_⟩
  obtain ⟨values, final, hRun, heap', hAt, hOwned, -⟩ := hN fuel hFuel
  exact ⟨values, final, hRun, heap', f x, hAt, hOwned, hf x hP⟩

end Project.Pipeline
