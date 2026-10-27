import Verified.ExprSpec

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def ImplementsStatic {α β : Type} [Represent α] [Represent β] (pool : Bytes.LiteralPool)
    (aborts : Bool) (m : Module) (entry : Nat) (f : α → β)
    (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Pre x heap store → pool.Input heap store params x →
    (∀ table ∈ tables, heap.Borrowed store table.1 table.2 ∧
      Apart store (Represent.moves store params x) (table.1.toNat, 8 * (table.2.size + 1))) →
    Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 →
    Runs aborts env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ region, heap.Region region → 0 < region.2 →
          Apart store (Represent.moves store params x) region →
          (∀ address, region.1 ≤ address → address < region.1 + region.2 →
            final.mem.bytes address = store.mem.bytes address) ∧
            heap'.Region region ∧ Represent.outside final values.reverse (f x) region) ∧
        Post x heap store heap' final

theorem ImplementsStatic.implementsA {α β : Type} {_ : Represent α} {_ : Represent β}
    {base : Nat} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic ⟨base, []⟩ aborts m entry f [] Pre Post) :
    ImplementsA aborts m entry f Pre Post :=
  fun env store heap params value hAt hPre hRep hSep hCap =>
    h env store heap params value hAt hPre (Bytes.LiteralPool.Input.empty _ _ _ _ _)
      (by intro table hTable; exact nomatch hTable) hRep hSep hCap

end Verified
