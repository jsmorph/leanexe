import Verified.Correct
import Verified.Instantiate
import LeanExe.ProofKit.BorrowedKept

/-!
The call of an entry of a verified compilation from a ready store.  A store is ready for a module
compiled with the tables `tables` when the allocator invariant holds, the memory cap is at most
65,535 pages, and each table is a borrowed array at its address, which is what the generated
`p.initial` states of the store in which `p.module` starts.  `Call m tables k f Pre Post` names the
statement that function `k` of `m`, called from a ready store with represented arguments `x` that
move no object and with `Pre`, returns `f x` without a trap and leaves a ready store.  The call
also keeps every borrowed array borrowed and every region of the heap intact, and it meets `Post`.
`CallSpec m tables k f B` is `Call` from a store with room for `B x` bytes, in which `top` rises by
at most `B x`.  `ImplementsTables.call` proves `Call` from the theorem of an entry whose tables are
among the program's, `Call.spec` proves `CallSpec` for a specification from a `trapFree` theorem,
and `Call.array` restates `Call` for an entry whose result is an owned array.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- A store from which the entries of the module `m`, compiled with the tables `tables`, run, with
`heap` the allocator's state: the allocator invariant holds, the memory cap is at most 65,535
pages, and table `k` is a borrowed array at `tableAddr tables k`. -/
def Ready (m : Module) (tables : List (Array UInt64)) (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap m 0 ≤ 65535 ∧
    ∀ k (hk : k < tables.length), heap.Borrowed store (tableAddr tables k) tables[k]

/-- The store in which a module without byte literals starts is ready, from the generated
`p.initial`, as `Ready.initial rfl p.initial` states it.  The pool's equation `hpool` lets Lean
match `p.module` by its definition: `p.initial` given as `Ready` directly reaches the recursion
limit for the tables of CRC and of the exponential. -/
theorem Ready.initial {S : List Sig} {prog : Prog S} {tables : List (Array UInt64)}
    {wrappers : List (Wrapper S tables.length)} {pool : Bytes.LiteralPool}
    (hpool : pool = prog.literalPool (tablesEnd tables))
    (h : let store : Store Unit := (compileWith prog tables wrappers).initialStore
      (initialHeap tables).At store ∧ store.memoryCap (compileWith prog tables wrappers) 0 ≤ 65535 ∧
        ∀ k (hk : k < tables.length),
          (initialHeap tables).Borrowed store (tableAddr tables k) tables[k]) :
    Ready (compileWith prog tables wrappers pool) tables (initialHeap tables)
      (compileWith prog tables wrappers pool).initialStore := by
  subst hpool
  exact h

/-- Function `k` of `m`, compiled with the tables `tables`, called from a ready store with the
arguments `x` in `params`, which move no object, and with `Pre`, returns without a trap the
representation of `f x` and leaves a ready store.  Every array borrowed before the call stays
borrowed, every region of the heap before the call keeps its bytes, stays a region, and lies apart
from the result's objects, and `Post` holds. -/
def Call {α β : Type} [Represent α] [Represent β] (m : Module) (tables : List (Array UInt64))
    (k : Nat) (f : α → β) (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (params : List Value) (x : α),
    Ready m tables heap store → Represent.borrowed heap store params x →
    Represent.moves store params x = [] → Pre x heap store →
    Runs false env m k store params.reverse fun final values =>
      ∃ heap' : Heap, Represent.owned heap' final values.reverse (f x) ∧
        Ready m tables heap' final ∧
        (∀ p ws, heap.Borrowed store p ws → heap'.Borrowed final p ws) ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r) ∧
        (∀ r, heap.Region r → 0 < r.2 → Represent.outside final values.reverse (f x) r) ∧
        Post x heap store heap' final

/-- `Call` from a store in which `top` can rise by `B x` bytes within the memory cap, with `top`
rising by at most `B x`. -/
def CallSpec {α β : Type} [Represent α] [Represent β] (m : Module) (tables : List (Array UInt64))
    (k : Nat) (f : α → β) (B : α → Nat) : Prop :=
  Call m tables k f (fun x heap store => heap.Within store m (B x))
    (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + B x)

/-- An entry that reads no table implements its function with the empty list of tables. -/
theorem ImplementsTables.ofA {α β : Type} [Represent α] [Represent β] {aborts : Bool}
    {m : Module} {entry : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m entry f Pre Post) : ImplementsTables aborts m entry f [] Pre Post :=
  fun env store heap params x hAt hPre _ hArgs hSep hCap =>
    h env store heap params x hAt hPre hArgs hSep hCap

/-- An entry that cannot trap and reads the tables `ts`, each of which is a table of the program
at its address, meets `Call`. -/
theorem ImplementsTables.call {α β : Type} [Represent α] [Represent β] {m : Module} {k : Nat}
    {f : α → β} {ts : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hI : ImplementsTables false m k f ts Pre Post) (tables : List (Array UInt64))
    (hts : ∀ t ∈ ts, ∃ i, ∃ hi : i < tables.length, t = (tableAddr tables i, tables[i])) :
    Call m tables k f Pre Post := by
  intro env heap store params x h hargs hmoves hpre
  obtain ⟨hAt, hCap, hTab⟩ := h
  have hapart : ∀ r, Apart store (Represent.moves store params x) r := fun r => by
    rw [hmoves]
    exact Apart.nil
  have htab : ∀ t ∈ ts, heap.Borrowed store t.1 t.2 ∧
      Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := hts t ht
    exact ⟨hTab i hi, hapart _⟩
  have hsep : Separate store (Represent.moves store params x) (Represent.reads store params x) := by
    rw [hmoves]
    exact Separate.nil
  refine (hI env store heap params x hAt hpre htab hargs hsep hCap).mono ?_
  intro final values ⟨heap', hAt', howned, hcaps, hframe, hpost⟩
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos (hapart r)).1, (hframe r hr hpos (hapart r)).2.1⟩
  have hkept : ∀ p ws, heap.Borrowed store p ws → heap'.Borrowed final p ws :=
    fun _ _ hp => LeanExe.ProofKit.BorrowedKept.borrowed_kept hp hAt' hkeep
  exact ⟨heap', howned, ⟨hAt', memoryCap_le_of_caps hcaps hCap, fun i hi => hkept _ _ (hTab i hi)⟩,
    hkept, hkeep, fun r hr hpos => (hframe r hr hpos (hapart r)).2.2, hpost⟩

/-- `CallSpec` for `g` from `Call` for `f`, when room for `B x` bytes gives `Pre`, `Post` bounds the
rise of `top` by `B x`, and `g` equals `f` on every represented argument.  For the generated
`p.f.trapFree` and `B` its bound `p.f.bound`, the first two premises hold by `fun _ _ _ h => h`
and `fun _ _ _ _ _ h => h`, with `trivial` in place of the first for a function that cannot
abort. -/
theorem Call.spec {α β : Type} [Represent α] [Represent β] {m : Module}
    {tables : List (Array UInt64)} {k : Nat} {f g : α → β} {B : α → Nat}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : Call m tables k f Pre Post)
    (hpre : ∀ x heap store, heap.Within store m (B x) → Pre x heap store)
    (hpost : ∀ x heap store heap' final, Post x heap store heap' final →
      heap'.top.toNat ≤ heap.top.toNat + B x)
    (hg : ∀ heap store params x, Represent.borrowed heap store params x → f x = g x) :
    CallSpec m tables k g B := by
  intro env heap store params x hR hargs hmoves hroom
  refine (h env heap store params x hR hargs hmoves (hpre x heap store hroom)).mono ?_
  intro final values ⟨heap', hv, hR', hkept, hkeep, hout, hP⟩
  rw [hg heap store params x hargs] at hv hout
  exact ⟨heap', hv, hR', hkept, hkeep, hout, hpost x heap store heap' final hP⟩

/-- `Call` for an entry whose result is an owned array: the call returns the array's address, and
the array's block lies apart from every region of the heap before the call. -/
theorem Call.array {α : Type} [Represent α] {m : Module} {tables : List (Array UInt64)} {k : Nat}
    {f : α → Array UInt64} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : Call m tables k f Pre Post) (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (x : α) (hR : Ready m tables heap store)
    (hargs : Represent.borrowed heap store params x)
    (hmoves : Represent.moves store params x = []) (hpre : Pre x heap store) :
    Runs false env m k store params.reverse fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.Owned final optr (f x) ∧
        Ready m tables heap' final ∧
        (∀ p ws, heap.Borrowed store p ws → heap'.Borrowed final p ws) ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        Post x heap store heap' final :=
  (h env heap store params x hR hargs hmoves hpre).mono
    fun final values ⟨heap', howned, hR', hkept, hkeep, hout, hpost⟩ => by
      obtain ⟨optr, hv, hown⟩ : ∃ optr, values.reverse = [.i64 optr] ∧
          heap'.Owned final optr (f x) := howned
      refine ⟨optr, by simpa using congrArg List.reverse hv, heap', hown, hR', hkept,
        fun r hr hpos => ⟨(hkeep r hr hpos).1, (hkeep r hr hpos).2, hout r hr hpos _ ?_⟩, hpost⟩
      rw [hv]
      exact List.mem_singleton_self _

#print axioms Ready.initial
#print axioms ImplementsTables.ofA
#print axioms ImplementsTables.call
#print axioms Call.spec
#print axioms Call.array

end Verified
