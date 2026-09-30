import Project.IR.Call
import Project.IR.Release
import Project.IR.Run

/-!
The invariant of a function body that combines calls and releases temporary
arrays.  `Live` records the allocator invariant, the bounds on `top` and memory,
the arrays of the caller kept, and the live temporaries: each owned, apart from
the caller's arrays, and apart from each other.  `Live.call` adds the fresh result
of a call, `Live.releaseSecond` releases the temporary below the head of the list,
and `Live.finish` gives the postcondition of `Func.implements_heap`.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module}

/-- The block of the object at `p`: its header and its payload capacity. -/
def block (store : Store Unit) (p : UInt64) : Nat × Nat := (p.toNat - 48, 48 + capacityAt store p)

theorem block_eq {store store' : Store Unit} {p : UInt64}
    (h : capacityAt store' p = capacityAt store p) : block store' p = block store p := by
  simp [block, h]

/-- The facts a body keeps while it runs calls: `used` bytes allocated from the
start, and the live temporaries `temps`, the newest first. -/
structure Live (heap0 : Heap) (initial : Store Unit) (used : Nat) (heap : Heap)
    (store : Store Unit) (temps : List (UInt64 × Array UInt64)) : Prop where
  at_ : heap.At store
  top : heap.top.toNat ≤ heap0.top.toNat + used
  pages : store.mem.pages ≤ max initial.mem.pages ((heap0.top.toNat + used + 65535) / 65536)
  caps : store.memoryCaps = initial.memoryCaps
  borrowed : ∀ p ws, heap0.Borrowed initial p ws → heap.Borrowed store p ws
  owned : ∀ p ws, heap0.Owned initial p ws →
    heap.Owned store p ws ∧ capacityAt store p = capacityAt initial p
  tempsOwned : ∀ t ∈ temps, heap.Owned store t.1 t.2
  apartB : ∀ t ∈ temps, ∀ p ws, heap0.Borrowed initial p ws →
    regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block store t.1)
  apartO : ∀ t ∈ temps, ∀ p ws, heap0.Owned initial p ws →
    regionsDisjoint (block initial p) (block store t.1)
  pairwise : temps.Pairwise fun t u => regionsDisjoint (block store t.1) (block store u.1)

theorem Live.start {heap : Heap} {initial : Store Unit} (hHeap : heap.At initial) :
    Live heap initial 0 heap initial [] :=
  ⟨hHeap, by omega, le_max_left _ _, rfl, fun _ _ h => h, fun _ _ h => ⟨h, rfl⟩,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, .nil⟩

/-- A call to entry `idx`, which implements `g` and returns an `Array Float`,
from arguments that represent `x`, leaves its result in local `r` and adds it to
the live temporaries. -/
theorem Live.call [Represent α] {idx : Nat} {g : α → Array Float} {gNeed : α → Nat}
    (hImpl : Implements m idx g gNeed) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {used total : Nat} {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial used heap store temps) (hTotal : heap0.Room initial m total)
    {x : α} (hNeed : used + gNeed x ≤ total) {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hR : r < afterArgs.params.length + afterArgs.locals.length) :
    Triple m (.call idx args [r]) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial (used + gNeed x) heap' s
        ((ptr, (g x).map Float.toBits) :: temps) ∧ st = afterArgs.update r (.i64 ptr)) := by
  have hTop := hLive.top
  have hPages := hLive.pages
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed
    (hTotal.after (used := used) hTop (by omega) hLive.caps)
    fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := h
    exact ⟨afterArgs.update r (.i64 q), by
      simp [State.setAll, State.set?_eq_update _ hR]⟩
  rintro s st ⟨heap', values, hAt', hOwned', -, hTop', hPages', hCaps', hKeepB, hKeepO, hOutB,
    hOutO, hSet⟩
  obtain ⟨q, rfl, hQ⟩ := hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ hR, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  subst hSet
  have hKeepT : ∀ t ∈ temps, heap'.Owned s t.1 t.2 ∧ block s t.1 = block store t.1 := fun t ht =>
    ⟨(hKeepO t.1 t.2 (hLive.tempsOwned t ht)).1, block_eq (hKeepO t.1 t.2 (hLive.tempsOwned t ht)).2⟩
  have hNewB : ∀ p ws, heap0.Borrowed initial p ws →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block s q) := fun p ws h => by
    obtain ⟨q', hq, hDisjoint⟩ := hOutB p ws (hLive.borrowed p ws h)
    simp only [List.cons.injEq, Value.i64.injEq, and_true] at hq
    subst hq
    exact hDisjoint
  have hNewO : ∀ p ws, heap0.Owned initial p ws → regionsDisjoint (block initial p) (block s q) :=
    fun p ws h => by
      obtain ⟨q', hq, hDisjoint⟩ := hOutO p ws (hLive.owned p ws h).1
      simp only [List.cons.injEq, Value.i64.injEq, and_true] at hq
      subst hq
      rw [(hLive.owned p ws h).2] at hDisjoint
      exact hDisjoint
  have hNewT : ∀ t ∈ temps, regionsDisjoint (block s q) (block s t.1) := fun t ht => by
    obtain ⟨q', hq, hDisjoint⟩ := hOutO t.1 t.2 (hLive.tempsOwned t ht)
    simp only [List.cons.injEq, Value.i64.injEq, and_true] at hq
    subst hq
    rw [(hKeepT t ht).2]
    exact regionsDisjoint_symm hDisjoint
  refine ⟨heap', q, ⟨hAt', by omega, by omega, hCaps'.trans hLive.caps,
    fun p ws h => hKeepB p ws (hLive.borrowed p ws h),
    fun p ws h => ⟨(hKeepO p ws (hLive.owned p ws h).1).1,
      (hKeepO p ws (hLive.owned p ws h).1).2.trans (hLive.owned p ws h).2⟩,
    fun t ht => ?_, fun t ht p ws h => ?_, fun t ht p ws h => ?_, ?_⟩, rfl⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hQ
    · exact (hKeepT t ht).1
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNewB p ws h
    · rw [(hKeepT t ht).2]; exact hLive.apartB t ht p ws h
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNewO p ws h
    · rw [(hKeepT t ht).2]; exact hLive.apartO t ht p ws h
  · refine List.pairwise_cons.mpr ⟨fun t ht => hNewT t ht, ?_⟩
    refine List.Pairwise.imp_of_mem (fun {t u} ht hu h => ?_) hLive.pairwise
    rw [(hKeepT t ht).2, (hKeepT u hu).2]
    exact h

/-- Releasing the temporary below the head of the list keeps the rest live. -/
theorem Live.releaseSecond {heap0 heap : Heap} {initial store : Store Unit} {used : Nat}
    {r t : UInt64 × Array UInt64} {rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial used heap store (r :: t :: rest)) {typeIdx scratch src : Nat}
    {before : State} (hImports : m.imports = [])
    (hFunc : m.funcs[2]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1)) :
    Triple m (.release src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => Live heap0 initial used (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
        s (r :: rest) ∧ st = before) := by
  have hT : heap.Owned store t.1 t.2 := hLive.tempsOwned t (by simp)
  have hMem : ∀ u ∈ r :: rest, u ∈ r :: t :: rest := fun u hu => by
    simp only [List.mem_cons] at hu ⊢
    tauto
  have hPair := hLive.pairwise
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hPair
  obtain ⟨⟨hRT, hRRest⟩, hTRest, hRest⟩ := hPair
  have hApartT : ∀ u ∈ r :: rest, regionsDisjoint (block store u.1) (block store t.1) :=
    fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hRT
      · exact regionsDisjoint_symm (hTRest u hu)
  refine (Stmt.release_spec hImports hFunc hPtr hLive.at_ hT).mono (fun _ _ h => h) ?_
  rintro s st ⟨rfl, rfl⟩
  have hKeep : ∀ u ∈ r :: rest,
      (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32)).Owned
        (heap.releaseStore store t.1) u.1 u.2 ∧
      block (heap.releaseStore store t.1) u.1 = block store u.1 := fun u hu => by
    obtain ⟨hOwned, hCapacity⟩ := (hLive.tempsOwned u (hMem u hu)).release hT (hApartT u hu)
    exact ⟨hOwned, block_eq hCapacity⟩
  refine ⟨⟨hLive.at_.release hT, hLive.top, by rw [Heap.releaseStore_pages]; exact hLive.pages,
    hLive.caps, fun p ws h => (hLive.borrowed p ws h).release hT (hLive.apartB t (by simp) p ws h),
    fun p ws h => ?_, fun u hu => (hKeep u hu).1, fun u hu p ws h => ?_, fun u hu p ws h => ?_,
    ?_⟩, rfl⟩
  · obtain ⟨hOwned, hCapacity⟩ := hLive.owned p ws h
    have hApart : regionsDisjoint (p.toNat - 48, 48 + capacityAt store p)
        (t.1.toNat - 48, 48 + capacityAt store t.1) := by
      have hDisjoint := hLive.apartO t (by simp) p ws h
      simp only [block] at hDisjoint
      rw [hCapacity]
      exact hDisjoint
    obtain ⟨hOwned', hCapacity'⟩ := hOwned.release hT hApart
    exact ⟨hOwned', hCapacity'.trans hCapacity⟩
  · rw [(hKeep u hu).2]; exact hLive.apartB u (hMem u hu) p ws h
  · rw [(hKeep u hu).2]; exact hLive.apartO u (hMem u hu) p ws h
  · refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_)
      (List.pairwise_cons.mpr ⟨hRRest, hRest⟩)
    rw [(hKeep a ha).2, (hKeep b hb).2]
    exact h

/-- With one live array, the result, a body ends with the facts that
`Func.implements_heap` requires of a function returning that array. -/
theorem Live.finish [Represent α] {heap0 heap : Heap} {initial store : Store Unit}
    {used need : Nat} {ptr : UInt64} {result : Array Float} {params : List Value} {x : α}
    (hLive : Live heap0 initial used heap store [(ptr, result.map Float.toBits)])
    (hUsed : used ≤ need)
    (hParams : ∀ heap' store', (∀ p ws, heap0.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' params x) :
    ∃ heap' : Heap, heap'.At store ∧ Represent.borrowed heap' store params x ∧
      heap'.top.toNat ≤ heap0.top.toNat + need ∧
      store.mem.pages ≤ max initial.mem.pages ((heap0.top.toNat + need + 65535) / 65536) ∧
      store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      Represent.owned heap' store [.i64 ptr] result ∧
      (∀ p ws, heap0.Borrowed initial p ws →
        Represent.outside store [.i64 ptr] result (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap0.Owned initial p ws →
        Represent.outside store [.i64 ptr] result (p.toNat - 48, 48 + capacityAt initial p)) := by
  have hTop := hLive.top
  have hPages := hLive.pages
  have hMem : (ptr, result.map Float.toBits) ∈ [(ptr, result.map Float.toBits)] :=
    List.mem_singleton_self _
  refine ⟨heap, hLive.at_, hParams heap store hLive.borrowed, by omega, ?_, hLive.caps,
    hLive.borrowed, hLive.owned, ?_, fun p ws h => ?_, fun p ws h => ?_⟩
  · refine le_trans hPages (max_le_max le_rfl (Nat.div_le_div_right ?_))
    omega
  · exact ⟨ptr, rfl, hLive.tempsOwned _ hMem⟩
  · exact ⟨ptr, rfl, hLive.apartB _ hMem p ws h⟩
  · exact ⟨ptr, rfl, hLive.apartO _ hMem p ws h⟩

end Project.IR
