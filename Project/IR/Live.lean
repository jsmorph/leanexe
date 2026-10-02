import Project.IR.Call
import Project.IR.Release
import Project.IR.Run

/-!
The invariant of a function body that combines calls and releases temporary
arrays.  `Live` records the allocator invariant, the unchanged memory caps, the
arrays of the caller kept, and the live temporaries: each owned, apart from
the caller's arrays, and apart from each other.  `Live.call` adds the fresh result
of a call, `Live.callScalar_seq` runs a call that returns scalars, `Live.releaseFirst`
and `Live.releaseSecond` release the head of the list and the temporary below it,
and `Live.finish` gives the postcondition of `Func.implements_heap`.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module} {moved : List UInt64}

/-- The facts a body keeps while it runs calls, with the live temporaries `temps`, the
newest first.  The body consumes the caller's arrays at `moved`, and the facts about the
caller's arrays cover those apart from their blocks. -/
structure Live (heap0 : Heap) (initial : Store Unit) (moved : List UInt64) (heap : Heap)
    (store : Store Unit) (temps : List (UInt64 × Array UInt64)) : Prop where
  at_ : heap.At store
  caps : store.memoryCaps = initial.memoryCaps
  borrowed : ∀ p ws, heap0.Borrowed initial p ws →
    Apart initial moved (p.toNat, 8 * (ws.size + 1)) → heap.Borrowed store p ws
  owned : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
    heap.Owned store p ws ∧ capacityAt store p = capacityAt initial p
  tempsOwned : ∀ t ∈ temps, heap.Owned store t.1 t.2
  apartB : ∀ t ∈ temps, ∀ p ws, heap0.Borrowed initial p ws →
    Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
    regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block store t.1)
  apartO : ∀ t ∈ temps, ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
    regionsDisjoint (block initial p) (block store t.1)
  pairwise : temps.Pairwise fun t u => regionsDisjoint (block store t.1) (block store u.1)

/-- The memory's cap stays within the bound that `Implements` requires. -/
theorem Live.cap {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps)
    (hCap : initial.memoryCap m 0 ≤ 65535) : store.memoryCap m 0 ≤ 65535 :=
  memoryCap_le_of_caps hLive.caps hCap

/-- Arguments that begin with an `Array Float` begin with its pointer. -/
theorem Represent.borrowed_float_pair {β : Type} [Represent β] {heap : Heap} {store : Store Unit}
    {vs : List Value} {a : Array Float} {rest : β} (h : Represent.borrowed heap store vs (a, rest)) :
    ∃ p vs', vs = .i64 p :: vs' ∧ heap.Borrowed store p (a.map Float.toBits) ∧
      Represent.borrowed heap store vs' rest := by
  obtain ⟨_, vs', rfl, ⟨p, rfl, hp⟩, h⟩ := h
  exact ⟨p, vs', rfl, hp, h⟩

/-- Arguments that begin with an `Array UInt64` begin with its pointer. -/
theorem Represent.borrowed_uint_pair {β : Type} [Represent β] {heap : Heap} {store : Store Unit}
    {vs : List Value} {a : Array UInt64} {rest : β} (h : Represent.borrowed heap store vs (a, rest)) :
    ∃ p vs', vs = .i64 p :: vs' ∧ heap.Borrowed store p a ∧ Represent.borrowed heap store vs' rest := by
  obtain ⟨_, vs', rfl, ⟨p, rfl, hp⟩, h⟩ := h
  exact ⟨p, vs', rfl, hp, h⟩

/-- Arguments that begin with a consumed `Array Float` begin with its pointer, owned. -/
theorem Represent.borrowed_moved_pair {β : Type} [Represent β] {heap : Heap} {store : Store Unit}
    {vs : List Value} {a : Moved (Array Float)} {rest : β}
    (h : Represent.borrowed heap store vs (a, rest)) :
    ∃ p vs', vs = .i64 p :: vs' ∧ heap.Owned store p (a.val.map Float.toBits) ∧
      Represent.borrowed heap store vs' rest := by
  obtain ⟨_, vs', rfl, ⟨p, rfl, hp⟩, h⟩ := h
  exact ⟨p, vs', rfl, hp, h⟩

theorem Live.start {heap : Heap} {initial : Store Unit} (hHeap : heap.At initial) :
    Live heap initial [] heap initial [] :=
  ⟨hHeap, rfl, fun _ _ h _ => h, fun _ _ h _ => ⟨h, rfl⟩,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, .nil⟩

/-- The consumed parameters start as the live temporaries: owned, with pairwise disjoint
blocks, and the caller's facts cover the arrays apart from those blocks. -/
theorem Live.start_moved {heap : Heap} {initial : Store Unit} (hHeap : heap.At initial)
    {temps : List (UInt64 × Array UInt64)} (hOwned : ∀ t ∈ temps, heap.Owned initial t.1 t.2)
    (hPairwise : temps.Pairwise fun t u => regionsDisjoint (block initial t.1) (block initial u.1)) :
    Live heap initial (temps.map (·.1)) heap initial temps :=
  ⟨hHeap, rfl, fun _ _ h _ => h, fun _ _ h _ => ⟨h, rfl⟩, hOwned,
    fun t ht _ _ _ hA => hA t.1 (List.mem_map_of_mem ht),
    fun t ht _ _ _ hA => hA t.1 (List.mem_map_of_mem ht), hPairwise⟩

/-- A call to entry `idx`, which implements `g` and returns an `Array Float`,
from arguments that represent `x`, leaves its result in local `r` and adds it to
the live temporaries. -/
theorem Live.call [Represent α] {idx : Nat} {g : α → Array Float}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hR : r < afterArgs.params.length + afterArgs.locals.length)
    (hNoMoves : ∀ (s : Store Unit) (vs : List Value) (y : α), Represent.moves s vs y = [] := by
      intro _ _ _; rfl) :
    Triple m (.call idx args [r]) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial moved heap' s
        ((ptr, (g x).map Float.toBits) :: temps) ∧ st = afterArgs.update r (.i64 ptr)) := by
  have hNone : ∀ region, Apart store (Represent.moves store vals x) region := fun _ => by
    rw [hNoMoves]; exact Apart.nil
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed
    ⟨by rw [hNoMoves]; exact .nil, fun r _ => hNone r⟩ (hLive.cap hCap)
    fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := h
    exact ⟨afterArgs.update r (.i64 q), by
      simp [State.setAll, State.set?_eq_update _ hR]⟩
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeepB, hKeepO, hOutB, hOutO, hSet⟩
  obtain ⟨q, rfl, hQ⟩ := hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ hR, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  subst hSet
  have hKeepT : ∀ t ∈ temps, heap'.Owned s t.1 t.2 ∧ block s t.1 = block store t.1 := fun t ht =>
    ⟨(hKeepO t.1 t.2 (hLive.tempsOwned t ht) (hNone _)).1,
      block_eq (hKeepO t.1 t.2 (hLive.tempsOwned t ht) (hNone _)).2⟩
  have hNewB : ∀ p ws, heap0.Borrowed initial p ws →
      Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block s q) := fun p ws h hA => by
    exact Represent.outside_float.mp (hOutB p ws (hLive.borrowed p ws h hA) (hNone _))
  have hNewO : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      regionsDisjoint (block initial p) (block s q) :=
    fun p ws h hA => by
      have hDisjoint := Represent.outside_float.mp (hOutO p ws (hLive.owned p ws h hA).1 (hNone _))
      rw [block_eq (hLive.owned p ws h hA).2] at hDisjoint
      exact hDisjoint
  have hNewT : ∀ t ∈ temps, regionsDisjoint (block s q) (block s t.1) := fun t ht => by
    have hDisjoint := Represent.outside_float.mp (hOutO t.1 t.2 (hLive.tempsOwned t ht) (hNone _))
    rw [(hKeepT t ht).2]
    exact regionsDisjoint_symm hDisjoint
  refine ⟨heap', q, ⟨hAt', hCaps'.trans hLive.caps,
    fun p ws h hA => hKeepB p ws (hLive.borrowed p ws h hA) (hNone _),
    fun p ws h hA => ⟨(hKeepO p ws (hLive.owned p ws h hA).1 (hNone _)).1,
      (hKeepO p ws (hLive.owned p ws h hA).1 (hNone _)).2.trans (hLive.owned p ws h hA).2⟩,
    fun t ht => ?_, fun t ht p ws h hA => ?_, fun t ht p ws h hA => ?_, ?_⟩, rfl⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hQ
    · exact (hKeepT t ht).1
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNewB p ws h hA
    · rw [(hKeepT t ht).2]; exact hLive.apartB t ht p ws h hA
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNewO p ws h hA
    · rw [(hKeepT t ht).2]; exact hLive.apartO t ht p ws h hA
  · refine List.pairwise_cons.mpr ⟨fun t ht => hNewT t ht, ?_⟩
    refine List.Pairwise.imp_of_mem (fun {t u} ht hu h => ?_) hLive.pairwise
    rw [(hKeepT t ht).2, (hKeepT u hu).2]
    exact h

/-- The order of the live temporaries does not matter. -/
theorem Live.perm {heap0 heap : Heap} {initial store : Store Unit}
    {temps temps' : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps)
    (hPerm : temps.Perm temps') : Live heap0 initial moved heap store temps' :=
  ⟨hLive.at_, hLive.caps, hLive.borrowed, hLive.owned,
    fun t ht => hLive.tempsOwned t (hPerm.mem_iff.mpr ht),
    fun t ht => hLive.apartB t (hPerm.mem_iff.mpr ht),
    fun t ht => hLive.apartO t (hPerm.mem_iff.mpr ht),
    (hPerm.pairwise_iff fun h => regionsDisjoint_symm h).mp hLive.pairwise⟩

/-- Releasing the newest temporary keeps the rest live. -/
theorem Live.releaseFirst {heap0 heap : Heap} {initial store : Store Unit}
    {t : UInt64 × Array UInt64} {rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (t :: rest)) {typeIdx scratch src : Nat}
    {before : State} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1)) :
    Triple m (.release src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => Live heap0 initial moved (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
        s rest ∧ st = before) := by
  have hT : heap.Owned store t.1 t.2 := hLive.tempsOwned t (by simp)
  have hPair := hLive.pairwise
  simp only [List.pairwise_cons] at hPair
  obtain ⟨hTRest, hRest⟩ := hPair
  refine (Stmt.release_spec hImports hFunc hPtr hLive.at_ hT).mono (fun _ _ h => h) ?_
  rintro s st ⟨rfl, rfl⟩
  have hKeep : ∀ u ∈ rest,
      (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32)).Owned
        (heap.releaseStore store t.1) u.1 u.2 ∧
      block (heap.releaseStore store t.1) u.1 = block store u.1 := fun u hu => by
    obtain ⟨hOwned, hCapacity⟩ := (hLive.tempsOwned u (List.mem_cons_of_mem _ hu)).release
      hLive.at_ hT.object (regionsDisjoint_symm (hTRest u hu))
    exact ⟨hOwned, block_eq hCapacity⟩
  refine ⟨⟨hLive.at_.release hT.object, hLive.caps, fun p ws h hA => (hLive.borrowed p ws h hA).release hLive.at_ hT.object (hLive.apartB t (by simp) p ws h hA),
    fun p ws h hA => ?_, fun u hu => (hKeep u hu).1, fun u hu p ws h hA => ?_, fun u hu p ws h hA => ?_,
    ?_⟩, rfl⟩
  · obtain ⟨hOwned, hCapacity⟩ := hLive.owned p ws h hA
    have hApart : regionsDisjoint (p.toNat - 48, 48 + capacityAt store p)
        (t.1.toNat - 48, 48 + capacityAt store t.1) := by
      have hDisjoint := hLive.apartO t (by simp) p ws h hA
      simp only [block] at hDisjoint
      rw [hCapacity]
      exact hDisjoint
    obtain ⟨hOwned', hCapacity'⟩ := hOwned.release hLive.at_ hT.object hApart
    exact ⟨hOwned', hCapacity'.trans hCapacity⟩
  · rw [(hKeep u hu).2]; exact hLive.apartB u (List.mem_cons_of_mem _ hu) p ws h hA
  · rw [(hKeep u hu).2]; exact hLive.apartO u (List.mem_cons_of_mem _ hu) p ws h hA
  · refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) hRest
    rw [(hKeep a ha).2, (hKeep b hb).2]
    exact h

/-- Releasing the temporary `t` at any position keeps the rest live. -/
theorem Live.releaseAt {heap0 heap : Heap} {initial store : Store Unit}
    {t : UInt64 × Array UInt64} {pre post : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (pre ++ t :: post)) {typeIdx scratch src : Nat}
    {before : State} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1)) :
    Triple m (.release src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => Live heap0 initial moved (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
        s (pre ++ post) ∧ st = before) :=
  (hLive.perm List.perm_middle).releaseFirst hImports hFunc hPtr

/-- Releasing the temporary below the head of the list keeps the rest live. -/
theorem Live.releaseSecond {heap0 heap : Heap} {initial store : Store Unit}
    {r t : UInt64 × Array UInt64} {rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (r :: t :: rest)) {typeIdx scratch src : Nat}
    {before : State} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1)) :
    Triple m (.release src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => Live heap0 initial moved (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
        s (r :: rest) ∧ st = before) :=
  Live.releaseAt (pre := [r]) hLive hImports hFunc hPtr

/-- A call to entry `idx`, which implements `g`, returns an `Array Float`, and consumes the
temporary `t`, the only array it moves, leaves its result in local `r`; the result
takes `t`'s place among the live temporaries.  The arrays the call reads lie apart from
`t`'s block. -/
theorem Live.callMove [Represent α] {idx : Nat} {g : α → Array Float}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {pre post : List (UInt64 × Array UInt64)} {t : UInt64 × Array UInt64}
    (hLive : Live heap0 initial moved heap store (pre ++ t :: post))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hMoves : Represent.moves store vals x = [t.1])
    (hReads : ∀ q ∈ Represent.reads vals x, regionsDisjoint q (block store t.1))
    (hR : r < afterArgs.params.length + afterArgs.locals.length) :
    Triple m (.call idx args [r]) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial moved heap' s
        ((ptr, (g x).map Float.toBits) :: (pre ++ post)) ∧
        st = afterArgs.update r (.i64 ptr)) := by
  have hT : t ∈ pre ++ t :: post := by simp
  have hRest : ∀ u ∈ pre ++ post, u ∈ pre ++ t :: post := fun u hu => by
    simp only [List.mem_append, List.mem_cons] at hu ⊢
    tauto
  have hPair := hLive.pairwise
  rw [List.pairwise_append, List.pairwise_cons] at hPair
  obtain ⟨hPre, ⟨hTPost, hPost⟩, hCross⟩ := hPair
  have hApartT : ∀ u ∈ pre ++ post, regionsDisjoint (block store u.1) (block store t.1) :=
    fun u hu => by
      rcases List.mem_append.mp hu with hu | hu
      · exact hCross u hu t (List.mem_cons_self ..)
      · exact regionsDisjoint_symm (hTPost u hu)
  have hKeep : ∀ region, regionsDisjoint region (block store t.1) →
      Apart store (Represent.moves store vals x) region := fun region h q hq => by
    rw [hMoves, List.mem_singleton] at hq
    subst hq
    exact h
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed
    ⟨by rw [hMoves]; exact List.pairwise_singleton _ _, fun q hq => hKeep q (hReads q hq)⟩
    (hLive.cap hCap) fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := h
    exact ⟨afterArgs.update r (.i64 q), by
      simp [State.setAll, State.set?_eq_update _ hR]⟩
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeepB, hKeepO, hOutB, hOutO, hSet⟩
  obtain ⟨q, rfl, hQ⟩ := hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ hR, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  subst hSet
  have hKeepT : ∀ u ∈ pre ++ post, heap'.Owned s u.1 u.2 ∧ block s u.1 = block store u.1 :=
    fun u hu =>
      have h := hKeepO u.1 u.2 (hLive.tempsOwned u (hRest u hu)) (hKeep _ (hApartT u hu))
      ⟨h.1, block_eq h.2⟩
  have hOwnedKeep : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      Apart store (Represent.moves store vals x) (block store p) := fun p ws h hA => by
    refine hKeep _ ?_
    rw [block_eq (hLive.owned p ws h hA).2]
    exact hLive.apartO t hT p ws h hA
  have hNewB : ∀ p ws, heap0.Borrowed initial p ws →
      Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block s q) := fun p ws h hA => by
    exact Represent.outside_float.mp (hOutB p ws (hLive.borrowed p ws h hA)
      (hKeep _ (hLive.apartB t hT p ws h hA)))
  have hNewO : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      regionsDisjoint (block initial p) (block s q) := fun p ws h hA => by
    have hDisjoint := Represent.outside_float.mp
      (hOutO p ws (hLive.owned p ws h hA).1 (hOwnedKeep p ws h hA))
    rw [block_eq (hLive.owned p ws h hA).2] at hDisjoint
    exact hDisjoint
  have hNewT : ∀ u ∈ pre ++ post, regionsDisjoint (block s q) (block s u.1) := fun u hu => by
    have hDisjoint := Represent.outside_float.mp (hOutO u.1 u.2 (hLive.tempsOwned u (hRest u hu))
      (hKeep _ (hApartT u hu)))
    rw [(hKeepT u hu).2]
    exact regionsDisjoint_symm hDisjoint
  refine ⟨heap', q, ⟨hAt', hCaps'.trans hLive.caps,
    fun p ws h hA => hKeepB p ws (hLive.borrowed p ws h hA) (hKeep _ (hLive.apartB t hT p ws h hA)),
    fun p ws h hA => ⟨(hKeepO p ws (hLive.owned p ws h hA).1 (hOwnedKeep p ws h hA)).1,
      (hKeepO p ws (hLive.owned p ws h hA).1 (hOwnedKeep p ws h hA)).2.trans
        (hLive.owned p ws h hA).2⟩,
    fun u hu => ?_, fun u hu p ws h hA => ?_, fun u hu p ws h hA => ?_, ?_⟩, rfl⟩
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact hQ
    · exact (hKeepT u hu).1
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact hNewB p ws h hA
    · rw [(hKeepT u hu).2]; exact hLive.apartB u (hRest u hu) p ws h hA
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact hNewO p ws h hA
    · rw [(hKeepT u hu).2]; exact hLive.apartO u (hRest u hu) p ws h hA
  · refine List.pairwise_cons.mpr ⟨fun u hu => hNewT u hu, ?_⟩
    refine List.Pairwise.imp_of_mem (fun {u v} hu hv h => ?_)
      (List.pairwise_append.mpr ⟨hPre, hPost, fun a ha b hb => hCross a ha b
        (List.mem_cons_of_mem _ hb)⟩)
    rw [(hKeepT u hu).2, (hKeepT v hv).2]
    exact h

/-- `Live.callMove` followed by `next`. -/
theorem Live.callMove_seq [Represent α] {idx : Nat} {g : α → Array Float}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {pre post : List (UInt64 × Array UInt64)} {t : UInt64 × Array UInt64}
    (hLive : Live heap0 initial moved heap store (pre ++ t :: post))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hMoves : Represent.moves store vals x = [t.1])
    (hReads : ∀ q ∈ Represent.reads vals x, regionsDisjoint q (block store t.1))
    (hR : r < afterArgs.params.length + afterArgs.locals.length)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' ptr s, Live heap0 initial moved heap' s
      ((ptr, (g x).map Float.toBits) :: (pre ++ post)) →
      Triple m next scratch (fun s' st => s' = s ∧ st = afterArgs.update r (.i64 ptr)) Q) :
    Triple m (.seq (.call idx args [r]) next) scratch (fun s st => s = store ∧ st = before) Q :=
  Stmt.seq_spec
    (Live.callMove hImpl hImport hFunc hParams hLive hCap hArgs hBorrowed hMoves hReads hR)
    (Triple.of_forall fun s _ ⟨heap', ptr, hL, hst⟩ => hst ▸ hNext heap' ptr s hL)

/-- With one live array, the result, a body that consumes the arrays at `moved` ends with
the facts that `Func.implements_moves` requires of a function returning that array. -/
theorem Live.finish_moved {heap0 heap : Heap} {initial store : Store Unit}
    {ptr : UInt64} {result : Array Float}
    (hLive : Live heap0 initial moved heap store [(ptr, result.map Float.toBits)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      Represent.owned heap' store [.i64 ptr] result ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        Represent.outside store [.i64 ptr] result (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        Represent.outside store [.i64 ptr] result (block initial p)) := by
  have hMem : (ptr, result.map Float.toBits) ∈ [(ptr, result.map Float.toBits)] :=
    List.mem_singleton_self _
  exact ⟨heap, hLive.at_, hLive.caps, hLive.borrowed, hLive.owned,
    ⟨ptr, rfl, hLive.tempsOwned _ hMem⟩,
    fun p ws h hA => Represent.outside_float.mpr (hLive.apartB _ hMem p ws h hA),
    fun p ws h hA => Represent.outside_float.mpr (hLive.apartO _ hMem p ws h hA)⟩

/-- With one live array, the result, a body ends with the facts that
`Func.implements_heap` requires of a function returning that array. -/
theorem Live.finish {heap0 heap : Heap} {initial store : Store Unit}
    {ptr : UInt64} {result : Array Float}
    (hLive : Live heap0 initial [] heap store [(ptr, result.map Float.toBits)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      Represent.owned heap' store [.i64 ptr] result ∧
      (∀ p ws, heap0.Borrowed initial p ws →
        Represent.outside store [.i64 ptr] result (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap0.Owned initial p ws →
        Represent.outside store [.i64 ptr] result (p.toNat - 48, 48 + capacityAt initial p)) := by
  have hMem : (ptr, result.map Float.toBits) ∈ [(ptr, result.map Float.toBits)] :=
    List.mem_singleton_self _
  have hBorrowed := fun p ws h => hLive.borrowed p ws h Apart.nil
  refine ⟨heap, hLive.at_, hLive.caps, hBorrowed,
    fun p ws h => hLive.owned p ws h Apart.nil, ?_, fun p ws h => ?_, fun p ws h => ?_⟩
  · exact ⟨ptr, rfl, hLive.tempsOwned _ hMem⟩
  · exact Represent.outside_float.mpr (hLive.apartB _ hMem p ws h Apart.nil)
  · exact Represent.outside_float.mpr (hLive.apartO _ hMem p ws h Apart.nil)

/-- A call followed by `next`: the proof of `next` receives the heap, the result's pointer,
and the store the call leaves, so the caller does not substitute the new state. -/
theorem Live.call_seq [Represent α] {idx : Nat} {g : α → Array Float}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hR : r < afterArgs.params.length + afterArgs.locals.length)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' ptr s, Live heap0 initial moved heap' s
      ((ptr, (g x).map Float.toBits) :: temps) →
      Triple m next scratch (fun s' st => s' = s ∧ st = afterArgs.update r (.i64 ptr)) Q)
    (hNoMoves : ∀ (s : Store Unit) (vs : List Value) (y : α), Represent.moves s vs y = [] := by
      intro _ _ _; rfl) :
    Triple m (.seq (.call idx args [r]) next) scratch (fun s st => s = store ∧ st = before) Q :=
  Stmt.seq_spec (Live.call hImpl hImport hFunc hParams hLive hCap hArgs hBorrowed hR hNoMoves)
    (Triple.of_forall fun s _ ⟨heap', ptr, hL, hst⟩ => hst ▸ hNext heap' ptr s hL)

/-- A release followed by `next`: the proof of `next` receives the store the release
leaves, so the caller does not substitute the unchanged state. -/
theorem Live.releaseSecond_seq {heap0 heap : Heap} {initial store : Store Unit}
    {r t : UInt64 × Array UInt64} {rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (r :: t :: rest)) {typeIdx scratch src : Nat}
    {before : State} {next : Stmt} {Q : Store Unit → State → Prop} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1))
    (hNext : ∀ s, Live heap0 initial moved (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
      s (r :: rest) → Triple m next scratch (fun s' st => s' = s ∧ st = before) Q) :
    Triple m (.seq (.release src) next) scratch (fun s st => s = store ∧ st = before) Q :=
  Stmt.seq_spec (hLive.releaseSecond hImports hFunc hPtr)
    (Triple.of_forall fun s _ ⟨hL, hst⟩ => hst ▸ hNext s hL)

/-- The last release of a body. -/
theorem Live.releaseSecond_last {heap0 heap : Heap} {initial store : Store Unit}
    {r t : UInt64 × Array UInt64} {rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (r :: t :: rest)) {typeIdx scratch src : Nat}
    {before : State} {Q : Store Unit → State → Prop} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (hPtr : before.get src = some (.i64 t.1))
    (hNext : ∀ s, Live heap0 initial moved (heap.release t.1 (store.mem.read64 (t.1 - 32).toUInt32))
      s (r :: rest) → Q s before) :
    Triple m (.release src) scratch (fun s st => s = store ∧ st = before) Q :=
  (hLive.releaseSecond hImports hFunc hPtr).mono (fun _ _ h => h) fun s _ ⟨hL, hst⟩ =>
    hst ▸ hNext s hL

/-- A call to entry `idx`, which implements `g` with a scalar result, followed by `next`:
the result goes to the locals `results`, and the temporaries stay live. -/
theorem Live.callScalar_seq [Represent α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs after : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hSet : afterArgs.setAll results.reverse (Scalar.values (g x)).reverse = some after)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' s, Live heap0 initial moved heap' s temps →
      Triple m next scratch (fun s' st => s' = s ∧ st = after) Q)
    (hNoMoves : ∀ (s : Store Unit) (vs : List Value) (y : α), Represent.moves s vs y = [] := by
      intro _ _ _; rfl) :
    Triple m (.seq (.call idx args results) next) scratch (fun s st => s = store ∧ st = before) Q := by
  have hNone : ∀ region, Apart store (Represent.moves store vals x) region := fun _ => by
    rw [hNoMoves]; exact Apart.nil
  refine Stmt.seq_spec (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_
    hBorrowed ⟨by rw [hNoMoves]; exact .nil, fun r _ => hNone r⟩ (hLive.cap hCap)
    fun _ _ values h => ⟨after, (show values = Scalar.values (g x) from h) ▸ hSet⟩)
    (Triple.of_forall fun s st h => ?_)
  obtain ⟨heap', values, hAt', hOwned', hCaps', hKeepB, hKeepO, -, -, hSet'⟩ := h
  rw [show values = Scalar.values (g x) from hOwned', hSet, Option.some.injEq] at hSet'
  subst hSet'
  have hKeepT : ∀ t ∈ temps, heap'.Owned s t.1 t.2 ∧ block s t.1 = block store t.1 := fun t ht =>
    ⟨(hKeepO t.1 t.2 (hLive.tempsOwned t ht) (hNone _)).1,
      block_eq (hKeepO t.1 t.2 (hLive.tempsOwned t ht) (hNone _)).2⟩
  refine hNext heap' s ⟨hAt', hCaps'.trans hLive.caps,
    fun p ws h hA => hKeepB p ws (hLive.borrowed p ws h hA) (hNone _),
    fun p ws h hA => ⟨(hKeepO p ws (hLive.owned p ws h hA).1 (hNone _)).1,
      (hKeepO p ws (hLive.owned p ws h hA).1 (hNone _)).2.trans (hLive.owned p ws h hA).2⟩,
    fun t ht => (hKeepT t ht).1, fun t ht p ws h hA => ?_, fun t ht p ws h hA => ?_, ?_⟩
  · rw [(hKeepT t ht).2]; exact hLive.apartB t ht p ws h hA
  · rw [(hKeepT t ht).2]; exact hLive.apartO t ht p ws h hA
  · refine List.Pairwise.imp_of_mem (fun {t u} ht hu h => ?_) hLive.pairwise
    rw [(hKeepT t ht).2, (hKeepT u hu).2]
    exact h

theorem Expr.evalResults_nil {mem : Mem} {scratch : Nat} {state : State} :
    Expr.evalResults mem scratch [] state = some ([], state) := rfl

theorem Expr.evalResults_get {mem : Mem} {scratch j : Nat} {state next : State}
    {rest : List ((type : ScalarType) × Expr type)} {vs : List Value} {v : UInt64}
    (hj : state.get j = some (.i64 v))
    (h : Expr.evalResults mem scratch rest state = some (vs, next)) :
    Expr.evalResults mem scratch (⟨.u64, .get j⟩ :: rest) state = some (.i64 v :: vs, next) := by
  simp [Expr.evalResults, Expr.eval, hj, h]

theorem Expr.evalResults_getF {mem : Mem} {scratch j : Nat} {state next : State}
    {rest : List ((type : ScalarType) × Expr type)} {vs : List Value} {v : UInt64}
    (hj : state.get j = some (.f64 v))
    (h : Expr.evalResults mem scratch rest state = some (vs, next)) :
    Expr.evalResults mem scratch (⟨.f64, .getF j⟩ :: rest) state = some (.f64 v :: vs, next) := by
  simp [Expr.evalResults, Expr.eval, hj, h]

theorem Expr.evalResults_u64 {mem : Mem} {scratch : Nat} {e : Expr .u64} {state next : State}
    {rest : List ((type : ScalarType) × Expr type)} {vs : List Value} {v : UInt64}
    (he : e.eval mem scratch state = some (v, state))
    (h : Expr.evalResults mem scratch rest state = some (vs, next)) :
    Expr.evalResults mem scratch (⟨.u64, e⟩ :: rest) state = some (.i64 v :: vs, next) := by
  simp [Expr.evalResults, he, h]

theorem Expr.evalResults_cons {mem : Mem} {scratch : Nat} {e : Expr .u64} {state mid next : State}
    {rest : List ((type : ScalarType) × Expr type)} {vs : List Value} {v : UInt64}
    (he : e.eval mem scratch state = some (v, mid))
    (h : Expr.evalResults mem scratch rest mid = some (vs, next)) :
    Expr.evalResults mem scratch (⟨.u64, e⟩ :: rest) state = some (.i64 v :: vs, next) := by
  simp [Expr.evalResults, he, h]

theorem Expr.eval_get {mem : Mem} {scratch j : Nat} {state : State} {v : UInt64}
    (hj : state.get j = some (.i64 v)) :
    (Expr.get j).eval mem scratch state = some (v, state) := by
  simp [Expr.eval, hj]

theorem Expr.eval_mul {mem : Mem} {scratch : Nat} {a b : Expr .u64} {state : State} {x y : UInt64}
    (ha : a.eval mem scratch state = some (x, state)) (hb : b.eval mem scratch state = some (y, state)) :
    (Expr.bin .mul a b).eval mem scratch state = some (x * y, state) := by
  simp [Expr.eval, ha, hb, U64Op.apply]

theorem Expr.eval_add {mem : Mem} {scratch : Nat} {a b : Expr .u64} {state : State} {x y : UInt64}
    (ha : a.eval mem scratch state = some (x, state)) (hb : b.eval mem scratch state = some (y, state)) :
    (Expr.bin .add a b).eval mem scratch state = some (x + y, state) := by
  simp [Expr.eval, ha, hb, U64Op.apply]

theorem Expr.eval_const {mem : Mem} {scratch : Nat} {state : State} {v : UInt64} :
    (Expr.const v).eval mem scratch state = some (v, state) := rfl

end Project.IR
