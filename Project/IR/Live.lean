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
newest first.  The body consumes the caller's objects at `moved`.  Every region of the
caller's heap apart from their blocks keeps its bytes, is a region of the current heap, and
lies apart from the temporaries, which are owned and pairwise apart. -/
structure Live (heap0 : Heap) (initial : Store Unit) (moved : List UInt64) (heap : Heap)
    (store : Store Unit) (temps : List (UInt64 × Array UInt64)) : Prop where
  at_ : heap.At store
  caps : store.memoryCaps = initial.memoryCaps
  keeps : heap0.Keeps initial (moved.map (block initial)) heap store
    (temps.map fun t => block store t.1)
  tempsOwned : ∀ t ∈ temps, heap.Owned store t.1 t.2
  pairwise : temps.Pairwise fun t u => regionsDisjoint (block store t.1) (block store u.1)

/-- The caller's borrowed arrays apart from the consumed blocks stay borrowed. -/
theorem Live.borrowed {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps) :
    ∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      heap.Borrowed store p ws :=
  fun _ _ h hA => (hLive.keeps.borrowed hLive.at_ h (apart_blocks.mp hA)).1

/-- The caller's owned arrays apart from the consumed blocks stay owned, with their
capacities. -/
theorem Live.owned {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps) :
    ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      heap.Owned store p ws ∧ capacityAt store p = capacityAt initial p :=
  fun _ _ h hA => (hLive.keeps.owned hLive.at_ h (apart_blocks.mp hA)).1

/-- The temporaries lie apart from the caller's borrowed arrays. -/
theorem Live.apartB {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps) :
    ∀ t ∈ temps, ∀ p ws, heap0.Borrowed initial p ws →
      Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block store t.1) :=
  fun _ ht _ _ h hA => (hLive.keeps.borrowed hLive.at_ h (apart_blocks.mp hA)).2 _
    (List.mem_map_of_mem ht)

/-- The temporaries lie apart from the caller's owned arrays. -/
theorem Live.apartO {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps) :
    ∀ t ∈ temps, ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      regionsDisjoint (block initial p) (block store t.1) :=
  fun _ ht _ _ h hA => (hLive.keeps.owned hLive.at_ h (apart_blocks.mp hA)).2 _
    (List.mem_map_of_mem ht)

/-- The memory's cap stays within the bound that `Implements` requires. -/
theorem Live.cap {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps)
    (hCap : initial.memoryCap m 0 ≤ 65535) : store.memoryCap m 0 ≤ 65535 :=
  memoryCap_le_of_caps hLive.caps hCap

/-- A step from a live state that consumes the temporaries `consumed`, keeps every region of
the heap apart from their blocks, and leaves the owned temporaries `news`, pairwise apart and
apart from those regions.  The other temporaries stay live after the new ones. -/
theorem Live.step {heap0 heap heap' : Heap} {initial store s : Store Unit}
    {consumed rest news : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (consumed ++ rest))
    (hAt : heap'.At s) (hCaps : s.memoryCaps = store.memoryCaps)
    (hKeeps : heap.Keeps store (consumed.map fun t => block store t.1) heap' s
      (news.map fun t => block s t.1))
    (hNews : ∀ t ∈ news, heap'.Owned s t.1 t.2)
    (hNewsPair : news.Pairwise fun t u => regionsDisjoint (block s t.1) (block s u.1)) :
    Live heap0 initial moved heap' s (news ++ rest) := by
  have hPair := hLive.pairwise
  rw [List.pairwise_append] at hPair
  obtain ⟨-, hRestPair, hCross⟩ := hPair
  have hRest : ∀ u ∈ rest, (heap'.Owned s u.1 u.2 ∧ capacityAt s u.1 = capacityAt store u.1) ∧
      ∀ b ∈ news.map (fun t => block s t.1), regionsDisjoint (block store u.1) b := fun u hu =>
    hKeeps.owned hAt (hLive.tempsOwned u (List.mem_append_right _ hu)) fun b hb => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      exact regionsDisjoint_symm (hCross t ht u hu)
  have hBlock : ∀ u ∈ rest, block s u.1 = block store u.1 := fun u hu => block_eq (hRest u hu).1.2
  refine ⟨hAt, hCaps.trans hLive.caps, fun r hr hpos hApart => ?_, fun u hu => ?_, ?_⟩
  · obtain ⟨hBytes1, hRegion1, hFresh1⟩ := hLive.keeps r hr hpos hApart
    obtain ⟨hBytes2, hRegion2, hFresh2⟩ := hKeeps r hRegion1 hpos fun b hb => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      exact hFresh1 _ (List.mem_map_of_mem (List.mem_append_left _ ht))
    refine ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes1 a hl hh), hRegion2, fun b hb => ?_⟩
    rw [List.map_append] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hFresh2 b hb
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
      rw [hBlock u hu]
      exact hFresh1 _ (List.mem_map_of_mem (List.mem_append_right _ hu))
  · rcases List.mem_append.mp hu with hu | hu
    · exact hNews u hu
    · exact (hRest u hu).1.1
  · refine List.pairwise_append.mpr ⟨hNewsPair, ?_, fun t ht u hu => ?_⟩
    · refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) hRestPair
      rw [hBlock a ha, hBlock b hb]
      exact h
    · rw [hBlock u hu]
      exact regionsDisjoint_symm ((hRest u hu).2 _ (List.mem_map_of_mem ht))

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
  ⟨hHeap, rfl, fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, fun _ hb => nomatch hb⟩,
    fun _ h => by simp at h, .nil⟩

/-- The consumed parameters start as the live temporaries: owned, with pairwise disjoint
blocks, and the caller's facts cover the regions apart from those blocks. -/
theorem Live.start_moved {heap : Heap} {initial : Store Unit} (hHeap : heap.At initial)
    {temps : List (UInt64 × Array UInt64)} (hOwned : ∀ t ∈ temps, heap.Owned initial t.1 t.2)
    (hPairwise : temps.Pairwise fun t u => regionsDisjoint (block initial t.1) (block initial u.1)) :
    Live heap initial (temps.map (·.1)) heap initial temps :=
  ⟨hHeap, rfl, fun _ hr _ hA => ⟨fun _ _ _ => rfl, hr, fun b hb => hA b (by
      rw [List.map_map]; exact hb)⟩, hOwned, hPairwise⟩

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
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeeps, hSet⟩
  obtain ⟨q, rfl, hQ⟩ := hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ hR, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  subst hSet
  refine ⟨heap', q, Live.step (consumed := []) (news := [(q, (g x).map Float.toBits)]) hLive
    hAt' hCaps' (hKeeps.mono (fun b hb => by rw [hNoMoves] at hb; exact nomatch hb)
      fun b hb => hb) (fun t ht => ?_) (List.pairwise_singleton _ _), rfl⟩
  rw [List.mem_singleton.mp ht]
  exact hQ

/-- The order of the live temporaries does not matter. -/
theorem Live.perm {heap0 heap : Heap} {initial store : Store Unit}
    {temps temps' : List (UInt64 × Array UInt64)} (hLive : Live heap0 initial moved heap store temps)
    (hPerm : temps.Perm temps') : Live heap0 initial moved heap store temps' :=
  ⟨hLive.at_, hLive.caps, hLive.keeps.mono (fun _ h => h) fun b hb => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      exact List.mem_map_of_mem (hPerm.mem_iff.mpr ht),
    fun t ht => hLive.tempsOwned t (hPerm.mem_iff.mpr ht),
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
  refine (Stmt.release_spec hImports hFunc hPtr hLive.at_ hT).mono (fun _ _ h => h) ?_
  rintro s st ⟨rfl, rfl⟩
  exact ⟨Live.step (consumed := [t]) (news := []) hLive (hLive.at_.release hT.object) rfl
    ((Heap.Keeps.release hLive.at_ hT.object).mono (fun b hb => hb) fun _ hb => nomatch hb)
    (fun _ h => nomatch h) .nil, rfl⟩

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
    (hReads : ∀ q ∈ Represent.reads store vals x, regionsDisjoint q (block store t.1))
    (hR : r < afterArgs.params.length + afterArgs.locals.length) :
    Triple m (.call idx args [r]) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial moved heap' s
        ((ptr, (g x).map Float.toBits) :: (pre ++ post)) ∧
        st = afterArgs.update r (.i64 ptr)) := by
  have hKeep : ∀ region, regionsDisjoint region (block store t.1) →
      Apart store (Represent.moves store vals x) region := fun region h q hq => by
    rw [hMoves, List.mem_singleton] at hq
    subst hq
    exact h
  have hL := hLive.perm List.perm_middle
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed
    ⟨by rw [hMoves]; exact List.pairwise_singleton _ _, fun q hq => hKeep q (hReads q hq)⟩
    (hLive.cap hCap) fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := h
    exact ⟨afterArgs.update r (.i64 q), by
      simp [State.setAll, State.set?_eq_update _ hR]⟩
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeeps, hSet⟩
  obtain ⟨q, rfl, hQ⟩ := hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ hR, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  subst hSet
  refine ⟨heap', q, Live.step (consumed := [t]) (news := [(q, (g x).map Float.toBits)]) hL
    hAt' hCaps' (hKeeps.mono (fun b hb => by rw [hMoves] at hb; exact hb) fun b hb => hb)
    (fun u hu => ?_) (List.pairwise_singleton _ _), rfl⟩
  rw [List.mem_singleton.mp hu]
  exact hQ

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
    (hReads : ∀ q ∈ Represent.reads store vals x, regionsDisjoint q (block store t.1))
    (hR : r < afterArgs.params.length + afterArgs.locals.length)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' ptr s, Live heap0 initial moved heap' s
      ((ptr, (g x).map Float.toBits) :: (pre ++ post)) →
      Triple m next scratch (fun s' st => s' = s ∧ st = afterArgs.update r (.i64 ptr)) Q) :
    Triple m (.seq (.call idx args [r]) next) scratch (fun s st => s = store ∧ st = before) Q :=
  Stmt.seq_spec
    (Live.callMove hImpl hImport hFunc hParams hLive hCap hArgs hBorrowed hMoves hReads hR)
    (Triple.of_forall fun s _ ⟨heap', ptr, hL, hst⟩ => hst ▸ hNext heap' ptr s hL)

/-- With one live array, the result, a body that consumes the objects at `moved` ends with
the facts that `Func.implements_moves` requires of a function returning that array. -/
theorem Live.finish_moved {heap0 heap : Heap} {initial store : Store Unit}
    {ptr : UInt64} {result : Array Float}
    (hLive : Live heap0 initial moved heap store [(ptr, result.map Float.toBits)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      Represent.owned heap' store [.i64 ptr] result ∧
      heap0.Keeps initial (moved.map (block initial)) heap' store
        (Represent.blocks store [.i64 ptr] result) :=
  ⟨heap, hLive.at_, hLive.caps, ⟨ptr, rfl, hLive.tempsOwned _ (List.mem_singleton_self _)⟩,
    hLive.keeps.mono (fun _ h => h) fun _ hb => hb⟩

/-- With one live array, the result, a body ends with the facts that
`Func.implements_heap` requires of a function returning that array. -/
theorem Live.finish {heap0 heap : Heap} {initial store : Store Unit}
    {ptr : UInt64} {result : Array Float}
    (hLive : Live heap0 initial [] heap store [(ptr, result.map Float.toBits)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      Represent.owned heap' store [.i64 ptr] result ∧
      heap0.Keeps initial [] heap' store (Represent.blocks store [.i64 ptr] result) :=
  Live.finish_moved hLive

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
  obtain ⟨heap', values, hAt', hOwned', hCaps', hKeeps, hSet'⟩ := h
  rw [show values = Scalar.values (g x) from hOwned', hSet, Option.some.injEq] at hSet'
  subst hSet'
  exact hNext heap' s (Live.step (consumed := []) (news := []) hLive hAt' hCaps'
    (hKeeps.mono (fun b hb => by rw [hNoMoves] at hb; exact nomatch hb) fun _ hb => nomatch hb)
    (fun _ h => nomatch h) .nil)

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
