import Project.IR.Build
import Project.IR.Live
import Project.Pipeline.Implements

/-!
The template for `xs ++ ys` when the caller hands over `xs`.  When the block of `xs`
has room for both arrays, the template stores the new length and the elements of `ys`
in place.  Otherwise it allocates a block of twice the old capacity, or of the size
needed when that is larger, at most `2 ^ 32` bytes, copies both arrays into it, and
releases the old block.  `Live.append` states the template for a body's live temporaries.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Element `i` of `xs ++ ys`, with `i` in local `index`: element `i` of the array at
local `src1` below its length, held in local `size1`, and element `i - size1` of the
array at local `src2` from there on. -/
def Stmt.appendElement (size1 index src1 src2 : Nat) : Expr .u64 :=
  .ite (.ltU (.get index) (.get size1)) (.read src1 (.get index))
    (.read src2 (.bin .sub (.get index) (.get size1)))

/-- The bytes of the new block: `min (max need (2 * capacity)) (2 ^ 32)`, where `need`
covers the length word and the elements counted in local `limit`, and local `cap` holds
the old capacity. -/
def Stmt.appendRequest (limit cap : Nat) : Expr .u64 :=
  .ite (.leU (.bin .mul (.bin .add (.get limit) (.const 1)) (.const 8))
      (.bin .mul (.get cap) (.const 2)))
    (.ite (.leU (.bin .mul (.get cap) (.const 2)) (.const 4294967296))
      (.bin .mul (.get cap) (.const 2)) (.const 4294967296))
    (.bin .mul (.bin .add (.get limit) (.const 1)) (.const 8))

/-- Local `dst` receives `xs ++ ys`, where local `src1` holds `xs`, which the template
consumes, and local `src2` holds `ys`.  The code traps when the result has `2 ^ 29`
elements or more. -/
def Stmt.append (dst size1 size2 limit index cap src1 src2 : Nat) : Stmt :=
  .seq (.arraySize size1 src1) <|
  .seq (.arraySize size2 src2) <|
  .seq (.assign limit (.bin .add (.get size1) (.get size2))) <|
  .seq (.ite (.ltU (.get limit) (.const 536870912)) .skip .abort) <|
  .seq (.load .u64 cap (.bin .sub (.get src1) (.const 32))) <|
  .seq (.ite (.leU (.bin .mul (.bin .add (.get limit) (.const 1)) (.const 8)) (.get cap))
      (.seq (.assign dst (.get src1)) (.assign index (.get size1)))
      (.seq (.assign cap (Stmt.appendRequest limit cap)) <|
        .seq (.call 0 [⟨.u64, .get cap⟩] [dst]) (.assign index (.const 0)))) <|
  .seq (.store (.get dst) (.get limit)) <|
  .seq (.fill dst limit index .skip (Stmt.appendElement size1 index src1 src2)) <|
  .ite (.eq (.get dst) (.get src1)) .skip (.release src1)

/-- The element expression gives element `k` of `xs ++ ys`, reading `xs` below its length
and `ys` from there on. -/
theorem appendElement_eval {store : Store Unit} {scratch size1 index src1 src2 : Nat}
    {state : State} {p1 p2 : UInt64} {xs ys : Array UInt64} {k : Nat}
    (hk : k < (xs ++ ys).size) (hSize : xs.size + ys.size < 536870912)
    (hScratch : scratch < state.params.length + state.locals.length)
    (hBelow1 : src1 < scratch) (hBelow2 : src2 < scratch)
    (hIndex : state.get index = some (.i64 (UInt64.ofNat k)))
    (hSize1 : state.get size1 = some (.i64 (UInt64.ofNat xs.size)))
    (hP1 : state.get src1 = some (.i64 p1)) (hP2 : state.get src2 = some (.i64 p2))
    (hXs : k < xs.size → UInt64Array.At store p1 xs)
    (hYs : xs.size ≤ k → UInt64Array.At store p2 ys) :
    ∃ next, (Stmt.appendElement size1 index src1 src2).eval store.mem scratch state =
      some ((xs ++ ys)[k], next) := by
  rw [Array.size_append] at hk
  have hLt : (UInt64.ofNat k < UInt64.ofNat xs.size) ↔ k < xs.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega),
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
  have hK : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  by_cases hLow : k < xs.size
  · obtain ⟨saved, hSet⟩ := State.exists_set? (state := state) (index := scratch)
      (.i64 (UInt64.ofNat k)) hScratch
    refine ⟨saved, ?_⟩
    simp only [Stmt.appendElement, Expr.eval, hIndex, hSize1, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, decide_eq_true (hLt.mpr hLow), ite_true]
    rw [hSet, Option.bind_some, Expr.readValue_at (hXs hLow)
      (by rw [State.get_set?_ne (by omega) hSet, hP1]), hK, getElem!_pos xs k hLow,
      Array.getElem_append_left hLow]
  · have hHigh : xs.size ≤ k := by omega
    have hSub : (UInt64.ofNat k - UInt64.ofNat xs.size).toNat = k - xs.size := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hK,
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; omega), hK,
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    obtain ⟨saved, hSet⟩ := State.exists_set? (state := state) (index := scratch)
      (.i64 (UInt64.ofNat k - UInt64.ofNat xs.size)) hScratch
    refine ⟨saved, ?_⟩
    simp only [Stmt.appendElement, Expr.eval, hIndex, hSize1, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, decide_eq_false (fun h => hLow (hLt.mp h)),
      Bool.false_eq_true, ite_false, U64Op.apply, reduceCtorEq, or_self]
    rw [hSet, Option.bind_some, Expr.readValue_at (hYs hHigh)
      (by rw [State.get_set?_ne (by omega) hSet, hP2]), hSub,
      getElem!_pos ys (k - xs.size) (by omega), Array.getElem_append_right hHigh]

/-- The request is at least the bytes the result needs and at most `2 ^ 32`. -/
theorem appendRequest_eval {mem : Mem} {scratch limit cap : Nat} {state : State} {total : Nat}
    {c : UInt64} (hTotal : total < 536870912) (hC : c.toNat < 4294967296)
    (hLimit : state.get limit = some (.i64 (UInt64.ofNat total)))
    (hCap : state.get cap = some (.i64 c)) :
    ∃ r : UInt64, (Stmt.appendRequest limit cap).eval mem scratch state = some (r, state) ∧
      8 * (total + 1) ≤ r.toNat ∧ r.toNat ≤ 4294967296 := by
  have hNeed : ((UInt64.ofNat total + 1) * 8).toNat = 8 * (total + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hDouble : (c * 2).toNat = 2 * c.toNat := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  simp only [Stmt.appendRequest, Expr.eval, hLimit, hCap, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, U64Op.apply, reduceCtorEq, or_self, ite_false]
  by_cases h1 : (UInt64.ofNat total + 1) * 8 ≤ c * 2
  · by_cases h2 : c * 2 ≤ 4294967296
    · refine ⟨c * 2, by simp [h1, h2], ?_, ?_⟩
      · rw [UInt64.le_iff_toNat_le, hNeed] at h1; exact h1
      · rw [UInt64.le_iff_toNat_le] at h2; exact h2
    · refine ⟨4294967296, by simp [h1, h2], ?_, by decide⟩
      simp only [UInt64.reduceToNat]
      omega
  · refine ⟨(UInt64.ofNat total + 1) * 8, by simp [h1], by rw [hNeed], by rw [hNeed]; omega⟩

/-- The facts after `Stmt.append` with `xs` at `p1`: local `dst` holds an owned array
`all`, every array apart from the block of `xs` is kept, an owned one with its capacity,
and the result's block lies apart from each of them. -/
def Stmt.AppendPost (heap : Heap) (initial : Store Unit) (before : State) (scratch : Nat)
    (locals : List Nat) (dst : Nat) (p1 : UInt64) (all : Array UInt64) (store : Store Unit)
    (state : State) : Prop :=
  ∃ (heap' : Heap) (p : UInt64), State.Frame scratch locals before state ∧
    state.get dst = some (.i64 p) ∧ heap'.At store ∧ heap'.Owned store p all ∧
    store.memoryCaps = initial.memoryCaps ∧
    (∀ q ws, heap.Borrowed initial q ws →
      regionsDisjoint (q.toNat, 8 * (ws.size + 1)) (block initial p1) →
      heap'.Borrowed store q ws ∧ regionsDisjoint (q.toNat, 8 * (ws.size + 1)) (block store p)) ∧
    (∀ q ws, heap.Owned initial q ws → regionsDisjoint (block initial q) (block initial p1) →
      heap'.Owned store q ws ∧ capacityAt store q = capacityAt initial q ∧
      regionsDisjoint (block initial q) (block store p))

/-- The in-place path: the block of `xs` has room for the result, so the template stores
the new length and the elements of `ys` after those of `xs`. -/
theorem Stmt.appendInPlace_spec {scratch dst size1 size2 limit index cap src1 src2 : Nat}
    {initial : Store Unit} {before start : State} {heap : Heap} {p1 p2 : UInt64}
    {xs ys : Array UInt64}
    (hLocals : [dst, size1, size2, limit, index, cap].Nodup)
    (hBelow : ∀ j ∈ [dst, size1, size2, limit, index, cap], j < scratch)
    (hSrc1 : src1 ∉ [dst, size1, size2, limit, index, cap])
    (hSrc2 : src2 ∉ [dst, size1, size2, limit, index, cap])
    (hSrcBelow1 : src1 < scratch) (hSrcBelow2 : src2 < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hXs : heap.Owned initial p1 xs) (hYs : heap.Borrowed initial p2 ys)
    (hApart : regionsDisjoint (p2.toNat, 8 * (ys.size + 1)) (block initial p1))
    (hSize : xs.size + ys.size < 536870912)
    (hFit : 8 * (xs.size + ys.size + 1) ≤ capacityAt initial p1)
    (hFrame0 : State.Frame scratch [dst, size1, size2, limit, index, cap] before start)
    (hP1 : before.get src1 = some (.i64 p1)) (hP2 : before.get src2 = some (.i64 p2))
    (hDst0 : start.get dst = some (.i64 p1))
    (hLimit0 : start.get limit = some (.i64 (UInt64.ofNat (xs.size + ys.size))))
    (hIndex0 : start.get index = some (.i64 (UInt64.ofNat xs.size)))
    (hSize10 : start.get size1 = some (.i64 (UInt64.ofNat xs.size))) :
    Triple m (.seq (.store (.get dst) (.get limit)) <|
        .seq (.fill dst limit index .skip (Stmt.appendElement size1 index src1 src2)) <|
        .ite (.eq (.get dst) (.get src1)) .skip (.release src1)) scratch
      (fun s st => s = initial ∧ st = start)
      (Stmt.AppendPost heap initial before scratch [dst, size1, size2, limit, index, cap] dst p1
        (xs ++ ys)) := by
  have hSub : [dst, limit, index].Sublist [dst, size1, size2, limit, index, cap] :=
    .cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons _ .slnil)))))
  have hLocals3 : [dst, limit, index].Nodup := hLocals.sublist hSub
  have hBelow3 : ∀ j ∈ [dst, limit, index], j < scratch := fun j hj => hBelow j (hSub.subset hj)
  have hNot1 : ∀ j ∈ [dst, limit, index], j ≠ src1 := fun j hj h => hSrc1 (h ▸ hSub.subset hj)
  have hNot2 : ∀ j ∈ [dst, limit, index], j ≠ src2 := fun j hj h => hSrc2 (h ▸ hSub.subset hj)
  have hSize1In : size1 ∈ [dst, size1, size2, limit, index, cap] := by simp
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDS1, -, hDL, hDI, -⟩, ⟨-, hS1L, hS1I, -⟩, -, -, -⟩ := hLocals
  obtain ⟨-, hS1B, -, -, -, -⟩ := hBelow
  have hS1Out : size1 ∉ [dst, limit, index] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hDS1, hS1L, hS1I⟩
  have hXv := hXs.values
  have hCapFit := hXs.address
  have hBelowTop := hXs.below
  have hBase := hXs.base
  have hTop := hHeap.top
  have hP1_32 : p1.toUInt32.toNat = p1.toNat := hXv.pointerAddress_toNat
  have hAllSize : (xs ++ ys).size = xs.size + ys.size := Array.size_append ..
  generalize hAllDef : xs ++ ys = all at hAllSize ⊢
  obtain ⟨store1, hStore1⟩ : ∃ s : Store Unit,
      s = { initial with mem := initial.mem.write64 p1.toUInt32 (UInt64.ofNat all.size) } :=
    ⟨_, rfl⟩
  have hPrefix1 : UInt64Array.PrefixAt store1 p1 all xs.size := by
    subst hStore1
    refine ⟨by omega, by simp only [Wasm.Mem.write64_pages]; omega,
      Memory.read64_write64 .., fun i hi hix => ?_⟩
    rw [Memory.read64_write64_disjoint _ _ _ _ (by
      rw [UInt64Array.wordAddress_toNat (words := all.size + 1) (by omega) (by omega)]; omega)]
    subst hAllDef
    rw [Array.getElem_append_left hix]
    exact hXv.elementRead i hix
  have hWrites1 : Memory.WritesRange initial store1 p1.toNat (p1.toNat + 8 * (all.size + 1)) := by
    subst hStore1
    exact Memory.WritesRange.write64 _ p1.toUInt32 _ _ _ (by omega) (by omega)
  have hSrc1F : ∀ {st}, State.Frame scratch [dst, limit, index] start st →
      st.get src1 = some (.i64 p1) := fun hF => by
    rw [hF.get src1 hSrcBelow1 (fun h => hNot1 src1 h rfl), hFrame0.get src1 hSrcBelow1 hSrc1, hP1]
  refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = start) ?_ <|
    Stmt.seq_spec (M := fun s st => UInt64Array.At s p1 all ∧
      Memory.WritesRange initial s p1.toNat (p1.toNat + 8 * (all.size + 1)) ∧
      State.Frame scratch ([dst, limit, index] ++ []) start st ∧ st.get dst = some (.i64 p1)) ?_ ?_
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨p1, start, UInt64.ofNat all.size, start, by simp [Expr.eval, hDst0],
      by simp [Expr.eval, hLimit0, hAllSize], by omega, hStore1.symm, rfl⟩
  · refine Stmt.fill_spec (writes := []) hLocals3 hBelow3 (by simp)
      (by rw [hFrame0.params, hFrame0.locals]; omega) (by omega) (by omega) hPrefix1 hWrites1
      hDst0 (by rw [hLimit0, hAllSize]) hIndex0 fun k hk s st hk0 hW hF hI => ?_
    refine (Stmt.skip_spec (R := fun s' st' => s' = s ∧ st' = st)).mono (fun _ _ h => h) ?_
    rintro s' st' ⟨hs, hst⟩
    subst s' st'
    have hFk : State.Frame scratch [dst, limit, index] start st := by simpa using hF
    have hYv : UInt64Array.At s p2 ys := by
      refine hYs.values.writesRange hW ?_
      simp only [block, regionsDisjoint] at hApart
      omega
    subst hAllDef
    obtain ⟨next, hEval⟩ := appendElement_eval (store := s) (scratch := scratch) (state := st)
      (p1 := p1) (hk := hk) hSize (by rw [hFk.params, hFk.locals, hFrame0.params, hFrame0.locals]; omega)
      hSrcBelow1 hSrcBelow2 hI
      (by rw [hFk.get size1 hS1B hS1Out, hSize10])
      (hSrc1F hFk)
      (by rw [hFk.get src2 hSrcBelow2 (fun h => hNot2 src2 h rfl),
        hFrame0.get src2 hSrcBelow2 hSrc2, hP2])
      (fun h => absurd h (by omega)) fun _ => hYv
    exact ⟨rfl, State.Frame.refl _ _ _, next, hEval⟩
  · apply Triple.of_forall
    rintro s st ⟨hAt, hW, hF, hD⟩
    have hFk : State.Frame scratch [dst, limit, index] start st := by simpa using hF
    refine (Stmt.ite_spec (PThen := fun s' st' => s' = s ∧ st' = st) (PElse := fun _ _ => False)
      Stmt.skip_spec Triple.of_false).mono ?_ ?_
    · rintro s' st' ⟨hs, hst⟩
      subst s' st'
      exact ⟨true, st, by simp [Expr.eval, hD, hSrc1F hFk], rfl, rfl⟩
    rintro s' st' ⟨hs, hst⟩
    subst s' st'
    have hWithin : WritesWithin initial s p1.toNat (capacityAt initial p1) :=
      ⟨by rw [hW.1], hW.2.1, fun address h => hW.2.2 address (by omega)⟩
    have hCap32 : (UInt64.ofNat (capacityAt initial p1)).toNat = capacityAt initial p1 :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hWithin' : WritesWithin initial s p1.toNat (UInt64.ofNat (capacityAt initial p1)).toNat := by
      rw [hCap32]; exact hWithin
    obtain ⟨hOwned, hCapacity⟩ := hXs.rewrite hWithin hAt (by omega)
    have hBlock : block s p1 = block initial p1 := block_eq hCapacity
    refine ⟨heap, p1, hFrame0.trans (hFk.weaken fun j hj => by simp at hj ⊢; omega), hD,
      hHeap.writesOwned hXs hWithin, hOwned, by rw [hW.1], fun q ws hq hDisjoint => ?_,
      fun q ws hq hDisjoint => ?_⟩
    · rw [hBlock]
      refine ⟨hq.writesWithin (by rw [hCap32]; exact hDisjoint) hWithin', hDisjoint⟩
    · rw [hBlock]
      have hqBase := hq.base
      have hqFit := hq.address
      refine ⟨hq.writesWithin (by rw [hCap32]; exact hDisjoint) (by omega) hWithin', ?_, hDisjoint⟩
      refine capacityAt_frame (by omega) (by omega) fun a hl hh => hWithin.bytes a ?_
      simp only [block, regionsDisjoint] at hDisjoint
      omega

/-- The growth fill: a new block of `need` bytes, enough for `all`, receives the length from
local `limit` and, by the fill loop, the values of `element`, which give the elements of `all`
while the old arrays stay in place; then the block of `xs` at local `src1` is released. -/
theorem Stmt.growFill_spec {releaseType scratch dst limit index src1 : Nat} {locals : List Nat}
    {initial : Store Unit} {before start : State} {heap : Heap} {p1 need : UInt64}
    {xs all : Array UInt64} {element : Expr .u64} (hImports : m.imports = [])
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hIn : ∀ j ∈ [dst, limit, index], j ∈ locals)
    (hSrc1 : src1 ∉ locals) (hSrcBelow1 : src1 < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hXs : heap.Owned initial p1 xs)
    (hSize : all.size < 536870912) (hFits : heap.Fits need)
    (hNeed : 8 * (all.size + 1) ≤ need.toNat)
    (hFrame0 : State.Frame scratch locals before start)
    (hP1 : before.get src1 = some (.i64 p1))
    (hDst0 : start.get dst = some (.i64 (FixedArrayAllocate.root heap.top need heap.free)))
    (hLimit0 : start.get limit = some (.i64 (UInt64.ofNat all.size)))
    (hIndex0 : start.get index = some (.i64 (UInt64.ofNat 0)))
    (hElement : ∀ (k : Nat) (hk : k < all.size) (s : Store Unit) (st : State),
      Memory.WritesRange (heap.allocateStore initial need 1) s
        (FixedArrayAllocate.root heap.top need heap.free).toNat
        ((FixedArrayAllocate.root heap.top need heap.free).toNat + 8 * (all.size + 1)) →
      State.Frame scratch [dst, limit, index] start st →
      st.get index = some (.i64 (UInt64.ofNat k)) →
      ∃ next, element.eval s.mem scratch st = some (all[k], next)) :
    Triple m (.seq (.store (.get dst) (.get limit)) <|
        .seq (.fill dst limit index .skip element) <|
        .ite (.eq (.get dst) (.get src1)) .skip (.release src1)) scratch
      (fun s st => s = heap.allocateStore initial need 1 ∧ st = start)
      (fun s st => Stmt.AppendPost heap initial before scratch locals dst p1 all s st ∧
        ∃ q, st.get dst = some (.i64 q) ∧ need.toNat ≤ capacityAt s q) := by
  have hNot1 : ∀ j ∈ [dst, limit, index], j ≠ src1 := fun j hj h => hSrc1 (h ▸ hIn j hj)
  have hBlock := hHeap.allocate_block 1 hFits
  have hCapacity := allocated_capacity need heap.free
  have hXApart := hXs.disjoint_allocated hHeap need
  have hXcap := hXs.capacity
  generalize hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr at hBlock hDst0 hXApart hElement
  have hBlockAddress := hBlock.address
  have hBlockMemory := hBlock.memory
  have hBlockBase := hBlock.base
  have hPtr32 : ptr.toUInt32.toNat = ptr.toNat := by
    rw [Memory.toUInt32_toNat]; omega
  generalize hStoreA : heap.allocateStore initial need 1 = storeA at hBlock hBlockMemory hElement ⊢
  obtain ⟨store1, hStore1⟩ : ∃ s : Store Unit,
      s = { storeA with mem := storeA.mem.write64 ptr.toUInt32 (UInt64.ofNat all.size) } :=
    ⟨_, rfl⟩
  have hPrefix1 : UInt64Array.PrefixAt store1 ptr all 0 := by
    subst hStore1
    refine UInt64Array.PrefixAt.empty _ _ _ (by omega) ?_ (Memory.read64_write64 ..)
    simp only [Wasm.Mem.write64_pages]
    omega
  have hWrites1 : Memory.WritesRange storeA store1 ptr.toNat (ptr.toNat + 8 * (all.size + 1)) := by
    subst hStore1
    exact Memory.WritesRange.write64 _ ptr.toUInt32 _ _ _ (by omega) (by omega)
  have hSrc1F : ∀ {st}, State.Frame scratch [dst, limit, index] start st →
      st.get src1 = some (.i64 p1) := fun hF => by
    rw [hF.get src1 hSrcBelow1 (fun h => hNot1 src1 h rfl), hFrame0.get src1 hSrcBelow1 hSrc1, hP1]
  refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = start) ?_ <|
    Stmt.seq_spec (M := fun s st => UInt64Array.At s ptr all ∧
      Memory.WritesRange storeA s ptr.toNat (ptr.toNat + 8 * (all.size + 1)) ∧
      State.Frame scratch ([dst, limit, index] ++ []) start st ∧ st.get dst = some (.i64 ptr)) ?_ ?_
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨ptr, start, UInt64.ofNat all.size, start, by simp [Expr.eval, hDst0],
      by simp [Expr.eval, hLimit0], by omega, hStore1.symm, rfl⟩
  · refine Stmt.fill_spec (writes := []) hLocals hBelow (by simp)
      (by rw [hFrame0.params, hFrame0.locals]; omega) (by omega) (Nat.zero_le _) hPrefix1 hWrites1
      hDst0 hLimit0 hIndex0 fun k hk s st _ hW hF hI => ?_
    refine (Stmt.skip_spec (R := fun s' st' => s' = s ∧ st' = st)).mono (fun _ _ h => h) ?_
    rintro s' st' ⟨hs, hst⟩
    subst s' st'
    have hFk : State.Frame scratch [dst, limit, index] start st := by simpa using hF
    obtain ⟨next, hEval⟩ := hElement k hk s st hW hFk hI
    exact ⟨rfl, State.Frame.refl _ _ _, next, hEval⟩
  · apply Triple.of_forall
    rintro s st ⟨hAt, hW, hF, hD⟩
    have hFk : State.Frame scratch [dst, limit, index] start st := by simpa using hF
    have hWithin : WritesWithin storeA s ptr.toNat (allocatedCapacity need heap.free).toNat :=
      ⟨by rw [hW.1], hW.2.1, fun address h => hW.2.2 address (by omega)⟩
    subst hPtrDef hStoreA
    have hNew := Heap.newArray_of_writes hHeap hFits hWithin hAt (by omega)
      (by rw [hW.1]; exact heap.allocateStore_memoryCaps initial need 1)
    have hCapS := ((hHeap.allocate_block 1 hFits).writesWithin hWithin).capacity_eq
    generalize hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr at hNew hD hXApart hCapS
    have hNe : ptr ≠ p1 := by
      rintro rfl
      simp only [regionsDisjoint] at hXApart
      omega
    obtain ⟨hOwnedP1, hCapP1⟩ := hNew.ownedKeep p1 xs hXs
    refine (Stmt.ite_spec (PThen := fun _ _ => False) (PElse := fun s' st' => s' = s ∧ st' = st)
      Triple.of_false (Stmt.release_spec hImports hRelease (hSrc1F hFk) hNew.at_ hOwnedP1)).mono
      ?_ ?_
    · rintro s' st' ⟨hs, hst⟩
      subst s' st'
      exact ⟨false, st, by simp [Expr.eval, hD, hSrc1F hFk, hNe], rfl, rfl⟩
    rintro s' st' ⟨hs, hst⟩
    subst s' st'
    have hBlockP1 : block s p1 = block initial p1 := block_eq hCapP1
    have hApartNew : regionsDisjoint (block s ptr) (block s p1) := by
      have := hNew.ownedApart p1 xs hXs
      rw [hBlockP1]
      exact regionsDisjoint_symm this
    obtain ⟨hOwnedNew, hCapNew⟩ := hNew.owned.release hNew.at_ hOwnedP1.object hApartNew
    have hBlockNew : block ((heap.allocate need).releaseStore s p1) ptr = block s ptr :=
      block_eq hCapNew
    refine ⟨⟨_, ptr, hFrame0.trans (hFk.weaken fun j hj => hIn j (by simpa using hj)), hD,
      hNew.at_.release hOwnedP1.object, hOwnedNew, hNew.caps, fun q ws hq hDisjoint => ?_,
      fun q ws hq hDisjoint => ?_⟩, ptr, hD, by rw [hCapNew, hCapS]; exact hCapacity⟩
    · rw [hBlockNew]
      refine ⟨(hNew.borrowed q ws hq).release hNew.at_ hOwnedP1.object ?_, hNew.borrowedApart q ws hq⟩
      rw [← hBlockP1] at hDisjoint
      exact hDisjoint
    · rw [hBlockNew]
      obtain ⟨hqOwned, hqCap⟩ := hNew.ownedKeep q ws hq
      have hqApart : regionsDisjoint (block s q) (block s p1) := by
        rw [block_eq hqCap, hBlockP1]; exact hDisjoint
      obtain ⟨hqOwned', hqCap'⟩ := hqOwned.release hNew.at_ hOwnedP1.object hqApart
      exact ⟨hqOwned', hqCap'.trans hqCap, hNew.ownedApart q ws hq⟩

/-- The growth path: a new block of `need` bytes, enough for the result, receives the length
and the elements of both arrays, and the block of `xs` is released. -/
theorem Stmt.appendGrow_spec {releaseType scratch dst size1 size2 limit index cap src1 src2 : Nat}
    {initial : Store Unit} {before start : State} {heap : Heap} {p1 p2 need : UInt64}
    {xs ys : Array UInt64} (hImports : m.imports = [])
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    (hLocals : [dst, size1, size2, limit, index, cap].Nodup)
    (hBelow : ∀ j ∈ [dst, size1, size2, limit, index, cap], j < scratch)
    (hSrc1 : src1 ∉ [dst, size1, size2, limit, index, cap])
    (hSrc2 : src2 ∉ [dst, size1, size2, limit, index, cap])
    (hSrcBelow1 : src1 < scratch) (hSrcBelow2 : src2 < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hXs : heap.Owned initial p1 xs) (hYs : heap.Borrowed initial p2 ys)
    (hSize : xs.size + ys.size < 536870912) (hFits : heap.Fits need)
    (hNeed : 8 * (xs.size + ys.size + 1) ≤ need.toNat)
    (hFrame0 : State.Frame scratch [dst, size1, size2, limit, index, cap] before start)
    (hP1 : before.get src1 = some (.i64 p1)) (hP2 : before.get src2 = some (.i64 p2))
    (hDst0 : start.get dst = some (.i64 (FixedArrayAllocate.root heap.top need heap.free)))
    (hLimit0 : start.get limit = some (.i64 (UInt64.ofNat (xs.size + ys.size))))
    (hIndex0 : start.get index = some (.i64 (UInt64.ofNat 0)))
    (hSize10 : start.get size1 = some (.i64 (UInt64.ofNat xs.size))) :
    Triple m (.seq (.store (.get dst) (.get limit)) <|
        .seq (.fill dst limit index .skip (Stmt.appendElement size1 index src1 src2)) <|
        .ite (.eq (.get dst) (.get src1)) .skip (.release src1)) scratch
      (fun s st => s = heap.allocateStore initial need 1 ∧ st = start)
      (Stmt.AppendPost heap initial before scratch [dst, size1, size2, limit, index, cap] dst p1
        (xs ++ ys)) := by
  have hSub : [dst, limit, index].Sublist [dst, size1, size2, limit, index, cap] :=
    .cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons _ .slnil)))))
  have hLocals3 : [dst, limit, index].Nodup := hLocals.sublist hSub
  have hBelow3 : ∀ j ∈ [dst, limit, index], j < scratch := fun j hj => hBelow j (hSub.subset hj)
  have hNot1 : ∀ j ∈ [dst, limit, index], j ≠ src1 := fun j hj h => hSrc1 (h ▸ hSub.subset hj)
  have hNot2 : ∀ j ∈ [dst, limit, index], j ≠ src2 := fun j hj h => hSrc2 (h ▸ hSub.subset hj)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDS1, -, hDL, hDI, -⟩, ⟨-, hS1L, hS1I, -⟩, -, -, -⟩ := hLocals
  obtain ⟨-, hS1B, -, -, -, -⟩ := hBelow
  have hS1Out : size1 ∉ [dst, limit, index] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hDS1, hS1L, hS1I⟩
  have hXApart := hXs.disjoint_allocated hHeap need
  have hYApart := hYs.disjoint_allocated hHeap need
  have hXA := hXs.allocate 1 hHeap hFits
  have hYA := hYs.allocate 1 hHeap hFits
  have hBlock := hHeap.allocate_block 1 hFits
  have hCapacity := allocated_capacity need heap.free
  have hBlockAddress := hBlock.address
  have hBlockBase := hBlock.base
  have hXcap := hXs.capacity
  have hSrc1F : ∀ {st}, State.Frame scratch [dst, limit, index] start st →
      st.get src1 = some (.i64 p1) := fun hF => by
    rw [hF.get src1 hSrcBelow1 (fun h => hNot1 src1 h rfl), hFrame0.get src1 hSrcBelow1 hSrc1, hP1]
  refine (Stmt.growFill_spec (all := xs ++ ys) hImports hRelease hLocals3 hBelow3
    (fun j hj => hSub.subset hj) hSrc1 hSrcBelow1 hRoom hHeap hXs (by simp; omega) hFits
    (by simp; omega) hFrame0 hP1 hDst0 (by rw [hLimit0, Array.size_append]) hIndex0
    fun k hk s st hW hFk hI => ?_).mono (fun _ _ h => h) fun _ _ h => h.1
  have hXv : UInt64Array.At s p1 xs := by
    refine hXA.values.writesRange hW ?_
    simp only [regionsDisjoint] at hXApart
    simp only [Array.size_append] at hW ⊢
    omega
  have hYv : UInt64Array.At s p2 ys := by
    refine hYA.values.writesRange hW ?_
    simp only [regionsDisjoint] at hYApart
    simp only [Array.size_append] at hW ⊢
    omega
  exact appendElement_eval (store := s) (scratch := scratch) (state := st)
    (hk := hk) hSize
    (by rw [hFk.params, hFk.locals, hFrame0.params, hFrame0.locals]; omega)
    hSrcBelow1 hSrcBelow2 hI (by rw [hFk.get size1 hS1B hS1Out, hSize10]) (hSrc1F hFk)
    (by rw [hFk.get src2 hSrcBelow2 (fun h => hNot2 src2 h rfl),
      hFrame0.get src2 hSrcBelow2 hSrc2, hP2])
    (fun _ => hXv) fun _ => hYv

theorem le_allocSize {bytes : UInt64} (h : bytes.toNat ≤ 4294967296) :
    bytes.toNat ≤ (allocSize bytes).toNat := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hSmall
    rw [UInt64.lt_iff_toNat_lt, hRound] at hSmall
    simp only [UInt64.reduceToNat] at hSmall ⊢
    omega
  · rw [hRound]
    omega

/-- Local `dst` receives `xs ++ ys` as an owned array, where local `src1` holds `xs`, owned
and consumed, and local `src2` holds `ys`, borrowed and apart from the block of `xs`.  The
template writes the locals `dst`, `size1`, `size2`, `limit`, `index`, and `cap`. -/
theorem Stmt.append_spec {typeIdx releaseType scratch dst size1 size2 limit index cap src1 src2 : Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {p1 p2 : UInt64}
    {xs ys : Array UInt64} (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hAlloc : m.funcs[0]? = some (allocFunction typeIdx))
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    (hLocals : [dst, size1, size2, limit, index, cap].Nodup)
    (hBelow : ∀ j ∈ [dst, size1, size2, limit, index, cap], j < scratch)
    (hSrc1 : src1 ∉ [dst, size1, size2, limit, index, cap])
    (hSrc2 : src2 ∉ [dst, size1, size2, limit, index, cap])
    (hSrcBelow1 : src1 < scratch) (hSrcBelow2 : src2 < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hXs : heap.Owned initial p1 xs) (hYs : heap.Borrowed initial p2 ys)
    (hApart : regionsDisjoint (p2.toNat, 8 * (ys.size + 1)) (block initial p1))
    (hP1 : before.get src1 = some (.i64 p1)) (hP2 : before.get src2 = some (.i64 p2)) :
    Triple m (.append dst size1 size2 limit index cap src1 src2) scratch
      (fun s st => s = initial ∧ st = before)
      (Stmt.AppendPost heap initial before scratch [dst, size1, size2, limit, index, cap] dst p1
        (xs ++ ys)) := by
  have hLocals0 := hLocals
  have hBelow0 := hBelow
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDS1, hDS2, hDL, hDI, hDC⟩, ⟨hS1S2, hS1L, hS1I, hS1C⟩, ⟨hS2L, hS2I, hS2C⟩, ⟨hLI, hLC⟩,
    hIC⟩ := hLocals
  obtain ⟨hDB, hS1B, hS2B, hLB, hIB, hCB⟩ := hBelow
  have hS1D : size1 ≠ dst := Ne.symm hDS1
  have hLD : limit ≠ dst := Ne.symm hDL
  have hSrc1' := hSrc1
  have hSrc2' := hSrc2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hSrc1' hSrc2'
  obtain ⟨h1D, h1S1, h1S2, h1L, h1I, h1C⟩ := hSrc1'
  obtain ⟨h2D, h2S1, h2S2, h2L, h2I, h2C⟩ := hSrc2'
  have hXv := hXs.values
  have hYv := hYs.values
  have hXFit := hXv.1
  have hYFit := hYv.1
  have hBase := hXs.base
  have hCapFit := hXs.address
  have hBelowTop := hXs.below
  have hTop := hHeap.top
  have hLen := hRoom
  -- The sizes and their sum.
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := size1)
    (.i64 (UInt64.ofNat xs.size)) (by omega)
  have hF1 : State.Frame scratch [dst, size1, size2, limit, index, cap] before s1 :=
    (State.Frame.refl _ _ _).set? hSet1 (Or.inl (by simp))
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := size2)
    (.i64 (UInt64.ofNat ys.size)) (by rw [hF1.params, hF1.locals]; omega)
  have hF2 := hF1.set? hSet2 (Or.inl (by simp))
  have hTotalValue : UInt64.ofNat xs.size + UInt64.ofNat ys.size =
      UInt64.ofNat (xs.size + ys.size) := by
    rw [← UInt64.ofNat_add]
  obtain ⟨s3, hSet3⟩ := State.exists_set? (state := s2) (index := limit)
    (.i64 (UInt64.ofNat (xs.size + ys.size))) (by rw [hF2.params, hF2.locals]; omega)
  have hF3 := hF2.set? hSet3 (Or.inl (by simp))
  have hGet1_3 : s3.get size1 = some (.i64 (UInt64.ofNat xs.size)) := by
    rw [State.get_set?_ne hS1L hSet3, State.get_set?_ne hS1S2 hSet2, State.get_set?_same hSet1]
  have hLimit3 : s3.get limit = some (.i64 (UInt64.ofNat (xs.size + ys.size))) :=
    State.get_set?_same hSet3
  have hSrc1_3 : s3.get src1 = some (.i64 p1) := by
    rw [hF3.get src1 hSrcBelow1 hSrc1, hP1]
  have hSrc2_3 : s3.get src2 = some (.i64 p2) := by
    rw [hF3.get src2 hSrcBelow2 hSrc2, hP2]
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
    Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
    Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
    Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3 ∧ xs.size + ys.size < 536870912) ?_ ?_
  · exact (Stmt.arraySize_spec hXv hP1 (by omega)).mono (fun _ _ h => h)
      fun s st ⟨hs, hst⟩ => ⟨hs, Option.some.inj (hst.symm.trans hSet1)⟩
  · refine (Stmt.arraySize_spec (initial := initial) (before := s1) hYv
      (by rw [hF1.get src2 hSrcBelow2 hSrc2, hP2]) (by rw [hF1.params, hF1.locals]; omega)).mono
      (fun _ _ h => h) fun s st ⟨hs, hst⟩ => ⟨hs, Option.some.inj (hst.symm.trans hSet2)⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    refine ⟨UInt64.ofNat (xs.size + ys.size), s2, s3, ?_, hSet3, rfl, rfl⟩
    simp only [Expr.eval, State.get_set?_same hSet2, State.get_set?_ne hS1S2 hSet2,
      State.get_set?_same hSet1, U64Op.apply, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, reduceCtorEq, or_self, ite_false]
    rw [hTotalValue]
  · refine (Stmt.ite_spec
      (PThen := fun s st => s = initial ∧ st = s3 ∧ xs.size + ys.size < 536870912)
      (PElse := fun _ _ => True) Stmt.skip_spec Stmt.abort_spec).mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    by_cases hn : xs.size + ys.size < 536870912
    · refine ⟨true, s3, ?_, rfl, rfl, hn⟩
      simp [Expr.eval, hLimit3, UInt64.lt_iff_toNat_lt]
      omega
    · refine ⟨false, s3, ?_, trivial⟩
      simp [Expr.eval, hLimit3, UInt64.lt_iff_toNat_lt]
      omega
  apply Triple.of_forall
  rintro s st ⟨hs, hst, hSize⟩
  subst s st
  -- The capacity word.
  obtain ⟨c, hc⟩ : ∃ c : UInt64, c = initial.mem.read64 (p1 - 32).toUInt32 := ⟨_, rfl⟩
  have hcNat : c.toNat = capacityAt initial p1 := by rw [hc]; rfl
  have hHeader : (p1 - 32).toUInt32.toNat = p1.toNat - 32 := by
    have := headerAddress_toNat (ptr := p1) (k := 32) (by simp; omega) (by omega)
    simpa using this
  obtain ⟨s5, hSet5⟩ := State.exists_set? (state := s3) (index := cap) (.i64 c)
    (by rw [hF3.params, hF3.locals]; omega)
  have hF5 := hF3.set? hSet5 (Or.inl (by simp))
  have hLimit5 : s5.get limit = some (.i64 (UInt64.ofNat (xs.size + ys.size))) := by
    rw [State.get_set?_ne hLC hSet5, hLimit3]
  have hCap5 : s5.get cap = some (.i64 c) := State.get_set?_same hSet5
  have hSize1_5 : s5.get size1 = some (.i64 (UInt64.ofNat xs.size)) := by
    rw [State.get_set?_ne hS1C hSet5, hGet1_3]
  have hSrc1_5 : s5.get src1 = some (.i64 p1) := by rw [hF5.get src1 hSrcBelow1 hSrc1, hP1]
  -- The states of the in-place path.
  obtain ⟨t1, hT1⟩ := State.exists_set? (state := s5) (index := dst) (.i64 p1)
    (by rw [hF5.params, hF5.locals]; omega)
  obtain ⟨t2, hT2⟩ := State.exists_set? (state := t1) (index := index)
    (.i64 (UInt64.ofNat xs.size)) (by
      have := (hF5.set? hT1 (Or.inl (by simp))).params
      have := (hF5.set? hT1 (Or.inl (by simp))).locals
      omega)
  have hFT2 := (hF5.set? hT1 (Or.inl (by simp))).set? hT2 (Or.inl (by simp))
  -- The states of the growth path.
  obtain ⟨r, hREval, hR1, hR2⟩ := appendRequest_eval (mem := initial.mem) (scratch := scratch)
    hSize (by omega) hLimit5 hCap5
  generalize hNeedDef : allocSize r = need
  have hNeed : 8 * (xs.size + ys.size + 1) ≤ need.toNat := by
    rw [← hNeedDef]; exact hR1.trans (le_allocSize hR2)
  obtain ⟨g1, hG1⟩ := State.exists_set? (state := s5) (index := cap) (.i64 r)
    (by rw [hF5.params, hF5.locals]; omega)
  have hFG1 := hF5.set? hG1 (Or.inl (by simp))
  obtain ⟨g2, hG2⟩ := State.exists_set? (state := g1) (index := dst)
    (.i64 (FixedArrayAllocate.root heap.top need heap.free))
    (by rw [hFG1.params, hFG1.locals]; omega)
  have hFG2 := hFG1.set? hG2 (Or.inl (by simp))
  obtain ⟨g3, hG3⟩ := State.exists_set? (state := g2) (index := index) (.i64 (UInt64.ofNat 0))
    (by rw [hFG2.params, hFG2.locals]; omega)
  have hFG3 := hFG2.set? hG3 (Or.inl (by simp))
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s5) ?_ <|
    Stmt.seq_spec (M := fun s st =>
      (s = initial ∧ st = t2 ∧ 8 * (xs.size + ys.size + 1) ≤ capacityAt initial p1) ∨
      (heap.Fits need ∧ s = heap.allocateStore initial need 1 ∧ st = g3)) ?_ ?_
  · refine Stmt.load_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    refine ⟨p1 - 32, s3, s5, by simp [Expr.eval, hSrc1_3, U64Op.apply], by omega, ?_, rfl, rfl⟩
    rw [← hc]
    exact hSet5
  · refine (Stmt.ite_spec
      (PThen := fun s st => s = initial ∧ st = s5 ∧
        8 * (xs.size + ys.size + 1) ≤ capacityAt initial p1)
      (PElse := fun s st => s = initial ∧ st = s5) ?_ ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = t1 ∧
        8 * (xs.size + ys.size + 1) ≤ capacityAt initial p1) ?_ ?_
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨hs, hst, hFit⟩
        subst s st
        exact ⟨p1, s5, t1, by simp [Expr.eval, hSrc1_5], hT1, rfl, rfl, hFit⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨hs, hst, hFit⟩
        subst s st
        refine ⟨UInt64.ofNat xs.size, t1, t2, ?_, hT2, .inl ⟨rfl, rfl, hFit⟩⟩
        simp [Expr.eval, State.get_set?_ne hS1D hT1, hSize1_5]
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = g1) ?_ <|
        Stmt.seq_spec (M := fun s st => heap.Fits need ∧ s = heap.allocateStore initial need 1 ∧
          st = g2) ?_ ?_
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨hs, hst⟩
        subst s st
        exact ⟨r, s5, g1, hREval, hG1, rfl, rfl⟩
      · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
          (by simpa [hImports] using hAlloc) rfl).mono ?_ fun _ _ h => h
        rintro s st ⟨hs, hst⟩
        subst s st
        refine ⟨[.i64 r], g1, _, by simp [Expr.evalResults, Expr.eval, State.get_set?_same hG1],
          fun env => alloc_spec_or_abort hMemory32 hImports hAlloc env heap initial r hHeap hR2
            hCap, ?_⟩
        rintro s' out ⟨hFits, hs', hOut⟩
        rw [hNeedDef] at hFits hs' hOut
        exact ⟨g2, by simp [hOut, State.setAll, hG2], hFits, hs', rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨hFits, hs, hst⟩
        subst s st
        exact ⟨UInt64.ofNat 0, g2, g3, by simp [Expr.eval], hG3, .inr ⟨hFits, rfl, rfl⟩⟩
    · rintro s st ⟨hs, hst⟩
      subst s st
      have hNeedValue : ((UInt64.ofNat (xs.size + ys.size) + 1) * 8).toNat =
          8 * (xs.size + ys.size + 1) := by
        simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      by_cases hFit : 8 * (xs.size + ys.size + 1) ≤ capacityAt initial p1
      · refine ⟨true, s5, ?_, rfl, rfl, hFit⟩
        simp only [Expr.eval, hLimit5, hCap5, U64Op.apply, Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, reduceCtorEq, or_self, ite_false, Option.some.injEq, Prod.mk.injEq,
          and_true, decide_eq_true_eq]
        rw [UInt64.le_iff_toNat_le, hNeedValue, hcNat]
        exact hFit
      · refine ⟨false, s5, ?_, rfl, rfl⟩
        simp only [Expr.eval, hLimit5, hCap5, U64Op.apply, Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, reduceCtorEq, or_self, ite_false, Option.some.injEq, Prod.mk.injEq,
          and_true, decide_eq_false_iff_not]
        rw [UInt64.le_iff_toNat_le, hNeedValue, hcNat]
        exact hFit
  apply Triple.of_forall
  rintro s st (⟨hs, hst, hFit⟩ | ⟨hFits, hs, hst⟩)
  · subst s st
    exact Stmt.appendInPlace_spec hLocals0 hBelow0 hSrc1 hSrc2 hSrcBelow1 hSrcBelow2 hRoom hHeap
      hXs hYs hApart hSize hFit hFT2 hP1 hP2
      (by rw [State.get_set?_ne hDI hT2, State.get_set?_same hT1])
      (by rw [State.get_set?_ne hLI hT2, State.get_set?_ne hLD hT1, hLimit5])
      (State.get_set?_same hT2)
      (by rw [State.get_set?_ne hS1I hT2, State.get_set?_ne hS1D hT1, hSize1_5])
  · subst s st
    exact Stmt.appendGrow_spec hImports hRelease hLocals0 hBelow0 hSrc1 hSrc2 hSrcBelow1
      hSrcBelow2 hRoom hHeap hXs hYs hSize hFits hNeed hFG3 hP1 hP2
      (by rw [State.get_set?_ne hDI hG3, State.get_set?_same hG2])
      (by rw [State.get_set?_ne hLI hG3, State.get_set?_ne hLD hG2, State.get_set?_ne hLC hG1,
        hLimit5])
      (State.get_set?_same hG3)
      (by rw [State.get_set?_ne hS1I hG3, State.get_set?_ne hS1D hG2, State.get_set?_ne hS1C hG1,
        hSize1_5])

/-- `Stmt.append` with the temporary `t` at local `src1`, which it consumes, and a borrowed
array `ys` at local `src2`, apart from `t`'s block, leaves `t.2 ++ ys` in a new temporary at
the head of the list, in place of `t`. -/
theorem Live.append {typeIdx releaseType scratch dst size1 size2 limit index cap src1 src2 : Nat}
    {moved : List UInt64} (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hAlloc : m.funcs[0]? = some (allocFunction typeIdx))
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    (hLocals : [dst, size1, size2, limit, index, cap].Nodup)
    (hBelow : ∀ j ∈ [dst, size1, size2, limit, index, cap], j < scratch)
    (hSrc1 : src1 ∉ [dst, size1, size2, limit, index, cap])
    (hSrc2 : src2 ∉ [dst, size1, size2, limit, index, cap])
    (hSrcBelow1 : src1 < scratch) (hSrcBelow2 : src2 < scratch) {before : State}
    (hRoom : scratch < before.params.length + before.locals.length)
    {heap0 heap : Heap} {initial store : Store Unit} {pre post : List (UInt64 × Array UInt64)}
    {t : UInt64 × Array UInt64} (hLive : Live heap0 initial moved heap store (pre ++ t :: post))
    (hCap : initial.memoryCap m 0 ≤ 65535) {p2 : UInt64} {ys : Array UInt64}
    (hYs : heap.Borrowed store p2 ys)
    (hApart : regionsDisjoint (p2.toNat, 8 * (ys.size + 1)) (block store t.1))
    (hP1 : before.get src1 = some (.i64 t.1)) (hP2 : before.get src2 = some (.i64 p2)) :
    Triple m (.append dst size1 size2 limit index cap src1 src2) scratch
      (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p, Live heap0 initial moved heap' s ((p, t.2 ++ ys) :: (pre ++ post)) ∧
        State.Frame scratch [dst, size1, size2, limit, index, cap] before st ∧
        st.get dst = some (.i64 p)) := by
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
      · exact hCross u hu t List.mem_cons_self
      · exact regionsDisjoint_symm (hTPost u hu)
  refine (Stmt.append_spec hMemory32 hImports hAlloc hRelease hLocals hBelow hSrc1 hSrc2
    hSrcBelow1 hSrcBelow2 hRoom hLive.at_ (hLive.cap hCap) (hLive.tempsOwned t hT) hYs hApart
    hP1 hP2).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap', p, hFrame, hDst, hAt', hOwnedP, hCaps', hKeepB, hKeepO⟩
  have hKeepT : ∀ u ∈ pre ++ post, heap'.Owned s u.1 u.2 ∧ block s u.1 = block store u.1 ∧
      regionsDisjoint (block store u.1) (block s p) := fun u hu =>
    have h := hKeepO u.1 u.2 (hLive.tempsOwned u (hRest u hu)) (hApartT u hu)
    ⟨h.1, block_eq h.2.1, h.2.2⟩
  have hOwnedKeep : ∀ q ws, heap0.Owned initial q ws → Apart initial moved (block initial q) →
      heap'.Owned s q ws ∧ capacityAt s q = capacityAt initial q ∧
        regionsDisjoint (block initial q) (block s p) := fun q ws h hA => by
    obtain ⟨hOwned, hCapacity⟩ := hLive.owned q ws h hA
    have hD := hLive.apartO t hT q ws h hA
    rw [← block_eq hCapacity] at hD
    obtain ⟨hOwned', hCapacity', hNew⟩ := hKeepO q ws hOwned hD
    rw [block_eq hCapacity] at hNew
    exact ⟨hOwned', hCapacity'.trans hCapacity, hNew⟩
  refine ⟨heap', p, ⟨hAt', hCaps'.trans hLive.caps,
    fun q ws h hA => (hKeepB q ws (hLive.borrowed q ws h hA) (hLive.apartB t hT q ws h hA)).1,
    fun q ws h hA => ⟨(hOwnedKeep q ws h hA).1, (hOwnedKeep q ws h hA).2.1⟩,
    fun u hu => ?_, fun u hu q ws h hA => ?_, fun u hu q ws h hA => ?_, ?_⟩, hFrame, hDst⟩
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact hOwnedP
    · exact (hKeepT u hu).1
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact (hKeepB q ws (hLive.borrowed q ws h hA) (hLive.apartB t hT q ws h hA)).2
    · rw [(hKeepT u hu).2.1]; exact hLive.apartB u (hRest u hu) q ws h hA
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact (hOwnedKeep q ws h hA).2.2
    · rw [(hKeepT u hu).2.1]; exact hLive.apartO u (hRest u hu) q ws h hA
  · refine List.pairwise_cons.mpr ⟨fun u hu => ?_, ?_⟩
    · rw [(hKeepT u hu).2.1]
      exact regionsDisjoint_symm (hKeepT u hu).2.2
    refine List.Pairwise.imp_of_mem (fun {u v} hu hv h => ?_)
      (List.pairwise_append.mpr ⟨hPre, hPost, fun a ha b hb => hCross a ha b
        (List.mem_cons_of_mem _ hb)⟩)
    rw [(hKeepT u hu).2.1, (hKeepT v hv).2.1]
    exact h

end Project.IR
