import Project.IR.Append
import Project.Pipeline.Records

/-!
The templates that update an owned array in its own block, so that the caller's array becomes
the result: `set!` writes one element; `eraseIdxIfInBounds` moves the later elements down by one
and then shortens the length; and `insertIdx!` moves the later elements up by one, from the top
down, after moving the array to a larger block when its own is full.  `Stmt.fill_inv` and
`Stmt.shiftUp_inv` prove their loops under an invariant of the store.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Writing `v` into element `k` of an array keeps its length and its other elements. -/
theorem arrayAt_set {store : Store Unit} {p v : UInt64} {xs : Array UInt64} {k : Nat}
    (h : UInt64Array.At store p xs) (hk : k < xs.size) :
    UInt64Array.At
      { store with mem := store.mem.write64 (p + UInt64.ofNat (8 * (k + 1))).toUInt32 v } p
      (xs.set! k v) := by
  have hSize : (xs.set! k v).size = xs.size := by simp
  have hAddr := h.elementAddress_toNat k hk
  have hPtr := h.pointerAddress_toNat
  refine ⟨by rw [hSize]; exact h.1, by rw [hSize, Wasm.Mem.write64_pages]; exact h.2.1, ?_, ?_⟩
  · rw [hSize, Memory.read64_write64_disjoint _ _ _ _ (by rw [hAddr, hPtr]; omega)]
    exact h.lengthRead
  · intro i hi
    rw [hSize] at hi
    by_cases hik : i = k
    · subst hik
      rw [Memory.read64_write64]
      simp [Array.set!, Array.setIfInBounds, hk]
    · rw [Memory.read64_write64_disjoint _ _ _ _
        (by rw [hAddr, h.elementAddress_toNat i hi]; omega), h.elementRead i hi]
      simp [Array.set!, Array.setIfInBounds, hk, Array.getElem_set, Ne.symm hik]

/-- Writes the word in local `v` into element `k`, the word in local `k`, of the array at local
`src`, when `k` is below the array's length, which local `size` receives. -/
def Stmt.setInPlace (src size k v : Nat) : Stmt :=
  .seq (.arraySize size src) <|
  .ite (.ltU (.get k) (.get size))
    (.store (.bin .add (.get src) (.bin .mul (.bin .add (.get k) (.const 1)) (.const 8))) (.get v))
    .skip


/-- Writes inside the block of an owned array that leave it holding `ys`, which fit its
capacity, give `Stmt.AppendPost` with the array's own pointer: the allocator invariant, the
array owned, and every array apart from its block kept. -/
theorem Stmt.AppendPost.inPlace {heap : Heap} {initial store : Store Unit} {before state : State}
    {scratch : Nat} {locals : List Nat} {dst : Nat} {p : UInt64} {xs ys : Array UInt64}
    (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs)
    (hWrites : Memory.WritesRange initial store p.toNat (p.toNat + capacityAt initial p))
    (hValues : UInt64Array.At store p ys) (hFit : 8 * (ys.size + 1) ≤ capacityAt initial p)
    (hFrame : State.Frame scratch locals before state) (hDst : state.get dst = some (.i64 p)) :
    Stmt.AppendPost heap initial before scratch locals dst p ys store state := by
  have hBase := hOwned.base
  have hGlobals : store.globals = initial.globals := by rw [hWrites.1]
  obtain ⟨hOwned', hCapacity⟩ := hOwned.rewrite (store' := store)
    ⟨hGlobals, hWrites.2.1, fun a ha => hWrites.2.2 a ha⟩ hValues hFit
  have hBlock : block store p = block initial p := block_eq hCapacity
  -- Bytes of a region apart from the block keep their values.
  have hKeep : ∀ r : Nat × Nat, regionsDisjoint r (block initial p) →
      ∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a :=
    fun r hr a hLow hHigh => hWrites.2.2 a (by simp only [regionsDisjoint, block] at hr; omega)
  have hRegion := hOwned.region
  refine ⟨heap, p, hFrame, hDst, hHeap.writesApart hWrites fun node hNode => ?_, hOwned',
    by rw [hWrites.1], fun q ws hq hApart => ⟨hq.keep (le_of_eq hWrites.2.1.symm)
      (hKeep _ hApart) hq.region, by rw [hBlock]; exact hApart⟩,
    fun q ws hq hApart => ?_⟩
  · have := hOwned.separate node hNode
    simp only [regionsDisjoint] at this ⊢
    omega
  · obtain ⟨hq', hCap⟩ := hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ hApart) hq.region
    exact ⟨hq', hCap, by rw [hBlock]; exact hApart⟩

/-- `set!` in place: with the array at local `src` owned and the position and value in locals
`k` and `v`, the template leaves the owned array updated at the same pointer, and local `size`
holds the old length. -/
theorem Stmt.setInPlace_spec {scratch src size k v : Nat} {initial : Store Unit} {before : State}
    {heap : Heap} {p kw vw : UInt64} {xs : Array UInt64}
    (hSizeBelow : size < scratch) (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hSrc : before.get src = some (.i64 p)) (hK : before.get k = some (.i64 kw))
    (hV : before.get v = some (.i64 vw)) (hSrcNe : src ≠ size) (hKNe : k ≠ size)
    (hVNe : v ≠ size) (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs) :
    Triple m (Stmt.setInPlace src size k v) scratch
      (fun store state => store = initial ∧ state = before)
      (Stmt.AppendPost heap initial before scratch [size] src p (xs.set! kw.toNat vw)) := by
  have hArray := hOwned.values
  have hBase := hOwned.base
  have hCap := hOwned.capacity
  have hAddress := hOwned.address
  have hFit32 := hArray.1
  obtain ⟨s1, hSet⟩ := State.exists_set? (state := before) (index := size)
    (.i64 (UInt64.ofNat xs.size)) (by omega)
  have hFrame1 : State.Frame scratch [size] before s1 :=
    (State.Frame.refl _ _ before).set? hSet (.inl (by simp))
  have hSrc1 : s1.get src = some (.i64 p) := (State.get_set?_ne hSrcNe hSet).trans hSrc
  have hK1 : s1.get k = some (.i64 kw) := (State.get_set?_ne hKNe hSet).trans hK
  have hV1 : s1.get v = some (.i64 vw) := (State.get_set?_ne hVNe hSet).trans hV
  have hSize1 : s1.get size = some (.i64 (UInt64.ofNat xs.size)) := State.get_set?_same hSet
  have hSizeLt : xs.size < 536870912 := by omega
  have hSizeNat : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    ((Stmt.arraySize_spec hArray hSrc (by omega)).mono (fun _ _ h => h)
      fun s st ⟨hs, hst⟩ => ⟨hs, by rw [hSet] at hst; exact (Option.some.inj hst).symm⟩) ?_
  by_cases hk : kw.toNat < xs.size
  · have hAddrEq : p + (kw + 1) * 8 = p + UInt64.ofNat (8 * (kw.toNat + 1)) := by
      congr 1
      apply UInt64.toNat.inj
      rw [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by
        simp [UInt64.size]; omega)]
      simp
      omega
    have hElem := hArray.elementAddress_toNat _ hk
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s1)
      (PElse := fun _ _ => False) (Stmt.store_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨p + (kw + 1) * 8, s1, vw, s1, by simp [Expr.eval, hSrc1, hK1, U64Op.apply],
        by simp [Expr.eval, hV1], by rw [hAddrEq]; exact hArray.elementBound _ hk, ?_⟩
      rw [hAddrEq]
      refine Stmt.AppendPost.inPlace hHeap hOwned
        (Memory.WritesRange.write64 _ _ _ _ _ (by rw [hElem]; omega) (by rw [hElem]; omega))
        (arrayAt_set hArray hk) (by simp; omega) hFrame1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨true, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]
  · have hSame : xs.set! kw.toNat vw = xs := by simp [Array.set!, Array.setIfInBounds, hk]
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = s1) Triple.of_false
      (Stmt.skip_spec.mono (fun _ _ h => h) ?_)).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, hst⟩
      subst st
      rw [hSame]
      exact Stmt.AppendPost.inPlace hHeap hOwned (.refl _ _ _) hArray (by omega) hFrame1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨false, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]

/-- The fill loop under an invariant `I` of the index and the store: when each step, from a
store where `I k` holds, leaves a value `w` of the element, an address of element `k` inside
memory, and `I (k + 1)` after `w` is written there, the loop ends with `I n`.  It writes locals
only among `dst`, `limit`, `index`, and `body`'s `writes`. -/
theorem Stmt.fill_inv {scratch dst limit index : Nat} {element : Expr .u64} {body : Stmt}
    {writes : List Nat} {before : State} {start : Store Unit} {ptr : UInt64} {n k0 : Nat}
    (I : Nat → Store Unit → Prop)
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length) (hn : n < 536870912)
    (hk0 : k0 ≤ n) (hStart : I k0 start)
    (hDst : before.get dst = some (.i64 ptr))
    (hLimit : before.get limit = some (.i64 (UInt64.ofNat n)))
    (hIndex : before.get index = some (.i64 (UInt64.ofNat k0)))
    (hStep : ∀ (k : Nat) (store : Store Unit) (state : State), k0 ≤ k → k < n → I k store →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get dst = some (.i64 ptr) → state.get index = some (.i64 (UInt64.ofNat k)) →
      Triple m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∃ w next, element.eval s.mem scratch st = some (w, next) ∧
            (UInt64Array.wordAddress ptr (k + 1)).toNat + 8 ≤ s.mem.pages * 65536 ∧
            I (k + 1) (UInt64Array.writeElement s ptr k w))) :
    Triple m (.fill dst limit index body element) scratch
      (fun store state => store = start ∧ state = before)
      (fun store state => I n store ∧
        State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr) ∧ state.get limit = some (.i64 (UInt64.ofNat n))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDstLimit, hDstIndex⟩, hLimitIndex⟩ := hLocals
  obtain ⟨hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hDstOut : dst ∉ writes := fun h => hApart dst h (by simp)
  have hLimitOut : limit ∉ writes := fun h => hApart limit h (by simp)
  have hIndexOut : index ∉ writes := fun h => hApart index h (by simp)
  let N : UInt64 := UInt64.ofNat n
  have hN : N.toNat = n := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  let Inv : Store Unit → State → Prop := fun store state =>
    ∃ k, k0 ≤ k ∧ k ≤ n ∧ I k store ∧
      State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
      state.get dst = some (.i64 ptr) ∧ state.get limit = some (.i64 N) ∧
      state.get index = some (.i64 (UInt64.ofNat k))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 k) => n - k.toNat
    | _ => 0
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro store state ⟨k, -, -, -, -, -, hLimitGet, hIndexGet⟩
    exact ⟨decide (UInt64.ofNat k < N), state, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨k, hkLow, hk, hI, hFrame, hDstGet, hLimitGet, hIndexGet⟩,
      rfl, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hLess
    refine Stmt.seq_spec (hStep k store current hkLow hLess hI hFrame hDstGet hIndexGet) ?_
    apply Triple.of_forall
    rintro s b ⟨hs, hFrameB, w, t1, hElementEval, hBound, hNext⟩
    subst s
    have hFrameBW : State.Frame scratch ([dst, limit, index] ++ writes) before b :=
      hFrame.trans (hFrameB.weaken fun j hj => List.mem_append_right _ hj)
    have hDstB : b.get dst = some (.i64 ptr) := (hFrameB.get dst hDstBelow hDstOut).trans hDstGet
    have hLimitB : b.get limit = some (.i64 N) :=
      (hFrameB.get limit hLimitBelow hLimitOut).trans hLimitGet
    have hIndexB : b.get index = some (.i64 (UInt64.ofNat k)) :=
      (hFrameB.get index hIndexBelow hIndexOut).trans hIndexGet
    have hFrameT1 := hFrameBW.trans (Expr.eval_frame _ element store.mem scratch b t1 _
      hElementEval)
    have hKeep : ∀ j, j < scratch → t1.get j = b.get j := fun j hj =>
      (Expr.eval_frame [] element store.mem scratch b t1 _ hElementEval).get j hj (by simp)
    obtain ⟨t2, hSetT2⟩ := State.exists_set? (state := t1) (index := index)
      (.i64 (UInt64.ofNat k + 1))
      (by have := hFrameT1.params; have := hFrameT1.locals; omega)
    refine Stmt.seq_spec (M := fun s st => s = UInt64Array.writeElement store ptr k w ∧
        st = t1) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨ptr + (UInt64.ofNat k + 1) * 8, b, w, t1,
        by simp [Expr.eval, hDstB, hIndexB, U64Op.apply], hElementEval, ?_, ?_, rfl⟩
      · rw [element_address]; exact hBound
      · rw [element_address]; rfl
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨UInt64.ofNat k + 1, t1, t2,
        by simp [Expr.eval, hKeep index hIndexBelow, hIndexB, U64Op.apply], hSetT2,
        ⟨k + 1, by omega, hLess, hNext, hFrameT1.set? hSetT2 (Or.inl (by simp)), ?_, ?_, ?_⟩, ?_⟩
      · rw [State.get_set?_ne hDstIndex hSetT2, hKeep dst hDstBelow, hDstB]
      · rw [State.get_set?_ne hLimitIndex hSetT2, hKeep limit hLimitBelow, hLimitB]
      · rw [State.get_set?_same hSetT2]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      · simp only [measure, State.get_set?_same hSetT2, hIndexGet, UInt64.toNat_add,
          UInt64.toNat_ofNat', UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · rintro store state ⟨rfl, rfl⟩
    exact ⟨k0, le_rfl, hk0, hStart, State.Frame.refl _ _ _, hDst, hLimit, hIndex⟩
  · rintro store state ⟨current, ⟨k, -, hk, hI, hFrame, hDstGet, hLimitGet, hIndexGet⟩,
      hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hNotLess
    obtain rfl : k = n := by omega
    exact ⟨hI, hFrame, hDstGet, hLimitGet⟩

/-- The array that erasing element `k` of `xs` passes through after the loop has moved the
elements `k + 1` to `j` down by one: element `i` is element `i + 1` of `xs` for `k ≤ i < j`. -/
def shifted (xs : Array UInt64) (k j : Nat) : Array UInt64 :=
  Array.ofFn (n := xs.size) fun i => if k ≤ i.val ∧ i.val < j then xs[i.val + 1]! else xs[i]

theorem shifted_size (xs : Array UInt64) (k j : Nat) : (shifted xs k j).size = xs.size := by
  simp [shifted]

theorem shifted_start (xs : Array UInt64) (k : Nat) : shifted xs k k = xs := by
  apply Array.ext (by simp [shifted])
  intro i h1 h2
  simp [shifted]

theorem shifted_step (xs : Array UInt64) {k j : Nat} (hkj : k ≤ j) (hj : j + 1 < xs.size) :
    (shifted xs k j).set! j xs[j + 1]! = shifted xs k (j + 1) := by
  apply Array.ext (by simp [shifted])
  intro i h1 h2
  simp only [Array.set!, Array.setIfInBounds, shifted_size, show j < xs.size by omega, dite_true]
  rw [Array.getElem_set]
  simp only [shifted, Array.getElem_ofFn]
  by_cases hij : j = i
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left ⟨hkj, by omega⟩]
  · rw [ite_eq_right hij]
    by_cases hc : k ≤ i ∧ i < j
    · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
    · rw [ite_eq_right hc, ite_eq_right (by omega)]

theorem shifted_get (xs : Array UInt64) {k j : Nat} (hj : j + 1 < xs.size) :
    (shifted xs k j)[j + 1]! = xs[j + 1]! := by
  rw [getElem!_pos _ _ (by simp [shifted_size]; omega)]
  simp [shifted, getElem!_pos xs (j + 1) hj]

theorem shifted_erase (xs : Array UInt64) {k : Nat} (hk : k < xs.size) :
    (shifted xs k (xs.size - 1)).take (xs.size - 1) = xs.eraseIdxIfInBounds k := by
  rw [Array.eraseIdxIfInBounds_eq, dite_eq_left_of_eq_true (eq_true hk)]
  apply Array.ext (by simp [shifted_size, Array.size_eraseIdx])
  intro i h1 h2
  simp only [Array.take, Array.getElem_extract, Nat.zero_add, shifted, Array.getElem_ofFn]
  by_cases hik : i < k
  · rw [Array.getElem_eraseIdx_of_lt hk _ hik, ite_eq_right (by omega)]
    rfl
  · rw [Array.getElem_eraseIdx_of_ge hk _ (by omega), ite_eq_left (by simp at h2; omega),
      getElem!_pos xs (i + 1) (by simp [Array.size_eraseIdx] at h2; omega)]

/-- Writing a shorter length `m` keeps the first `m` elements of an array. -/
theorem arrayAt_shrink {store : Store Unit} {p : UInt64} {ys : Array UInt64} {m : Nat}
    (h : UInt64Array.At store p ys) (hm : m ≤ ys.size) :
    UInt64Array.At { store with mem := store.mem.write64 p.toUInt32 (UInt64.ofNat m) } p
      (ys.take m) := by
  have hSize : (ys.take m).size = m := by simp; omega
  have hPtr := h.pointerAddress_toNat
  refine ⟨by rw [hSize]; have := h.1; omega, by rw [hSize, Wasm.Mem.write64_pages]; have := h.2.1; omega,
    by rw [hSize, Memory.read64_write64], ?_⟩
  intro i hi
  rw [hSize] at hi
  rw [Memory.read64_write64_disjoint _ _ _ _ (by rw [h.elementAddress_toNat i (by omega), hPtr]; omega),
    h.elementRead i (by omega)]
  simp

/-- Removes element `k`, the word in local `k`, of the array at local `src` when `k` is below
its length, which local `size` receives: a loop over local `index` from `k` below local `limit`,
the length less one, moves each later element down by one, and the length word changes last,
since each read checks its position against it. -/
def Stmt.eraseInPlace (src size k limit index : Nat) : Stmt :=
  .seq (.arraySize size src) <|
  .ite (.ltU (.get k) (.get size))
    (.seq (.assign limit (.bin .sub (.get size) (.const 1))) <|
      .seq (.assign index (.get k)) <|
      .seq (.fill src limit index .skip (.read src (.bin .add (.get index) (.const 1)))) <|
      .store (.get src) (.get limit))
    .skip

/-- `eraseIdxIfInBounds` in place: with the array at local `src` owned and the position in local
`k`, the template leaves the owned array without element `k` at the same pointer. -/
theorem Stmt.eraseInPlace_spec {scratch src size k limit index : Nat} {initial : Store Unit}
    {before : State} {heap : Heap} {p kw : UInt64} {xs : Array UInt64}
    (hLocals : [size, limit, index].Nodup) (hBelow : ∀ j ∈ [size, limit, index], j < scratch)
    (hSrc0 : src ∉ [size, limit, index]) (hK0 : k ∉ [size, limit, index])
    (hSrcBelow : src < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hSrc : before.get src = some (.i64 p)) (hK : before.get k = some (.i64 kw))
    (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs) :
    Triple m (Stmt.eraseInPlace src size k limit index) scratch
      (fun store state => store = initial ∧ state = before)
      (Stmt.AppendPost heap initial before scratch [size, limit, index] src p
        (xs.eraseIdxIfInBounds kw.toNat)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals hSrc0 hK0
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hSL, hSI⟩, hLI⟩ := hLocals
  obtain ⟨hSizeBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hArray := hOwned.values
  have hCap := hOwned.capacity
  have hFit32 := hArray.1
  have hBase := hOwned.base
  set n := xs.size with hn
  have hSizeLt : n < 536870912 := by omega
  have hSizeNat : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := size)
    (.i64 (UInt64.ofNat n)) (by omega)
  have hFrame1 : State.Frame scratch [size, limit, index] before s1 :=
    (State.Frame.refl _ _ before).set? hSet1 (.inl (by simp))
  have hLen1 : s1.params.length + s1.locals.length = before.params.length + before.locals.length := by
    rw [hFrame1.params, hFrame1.locals]
  have hSrc1 : s1.get src = some (.i64 p) := (State.get_set?_ne hSrc0.1 hSet1).trans hSrc
  have hK1 : s1.get k = some (.i64 kw) := (State.get_set?_ne hK0.1 hSet1).trans hK
  have hSize1 : s1.get size = some (.i64 (UInt64.ofNat n)) := State.get_set?_same hSet1
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    ((Stmt.arraySize_spec hArray hSrc (by omega)).mono (fun _ _ h => h)
      fun s st ⟨hs, hst⟩ => ⟨hs, by rw [hSet1] at hst; exact (Option.some.inj hst).symm⟩) ?_
  by_cases hk : kw.toNat < n
  · have hSub : (UInt64.ofNat n - 1 : UInt64) = UInt64.ofNat (n - 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSizeNat]; simp; omega),
        hSizeNat, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp
    have hKNat : UInt64.ofNat kw.toNat = kw := UInt64.ofNat_toNat
    obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := limit)
      (.i64 (UInt64.ofNat (n - 1))) (by omega)
    have hFrame2 := hFrame1.set? hSet2 (.inl (by simp))
    obtain ⟨s3, hSet3⟩ := State.exists_set? (state := s2) (index := index) (.i64 kw)
      (by have := hFrame2.params; have := hFrame2.locals; omega)
    have hFrame3 := hFrame2.set? hSet3 (.inl (by simp))
    have hLen3 : s3.params.length + s3.locals.length = before.params.length + before.locals.length := by
      rw [hFrame3.params, hFrame3.locals]
    have hSrc3 : s3.get src = some (.i64 p) := by
      rw [State.get_set?_ne hSrc0.2.2 hSet3, State.get_set?_ne hSrc0.2.1 hSet2, hSrc1]
    have hLimit3 : s3.get limit = some (.i64 (UInt64.ofNat (n - 1))) := by
      rw [State.get_set?_ne hLI hSet3, State.get_set?_same hSet2]
    have hIndex3 : s3.get index = some (.i64 (UInt64.ofNat kw.toNat)) := by
      rw [State.get_set?_same hSet3, hKNat]
    have hSize2 : s2.get size = some (.i64 (UInt64.ofNat n)) := by
      rw [State.get_set?_ne hSL hSet2, hSize1]
    have hK2 : s2.get k = some (.i64 kw) := by
      rw [State.get_set?_ne hK0.2.1 hSet2, hK1]
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s1)
      (PElse := fun _ _ => False) ?_ Triple.of_false).mono ?_ fun _ _ h => h
    rotate_left
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨true, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]
    refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
      Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, hst⟩
      subst st
      exact ⟨UInt64.ofNat (n - 1), s1, s2, by simp [Expr.eval, hSize1, U64Op.apply, hSub],
        hSet2, rfl, rfl⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, hst⟩
      subst st
      exact ⟨kw, s2, s3, by simp [Expr.eval, hK2], hSet3, rfl, rfl⟩
    -- The loop, then the shorter length.
    let I : Nat → Store Unit → Prop := fun j s =>
      UInt64Array.At s p (shifted xs kw.toNat j) ∧
        Memory.WritesRange initial s p.toNat (p.toNat + 8 * (n + 1))
    refine Stmt.seq_spec (Stmt.fill_inv (n := n - 1) (k0 := kw.toNat) (writes := []) I
      (by simp [hSrc0.2.1, hSrc0.2.2, hLI])
      (by simp [hSrcBelow, hLimitBelow, hIndexBelow]) (by simp) (by omega) (by omega) (by omega)
      ⟨by rw [shifted_start]; exact hArray, .refl _ _ _⟩ hSrc3 hLimit3 hIndex3 ?_) ?_
    · intro j store state hkj hj ⟨hAt, hW⟩ hFr hSrcSt hIdx
      refine Stmt.skip_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      have hj1 : j + 1 < xs.size := by omega
      obtain ⟨saved, hSaved⟩ := State.exists_set? (state := state) (index := scratch)
        (.i64 (UInt64.ofNat j + 1)) (by have := hFr.params; have := hFr.locals; omega)
      have hSavedSrc : saved.get src = some (.i64 p) := by
        rw [State.get_set?_ne (by omega) hSaved, hSrcSt]
      have hjNat : (UInt64.ofNat j + 1).toNat = j + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
        simp
        omega
      have hEval := Expr.read_spec (array := src) (scratch := scratch) (state := state)
        (afterPosition := state) (k := UInt64.ofNat j + 1)
        (position := .bin .add (.get index) (.const 1)) hAt
        (by simp [Expr.eval, hIdx, U64Op.apply]) hSaved hSavedSrc
      rw [hjNat, shifted_get xs hj1] at hEval
      refine ⟨rfl, .refl _ _ _, xs[j + 1]!, saved, hEval,
        hAt.elementBound j (by rw [shifted_size]; omega), ?_, ?_⟩
      · have := arrayAt_set (k := j) (v := xs[j + 1]!) hAt (by rw [shifted_size]; omega)
        rw [shifted_step xs hkj hj1] at this
        exact this
      · exact hW.trans (UInt64Array.writeElement_frame store p n j _ hFit32 (by omega))
    apply Triple.of_forall
    rintro sEnd stEnd ⟨⟨hAtEnd, hWEnd⟩, hFrEnd, hSrcEnd, hLimitEnd⟩
    let final : Store Unit :=
      { sEnd with mem := sEnd.mem.write64 p.toUInt32 (UInt64.ofNat (n - 1)) }
    have hPtr32 := hAtEnd.pointerAddress_toNat
    refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    refine ⟨p, stEnd, UInt64.ofNat (n - 1), stEnd, by simp [Expr.eval, hSrcEnd],
      by simp [Expr.eval, hLimitEnd], hAtEnd.lengthBound, ?_⟩
    have hValues := arrayAt_shrink (m := n - 1) hAtEnd (by rw [shifted_size]; omega)
    rw [hn, shifted_erase xs hk] at hValues
    refine Stmt.AppendPost.inPlace hHeap hOwned
      ((hWEnd.trans (Memory.WritesRange.write64 _ _ _ _ _ (by omega) (by omega))).mono
        le_rfl (by omega)) hValues
        (by simp [Array.eraseIdxIfInBounds_eq, show kw.toNat < xs.size from hk, Array.size_eraseIdx]; omega)
      ⟨by rw [hFrEnd.params, hFrame3.params], by rw [hFrEnd.locals, hFrame3.locals], ?_⟩ hSrcEnd
    intro j hj hjNot
    by_cases hjs : j = src
    · subst hjs; rw [hSrcEnd, hSrc]
    · have hj3 := hjNot
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj3
      rw [hFrEnd.get j hj (by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
          omega), hFrame3.get j hj hjNot]
  · have hSame : xs.eraseIdxIfInBounds kw.toNat = xs := by
      rw [Array.eraseIdxIfInBounds_eq, dite_eq_right_iff.mpr fun h => absurd h hk]
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = s1) Triple.of_false
      (Stmt.skip_spec.mono (fun _ _ h => h) ?_)).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, hst⟩
      subst st
      rw [hSame]
      exact Stmt.AppendPost.inPlace hHeap hOwned (.refl _ _ _) hArray (by omega) hFrame1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨false, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]

/-- The loop that moves elements `k` to `index - 1` of the array at local `src` up by one place,
from the top down: while `k` is below `index`, element `index` receives element `index - 1`, and
`index` falls by one. -/
def Stmt.shiftUp (src k index : Nat) : Stmt :=
  .while (.ltU (.get k) (.get index)) <|
    .seq (.store (.bin .add (.get src) (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8)))
        (.read src (.bin .sub (.get index) (.const 1))))
      (.assign index (.bin .sub (.get index) (.const 1)))

/-- With room for one more element in the block of the array at local `src`, whose length is in
local `size`: `Stmt.shiftUp` moves the elements from position `k` on up by one place, `v` goes
into element `k`, and the longer length is written last. -/
def Stmt.insertShift (src size k v index : Nat) : Stmt :=
  .seq (.assign index (.get size)) <|
  .seq (Stmt.shiftUp src k index) <|
  .seq (.store (.bin .add (.get src) (.bin .mul (.bin .add (.get k) (.const 1)) (.const 8)))
    (.get v)) <|
  .store (.get src) (.bin .add (.get size) (.const 1))

/-- Inserts the word in local `v` at position `k`, the word in local `k`, of the array at local
`src`, whose length local `size` receives.  When `k` exceeds the length, the length becomes 0,
Lean's `default`.  When the block has no room for one more element, a block of twice the
capacity, or of the size needed, receives a copy of the array, the old block is released, and
`src` takes the new pointer.  `Stmt.shiftUp` then moves the elements from `k` on up by one place,
`v` goes into element `k`, and the longer length is written last. -/
def Stmt.insertInPlace (src size k v cap dst limit index : Nat) : Stmt :=
  .seq (.arraySize size src) <|
  .ite (.leU (.get k) (.get size))
    (.seq (.load .u64 cap (.bin .sub (.get src) (.const 32))) <|
      .seq (.ite (.leU (.bin .mul (.bin .add (.get size) (.const 2)) (.const 8)) (.get cap)) .skip
        (.seq (.assign limit (.bin .add (.get size) (.const 1))) <|
          .seq (.assign cap (Stmt.appendRequest limit cap)) <|
          .seq (.call 0 [⟨.u64, .get cap⟩] [dst]) <|
          .seq (.assign limit (.get size)) <|
          .seq (.assign index (.const 0)) <|
          .seq (.seq (.store (.get dst) (.get limit)) <|
            .seq (.fill dst limit index .skip (.read src (.get index))) <|
            .ite (.eq (.get dst) (.get src)) .skip (.release src)) <|
          .assign src (.get dst))) <|
      Stmt.insertShift src size k v index)
    (.store (.get src) (.const 0))

/-- `Stmt.shiftUp` under an invariant `J` of the index and the store: when each step from a
store where `J i` holds, with `k < i`, finds an array laid out at the pointer whose element
`i - 1` it reads, an address of element `i` inside memory, and `J (i - 1)` after that element is
written there, the loop ends with `J k`.  It writes only the local `index` below the scratch
locals. -/
theorem Stmt.shiftUp_inv {scratch src k index : Nat} {before : State} {start : Store Unit}
    {ptr kw : UInt64} {n : Nat} (J : Nat → Store Unit → Prop)
    (hSrcIndex : src ≠ index) (hKIndex : k ≠ index) (hSrcBelow : src < scratch)
    (hKBelow : k < scratch) (hIndexBelow : index < scratch)
    (hRoom : scratch < before.params.length + before.locals.length) (hn : n < 536870912)
    (hk : kw.toNat ≤ n) (hStart : J n start)
    (hSrc : before.get src = some (.i64 ptr)) (hK : before.get k = some (.i64 kw))
    (hIndex : before.get index = some (.i64 (UInt64.ofNat n)))
    (hStep : ∀ (i : Nat) (store : Store Unit), kw.toNat < i → i ≤ n → J i store →
      ∃ ys : Array UInt64, UInt64Array.At store ptr ys ∧ i - 1 < ys.size ∧
        (UInt64Array.wordAddress ptr (i + 1)).toNat + 8 ≤ store.mem.pages * 65536 ∧
        J (i - 1) (UInt64Array.writeElement store ptr i ys[i - 1]!)) :
    Triple m (Stmt.shiftUp src k index) scratch
      (fun store state => store = start ∧ state = before)
      (fun store state => J kw.toNat store ∧ State.Frame scratch [index] before state ∧
        state.get index = some (.i64 kw)) := by
  let Inv : Store Unit → State → Prop := fun store state =>
    ∃ i, kw.toNat ≤ i ∧ i ≤ n ∧ J i store ∧ State.Frame scratch [index] before state ∧
      state.get index = some (.i64 (UInt64.ofNat i))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 i) => i.toNat - kw.toNat
    | _ => 0
  have hKeep : ∀ {st : State}, State.Frame scratch [index] before st →
      st.get src = some (.i64 ptr) ∧ st.get k = some (.i64 kw) := fun hF =>
    ⟨(hF.get src hSrcBelow (by simp [hSrcIndex])).trans hSrc,
      (hF.get k hKBelow (by simp [hKIndex])).trans hK⟩
  have hNat : ∀ i, i ≤ n → (UInt64.ofNat i).toNat = i := fun i hi =>
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro store state ⟨i, -, -, -, hF, hI⟩
    exact ⟨decide (kw < UInt64.ofNat i), state, by simp [Expr.eval, (hKeep hF).2, hI]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨i, hki, hin, hJ, hF, hI⟩, rfl, hCondition⟩
    obtain ⟨hSrcS, hKS⟩ := hKeep hF
    simp only [Expr.eval, hKS, hI, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [UInt64.lt_iff_toNat_lt, hNat i hin] at hLess
    obtain ⟨ys, hAt, hSize, hBound, hNext⟩ := hStep i store hLess hin hJ
    obtain ⟨saved, hSaved⟩ := State.exists_set? (state := current) (index := scratch)
      (.i64 (UInt64.ofNat i - 1)) (by have := hF.params; have := hF.locals; omega)
    have hSavedSrc : saved.get src = some (.i64 ptr) := by
      rw [State.get_set?_ne (by omega) hSaved, hSrcS]
    have hSubNat : (UInt64.ofNat i - 1).toNat = i - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hNat i hin]; simp; omega),
        hNat i hin]
      simp
    have hEval := Expr.read_spec (array := src) (scratch := scratch) (state := current)
      (afterPosition := current) (k := UInt64.ofNat i - 1)
      (position := .bin .sub (.get index) (.const 1)) hAt
      (by simp [Expr.eval, hI, U64Op.apply]) hSaved hSavedSrc
    rw [hSubNat] at hEval
    have hFrameSaved : State.Frame scratch [index] before saved :=
      hF.set? hSaved (Or.inr le_rfl)
    obtain ⟨t2, hSetT2⟩ := State.exists_set? (state := saved) (index := index)
      (.i64 (UInt64.ofNat i - 1)) (by have := hFrameSaved.params; have := hFrameSaved.locals; omega)
    refine Stmt.seq_spec (M := fun s st => s = UInt64Array.writeElement store ptr i ys[i - 1]! ∧
        st = saved) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨ptr + (UInt64.ofNat i + 1) * 8, current, ys[i - 1]!, saved,
        by simp [Expr.eval, hSrcS, hI, U64Op.apply], hEval, ?_, ?_⟩
      · rw [element_address]; exact hBound
      · rw [element_address]; exact ⟨rfl, rfl⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨UInt64.ofNat i - 1, saved, t2, ?_, hSetT2,
        ⟨i - 1, by omega, by omega, hNext, hFrameSaved.set? hSetT2 (Or.inl (by simp)), ?_⟩, ?_⟩
      · simp [Expr.eval, State.get_set?_ne (show index ≠ scratch by omega) hSaved, hI,
          U64Op.apply]
      · rw [State.get_set?_same hSetT2]
        congr 2
        apply UInt64.toNat_inj.mp
        rw [hSubNat, hNat (i - 1) (by omega)]
      · simp only [measure, State.get_set?_same hSetT2, hI, hSubNat, hNat i hin]
        omega
  · rintro store state ⟨rfl, rfl⟩
    exact ⟨n, hk, le_rfl, hStart, State.Frame.refl _ _ _, hIndex⟩
  · rintro store state ⟨current, ⟨i, hki, hin, hJ, hF, hI⟩, hCondition⟩
    obtain ⟨-, hKS⟩ := hKeep hF
    simp only [Expr.eval, hKS, hI, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [UInt64.lt_iff_toNat_lt, hNat i hin] at hNotLess
    obtain rfl : i = kw.toNat := by omega
    refine ⟨hJ, hF, ?_⟩
    rw [hI, UInt64.ofNat_toNat]

/-- The array that inserting into `xs` passes through after the elements above `i` have moved up
by one place: element `j` is element `j - 1` of `xs` for `j > i`. -/
def shiftedUp (xs : Array UInt64) (i : Nat) : Array UInt64 :=
  Array.ofFn (n := xs.size) fun j => if j.val ≤ i then xs[j] else xs[j.val - 1]!

theorem shiftedUp_size (xs : Array UInt64) (i : Nat) : (shiftedUp xs i).size = xs.size := by
  simp [shiftedUp]

theorem shiftedUp_of_le (xs : Array UInt64) {i : Nat} (hi : xs.size ≤ i + 1) :
    shiftedUp xs i = xs := by
  apply Array.ext (by simp [shiftedUp])
  intro j h1 h2
  simp only [shiftedUp, Array.getElem_ofFn]
  rw [ite_eq_left (by simp [shiftedUp] at h1; omega)]
  rfl

theorem shiftedUp_step (xs : Array UInt64) {i : Nat} (hi : 0 < i) (hin : i < xs.size) :
    (shiftedUp xs i).set! i xs[i - 1]! = shiftedUp xs (i - 1) := by
  apply Array.ext (by simp [shiftedUp])
  intro j h1 h2
  simp only [Array.set!, Array.setIfInBounds, shiftedUp_size, hin, dite_true]
  rw [Array.getElem_set]
  simp only [shiftedUp, Array.getElem_ofFn]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_right (by omega)]
  · rw [ite_eq_right hij]
    by_cases hc : j ≤ i
    · rw [ite_eq_left hc, ite_eq_left (by omega)]
    · rw [ite_eq_right hc, ite_eq_right (by omega)]

theorem shiftedUp_get (xs : Array UInt64) {i : Nat} (hi : 0 < i) (hin : i ≤ xs.size) :
    (shiftedUp xs i)[i - 1]! = xs[i - 1]! := by
  rw [getElem!_pos _ _ (by simp [shiftedUp_size]; omega), getElem!_pos xs _ (by omega)]
  simp only [shiftedUp, Array.getElem_ofFn]
  rw [ite_eq_left (by omega)]
  rfl

/-- Writing a longer length `ys.size + 1`, with `w` already in the word after the array, gives
the array with `w` pushed. -/
theorem arrayAt_grow {store : Store Unit} {p w : UInt64} {ys : Array UInt64}
    (h : UInt64Array.At store p ys)
    (hw : store.mem.read64 (UInt64Array.wordAddress p (ys.size + 1)) = w)
    (hFit : p.toNat + 8 * (ys.size + 2) ≤ 4294967296)
    (hMem : p.toNat + 8 * (ys.size + 2) ≤ store.mem.pages * 65536) :
    UInt64Array.At { store with mem := store.mem.write64 p.toUInt32 (UInt64.ofNat (ys.size + 1)) }
      p (ys.push w) := by
  have hSize : (ys.push w).size = ys.size + 1 := by simp
  have hPtr := h.pointerAddress_toNat
  refine ⟨by rw [hSize]; omega, by rw [hSize, Wasm.Mem.write64_pages]; omega,
    by rw [hSize, Memory.read64_write64], ?_⟩
  intro i hi
  rw [hSize] at hi
  have hAddr : ((p + UInt64.ofNat (8 * (i + 1))).toUInt32).toNat = p.toNat + 8 * (i + 1) :=
    UInt64Array.wordAddress_toNat (words := ys.size + 2) (by omega) (by omega)
  rw [Memory.read64_write64_disjoint _ _ _ _ (by rw [hAddr, hPtr]; omega)]
  by_cases hin : i < ys.size
  · rw [h.elementRead i hin]
    simp [Array.getElem_push, hin]
  · obtain rfl : i = ys.size := by omega
    rw [show (p + UInt64.ofNat (8 * (ys.size + 1))).toUInt32 =
      UInt64Array.wordAddress p (ys.size + 1) from rfl, hw]
    simp

theorem insert_final (xs : Array UInt64) {k : Nat} (v : UInt64) (hk : k < xs.size) :
    ((shiftedUp xs k).set! k v).push xs[xs.size - 1]! = xs.insertIdx! k v := by
  have hk' : k ≤ xs.size := by omega
  simp only [Array.insertIdx!, hk', dite_true]
  apply Array.ext (by simp [shiftedUp_size, Array.size_insertIdx])
  intro j h1 h2
  rw [Array.getElem_insertIdx, Array.getElem_push]
  simp only [Array.size_set!, shiftedUp_size, Array.size_push] at h1
  by_cases hjn : j < xs.size
  · rw [dite_eq_left (by simp [shiftedUp_size]; omega)]
    simp only [Array.set!, Array.setIfInBounds, shiftedUp_size, hk, dite_true]
    rw [Array.getElem_set]
    simp only [shiftedUp, Array.getElem_ofFn]
    by_cases hjk : j < k
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), dite_eq_left hjk]
      rfl
    · by_cases hjk' : j = k
      · subst hjk'
        rw [ite_eq_left rfl, dite_eq_right (by omega), dite_eq_left rfl]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right hjk, dite_eq_right hjk',
          getElem!_pos xs (j - 1) (by omega)]
  · obtain rfl : j = xs.size := by omega
    rw [dite_eq_right (by simp [shiftedUp_size]), dite_eq_right (by omega), dite_eq_right (by omega),
      getElem!_pos xs (xs.size - 1) (by omega)]

theorem insert_end (xs : Array UInt64) (v : UInt64) : xs.push v = xs.insertIdx! xs.size v := by
  simp only [Array.insertIdx!, le_refl, dite_true]
  exact Array.insertIdx_size_self.symm

theorem insert_out (xs : Array UInt64) {k : Nat} (v : UInt64) (hk : xs.size < k) :
    xs.insertIdx! k v = #[] := by
  simp only [Array.insertIdx!, dite_eq_right (show ¬k ≤ xs.size by omega)]
  rfl

/-- The in-place insert with room: from an owned array at the pointer in local `src` whose block
holds one more element, with its length in local `size`, the position `kw ≤ n` in local `k`, and
the word in local `v`, the template leaves the owned array with `v` inserted at the same
pointer. -/
theorem Stmt.insertShift_spec {scratch src size k v index : Nat} {initial : Store Unit}
    {before : State} {heap : Heap} {p kw vw : UInt64} {xs : Array UInt64}
    (hSrcIndex : src ≠ index) (hKIndex : k ≠ index) (hVIndex : v ≠ index) (hSizeIndex : size ≠ index)
    (hSrcBelow : src < scratch) (hKBelow : k < scratch) (hIndexBelow : index < scratch)
    (hVBelow : v < scratch) (hSizeBelow : size < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hSrc : before.get src = some (.i64 p)) (hSize : before.get size = some (.i64 (UInt64.ofNat xs.size)))
    (hK : before.get k = some (.i64 kw)) (hV : before.get v = some (.i64 vw))
    (hk : kw.toNat ≤ xs.size) (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs)
    (hFit : 8 * (xs.size + 2) ≤ capacityAt initial p) :
    Triple m (Stmt.insertShift src size k v index) scratch
      (fun store state => store = initial ∧ state = before)
      (Stmt.AppendPost heap initial before scratch [index] src p (xs.insertIdx! kw.toNat vw)) := by
  have hArray := hOwned.values
  have hAddress := hOwned.address
  have hBelowTop := hOwned.below
  have hTop := hHeap.top
  have hBase := hOwned.base
  set n := xs.size with hn
  have hn29 : n < 536870912 := by omega
  have hNat : ∀ i, i ≤ n + 1 → (UInt64.ofNat i).toNat = i := fun i hi =>
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hPtr32 := hArray.pointerAddress_toNat
  have hWordAt : ∀ i, i ≤ n + 1 → (UInt64Array.wordAddress p i).toNat = p.toNat + 8 * i :=
    fun i hi => UInt64Array.wordAddress_toNat (words := n + 2) (by omega) (by omega)
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := index)
    (.i64 (UInt64.ofNat n)) (by omega)
  have hFrame1 : State.Frame scratch [index] before s1 :=
    (State.Frame.refl _ _ before).set? hSet1 (.inl (by simp))
  have hGet1 : ∀ j, j ≠ index → s1.get j = before.get j := fun j hj => State.get_set?_ne hj hSet1
  let J : Nat → Store Unit → Prop := fun i s =>
    UInt64Array.At s p (shiftedUp xs i) ∧
      (i < n → s.mem.read64 (UInt64Array.wordAddress p (n + 1)) = xs[n - 1]!) ∧
      Memory.WritesRange initial s p.toNat (p.toNat + 8 * (n + 2))
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
    Stmt.seq_spec (Stmt.shiftUp_inv (n := n) (ptr := p) (kw := kw) J hSrcIndex hKIndex hSrcBelow
      hKBelow hIndexBelow (by rw [hFrame1.params, hFrame1.locals]; omega) hn29 hk
      ⟨by rw [shiftedUp_of_le xs (by omega)]; exact hArray, fun h => absurd h (lt_irrefl _),
        .refl _ _ _⟩
      (by rw [hGet1 src hSrcIndex, hSrc]) (by rw [hGet1 k hKIndex, hK])
      (State.get_set?_same hSet1) ?_) ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨rfl, hst⟩
    subst st
    exact ⟨UInt64.ofNat n, before, s1, by simp [Expr.eval, hSize], hSet1, rfl, rfl⟩
  · intro i s hki hin ⟨hAt, hTopRead, hW⟩
    have hPages : s.mem.pages = initial.mem.pages := hW.2.1
    refine ⟨shiftedUp xs i, hAt, by rw [shiftedUp_size]; omega, ?_, ?_⟩
    · rw [hWordAt (i + 1) (by omega), hPages]; omega
    · rw [shiftedUp_get xs (by omega) hin]
      have hWrite := Memory.WritesRange.write64 s (UInt64Array.wordAddress p (i + 1)) xs[i - 1]!
        p.toNat (p.toNat + 8 * (n + 2)) (by rw [hWordAt (i + 1) (by omega)]; omega)
        (by rw [hWordAt (i + 1) (by omega)]; omega)
      refine ⟨?_, fun _ => ?_, hW.trans hWrite⟩
      · by_cases hi : i < n
        · have := arrayAt_set (k := i) (v := xs[i - 1]!) hAt (by rw [shiftedUp_size]; omega)
          rw [shiftedUp_step xs (by omega) hi] at this
          exact this
        · obtain rfl : i = n := by omega
          have := hAt.write64After (address := UInt64Array.wordAddress p (n + 1))
            (value := xs[n - 1]!) (by rw [shiftedUp_size, hWordAt (n + 1) (by omega)])
          rw [shiftedUp_of_le xs (by omega)] at this
          rw [shiftedUp_of_le xs (by omega)]
          exact this
      · by_cases hi : i < n
        · rw [show (UInt64Array.writeElement s p i xs[i - 1]!).mem.read64
              (UInt64Array.wordAddress p (n + 1)) = s.mem.read64 (UInt64Array.wordAddress p (n + 1))
            from Memory.read64_write64_disjoint _ _ _ _
              (by rw [hWordAt (i + 1) (by omega), hWordAt (n + 1) (by omega)]; omega)]
          exact hTopRead hi
        · obtain rfl : i = n := by omega
          exact Memory.read64_write64 _ _ _
  · apply Triple.of_forall
    rintro s2 st2 ⟨⟨hAt2, hTop2, hW2⟩, hFr2, hIdx2⟩
    have hPages2 : s2.mem.pages = initial.mem.pages := hW2.2.1
    have hFrame2 : State.Frame scratch [index] before st2 := hFrame1.trans hFr2
    have hSrc2 : st2.get src = some (.i64 p) := by
      rw [hFrame2.get src hSrcBelow (by simp [hSrcIndex]), hSrc]
    have hK2 : st2.get k = some (.i64 kw) := by
      rw [hFrame2.get k hKBelow (by simp [hKIndex]), hK]
    have hV2 : st2.get v = some (.i64 vw) := by
      rw [hFrame2.get v hVBelow (by simp [hVIndex]), hV]
    have hSize2 : st2.get size = some (.i64 (UInt64.ofNat n)) := by
      rw [hFrame2.get size hSizeBelow (by simp [hSizeIndex]), hSize]
    have hKNat : UInt64.ofNat kw.toNat = kw := UInt64.ofNat_toNat
    have hElemAddr : (p + (kw + 1) * 8).toUInt32 = UInt64Array.wordAddress p (kw.toNat + 1) := by
      rw [← element_address p kw.toNat, hKNat]
    have hLen : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hNat n (by omega), hNat (n + 1) le_rfl]
      simp
      omega
    let s3 : Store Unit := UInt64Array.writeElement s2 p kw.toNat vw
    have hWrite3 : Memory.WritesRange s2 s3 p.toNat (p.toNat + 8 * (n + 2)) :=
      Memory.WritesRange.write64 s2 _ vw _ _ (by rw [hWordAt (kw.toNat + 1) (by omega)]; omega)
        (by rw [hWordAt (kw.toNat + 1) (by omega)]; omega)
    -- The array after `v` goes into element `k`, and the word after it.
    obtain ⟨ys, w, hYs, hTop3, hSizeYs, hResult⟩ : ∃ (ys : Array UInt64) (w : UInt64),
        UInt64Array.At s3 p ys ∧ s3.mem.read64 (UInt64Array.wordAddress p (n + 1)) = w ∧
        ys.size = n ∧ ys.push w = xs.insertIdx! kw.toNat vw := by
      by_cases hkn : kw.toNat < n
      · refine ⟨(shiftedUp xs kw.toNat).set! kw.toNat vw, xs[n - 1]!,
          arrayAt_set (k := kw.toNat) (v := vw) hAt2 (by rw [shiftedUp_size]; omega), ?_,
          by simp [shiftedUp_size, hn], insert_final xs vw hkn⟩
        rw [show s3.mem.read64 (UInt64Array.wordAddress p (n + 1)) =
            s2.mem.read64 (UInt64Array.wordAddress p (n + 1)) from
          Memory.read64_write64_disjoint _ _ _ _
            (by rw [hWordAt (kw.toNat + 1) (by omega), hWordAt (n + 1) (by omega)]; omega)]
        exact hTop2 hkn
      · obtain hkn' : kw.toNat = n := by omega
        refine ⟨xs, vw, ?_, ?_, rfl, by rw [hkn', hn]; exact insert_end xs vw⟩
        · have := hAt2.write64After (address := UInt64Array.wordAddress p (kw.toNat + 1))
            (value := vw) (by rw [shiftedUp_size, hWordAt (kw.toNat + 1) (by omega)]; omega)
          rw [shiftedUp_of_le xs (by omega)] at this
          exact this
        · show (s2.mem.write64 (UInt64Array.wordAddress p (kw.toNat + 1)) vw).read64
            (UInt64Array.wordAddress p (n + 1)) = vw
          rw [hkn']
          exact Memory.read64_write64 _ _ _
    rw [← hSizeYs] at hTop3
    have hPages3 : s3.mem.pages = initial.mem.pages := by
      show (Wasm.Mem.write64 _ _ _).pages = _
      rw [Wasm.Mem.write64_pages, hPages2]
    have hFinal := arrayAt_grow hYs hTop3 (by rw [hSizeYs]; omega)
      (by rw [hSizeYs, hPages3]; omega)
    rw [hSizeYs, hResult] at hFinal
    have hWrite4 : Memory.WritesRange s3
        { s3 with mem := s3.mem.write64 p.toUInt32 (UInt64.ofNat (n + 1)) } p.toNat
        (p.toNat + 8 * (n + 2)) :=
      Memory.WritesRange.write64 s3 _ _ _ _ (by rw [hPtr32]) (by rw [hPtr32]; omega)
    refine Stmt.seq_spec (M := fun s st => s = s3 ∧ st = st2) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨p + (kw + 1) * 8, st2, vw, st2, by simp [Expr.eval, hSrc2, hK2, U64Op.apply],
        by simp [Expr.eval, hV2], ?_, ?_⟩
      · rw [hElemAddr, hWordAt (kw.toNat + 1) (by omega), hPages2]; omega
      · rw [hElemAddr]; exact ⟨rfl, rfl⟩
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨p, st2, UInt64.ofNat (n + 1), st2, by simp [Expr.eval, hSrc2],
        by rw [← hLen]; simp [Expr.eval, hSize2, U64Op.apply], ?_, ?_⟩
      · rw [hPtr32]; show _ ≤ (Wasm.Mem.write64 _ _ _).pages * 65536
        rw [Wasm.Mem.write64_pages, hPages2]; omega
      · refine Stmt.AppendPost.inPlace hHeap hOwned
          (((hW2.trans hWrite3).trans hWrite4).mono le_rfl (by omega)) hFinal
          (by rw [← hResult, Array.size_push, hSizeYs]; omega) hFrame2 hSrc2

/-- Two array updates in a row: when a first step keeps every array apart from the block at `p`
and leaves them apart from the block at `q`, and a second step from its store and heap gives
`Stmt.AppendPost` for the block at `q`, the two give `Stmt.AppendPost` for the block at `p`, with
the locals of both. -/
theorem Stmt.AppendPost.trans {heap heap1 : Heap} {initial store1 store2 : Store Unit}
    {before mid st2 : State} {scratch : Nat} {locals locals2 : List Nat} {dst : Nat}
    {p q : UInt64} {zs : Array UInt64}
    (hFrame : State.Frame scratch locals before mid)
    (hB1 : ∀ r ws, heap.Borrowed initial r ws →
      regionsDisjoint (r.toNat, 8 * (ws.size + 1)) (block initial p) →
      heap1.Borrowed store1 r ws ∧ regionsDisjoint (r.toNat, 8 * (ws.size + 1)) (block store1 q))
    (hO1 : ∀ r ws, heap.Owned initial r ws → regionsDisjoint (block initial r) (block initial p) →
      heap1.Owned store1 r ws ∧ capacityAt store1 r = capacityAt initial r ∧
        regionsDisjoint (block initial r) (block store1 q))
    (hCaps1 : store1.memoryCaps = initial.memoryCaps)
    (h2 : Stmt.AppendPost heap1 store1 mid scratch locals2 dst q zs store2 st2)
    (hSub : ∀ j ∈ locals2, j ∈ locals) :
    Stmt.AppendPost heap initial before scratch locals dst p zs store2 st2 := by
  obtain ⟨heap2, q2, hF2, hD2, hAt2, hOwned2, hCaps2, hB2, hO2⟩ := h2
  refine ⟨heap2, q2, hFrame.trans (hF2.weaken hSub), hD2, hAt2, hOwned2, hCaps2.trans hCaps1,
    fun r ws hr hA => ?_, fun r ws hr hA => ?_⟩
  · obtain ⟨hr1, hA1⟩ := hB1 r ws hr hA
    exact hB2 r ws hr1 hA1
  · obtain ⟨hr1, hc1, hA1⟩ := hO1 r ws hr hA
    obtain ⟨hr2, hc2, hA2⟩ := hO2 r ws hr1 (by rw [block_eq hc1]; exact hA1)
    rw [block_eq hc1] at hA2
    exact ⟨hr2, hc2.trans hc1, hA2⟩

/-- `Stmt.AppendPost` from a later state, whose frame from the earlier one lies within the
locals. -/
theorem Stmt.AppendPost.frame {heap : Heap} {initial store : Store Unit}
    {before mid st : State} {scratch : Nat} {locals locals2 : List Nat} {dst : Nat}
    {p : UInt64} {zs : Array UInt64} (hFrame : State.Frame scratch locals before mid)
    (h : Stmt.AppendPost heap initial mid scratch locals2 dst p zs store st)
    (hSub : ∀ j ∈ locals2, j ∈ locals) :
    Stmt.AppendPost heap initial before scratch locals dst p zs store st :=
  Stmt.AppendPost.trans (heap1 := heap) (store1 := initial) (q := p) hFrame
    (fun _ _ hr hA => ⟨hr, hA⟩) (fun _ _ hr hA => ⟨hr, rfl, hA⟩) rfl h hSub

/-- `insertIdx!` in place: with the array at local `src` owned and the position and value in
locals `k` and `v`, the template leaves the owned array with the value inserted, at the same
pointer when the block has room and in a new block otherwise, whose pointer `src` then holds. -/
theorem Stmt.insertInPlace_spec {typeIdx releaseType scratch src size k v cap dst limit index : Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {p kw vw : UInt64} {xs : Array UInt64}
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hAlloc : m.funcs[0]? = some (allocFunction typeIdx))
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    (hLocals : [size, cap, dst, limit, index].Nodup)
    (hBelow : ∀ j ∈ [size, cap, dst, limit, index], j < scratch)
    (hSrc0 : src ∉ [size, cap, dst, limit, index]) (hK0 : k ∉ [size, cap, dst, limit, index])
    (hV0 : v ∉ [size, cap, dst, limit, index]) (hKSrc : k ≠ src) (hVSrc : v ≠ src)
    (hSrcBelow : src < scratch) (hKBelow : k < scratch) (hVBelow : v < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hSrc : before.get src = some (.i64 p)) (hK : before.get k = some (.i64 kw))
    (hV : before.get v = some (.i64 vw))
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hOwned : heap.Owned initial p xs) :
    Triple m (Stmt.insertInPlace src size k v cap dst limit index) scratch
      (fun store state => store = initial ∧ state = before)
      (Stmt.AppendPost heap initial before scratch [src, size, cap, dst, limit, index] src p
        (xs.insertIdx! kw.toNat vw)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals hSrc0 hK0 hV0
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hSC, hSD, hSL, hSI⟩, ⟨hCD, hCL, hCI⟩, ⟨hDL, hDI⟩, hLI⟩ := hLocals
  obtain ⟨hSizeBelow, hCapBelow, hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hArray := hOwned.values
  have hCapacity := hOwned.capacity
  have hBase := hOwned.base
  have hAddr := hOwned.address
  set n := xs.size with hn
  have hn29 : n < 536870912 := by have := hArray.1; omega
  have hNat : ∀ i, i ≤ n + 2 → (UInt64.ofNat i).toNat = i := fun i hi =>
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  let L := [src, size, cap, dst, limit, index]
  -- The length.
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := size)
    (.i64 (UInt64.ofNat n)) (by omega)
  have hF1 : State.Frame scratch L before s1 :=
    (State.Frame.refl _ _ before).set? hSet1 (.inl (by simp [L]))
  have hSrc1 : s1.get src = some (.i64 p) := (State.get_set?_ne hSrc0.1 hSet1).trans hSrc
  have hK1 : s1.get k = some (.i64 kw) := (State.get_set?_ne hK0.1 hSet1).trans hK
  have hV1 : s1.get v = some (.i64 vw) := (State.get_set?_ne hV0.1 hSet1).trans hV
  have hSize1 : s1.get size = some (.i64 (UInt64.ofNat n)) := State.get_set?_same hSet1
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    ((Stmt.arraySize_spec hArray hSrc (by omega)).mono (fun _ _ h => h)
      fun s st ⟨hs, hst⟩ => ⟨hs, by rw [hSet1] at hst; exact (Option.some.inj hst).symm⟩) ?_
  by_cases hk : kw.toNat ≤ n
  · have hSizeNat := hNat n (by omega)
    have hPtr32 := hArray.pointerAddress_toNat
    have hMemP := hArray.2.1
    -- The capacity word.
    obtain ⟨c, hc⟩ : ∃ c : UInt64, c = initial.mem.read64 (p - 32).toUInt32 := ⟨_, rfl⟩
    have hcNat : c.toNat = capacityAt initial p := by rw [hc]; rfl
    have hHeader : (p - 32).toUInt32.toNat = p.toNat - 32 := by
      have := headerAddress_toNat (ptr := p) (k := 32) (by simp; omega) (by omega)
      simpa using this
    obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := cap) (.i64 c)
      (by rw [hF1.params, hF1.locals]; omega)
    have hF2 : State.Frame scratch L before s2 := hF1.set? hSet2 (.inl (by simp [L]))
    have hF12 : State.Frame scratch [cap, dst, limit, index] s1 s2 :=
      (State.Frame.refl _ _ s1).set? hSet2 (.inl (by simp))
    have hSrc2 : s2.get src = some (.i64 p) := (State.get_set?_ne hSrc0.2.1 hSet2).trans hSrc1
    have hK2 : s2.get k = some (.i64 kw) := (State.get_set?_ne hK0.2.1 hSet2).trans hK1
    have hV2 : s2.get v = some (.i64 vw) := (State.get_set?_ne hV0.2.1 hSet2).trans hV1
    have hSize2 : s2.get size = some (.i64 (UInt64.ofNat n)) :=
      (State.get_set?_ne hSC hSet2).trans hSize1
    have hCap2 : s2.get cap = some (.i64 c) := State.get_set?_same hSet2
    let M : Store Unit → State → Prop := fun s st =>
      Stmt.AppendPost heap initial before scratch L src p xs s st ∧
        (∃ q, st.get src = some (.i64 q) ∧ 8 * (n + 2) ≤ capacityAt s q) ∧
        st.get size = some (.i64 (UInt64.ofNat n)) ∧ st.get k = some (.i64 kw) ∧
        st.get v = some (.i64 vw)
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s1)
      (PElse := fun _ _ => False) ?_ Triple.of_false).mono ?_ fun _ _ h => h
    rotate_left
    · rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨true, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.le_iff_toNat_le, hSizeNat, hk]
    refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
      Stmt.seq_spec (M := M) ?_ ?_
    · refine Stmt.load_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨p - 32, s1, s2, by simp [Expr.eval, hSrc1, U64Op.apply], by omega, ?_, rfl, rfl⟩
      rw [← hc]
      exact hSet2
    · refine (Stmt.ite_spec
        (PThen := fun s st => s = initial ∧ st = s2 ∧ 8 * (n + 2) ≤ capacityAt initial p)
        (PElse := fun s st => s = initial ∧ st = s2 ∧ ¬8 * (n + 2) ≤ capacityAt initial p)
        ?_ ?_).mono ?_ fun _ _ h => h
      · refine Stmt.skip_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨hs, hst, hRm⟩
        subst s st
        exact ⟨Stmt.AppendPost.inPlace hHeap hOwned (.refl _ _ _) hArray (by omega) hF2 hSrc2,
          ⟨p, hSrc2, hRm⟩, hSize2, hK2, hV2⟩
      · apply Triple.of_forall
        rintro s0 st0 ⟨hs, hst, hRm⟩
        subst s0 st0
        -- The growth path: a request, `alloc`, a copy into the new block, and `src` moved.
        have hLen1 : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, hSizeNat, hNat (n + 1) (by omega)]
          simp
          omega
        obtain ⟨g1, hG1⟩ := State.exists_set? (state := s2) (index := limit)
          (.i64 (UInt64.ofNat (n + 1))) (by rw [hF2.params, hF2.locals]; omega)
        have hFG1 := hF12.set? hG1 (.inl (by simp))
        have hLimitG1 : g1.get limit = some (.i64 (UInt64.ofNat (n + 1))) := State.get_set?_same hG1
        have hCapG1 : g1.get cap = some (.i64 c) := by rw [State.get_set?_ne hCL hG1, hCap2]
        obtain ⟨r, hREval, hR1, hR2⟩ := appendRequest_eval (mem := initial.mem) (scratch := scratch)
          (total := n + 1) (by omega) (by rw [hcNat]; omega) hLimitG1 hCapG1
        generalize hNeedDef : allocSize r = need
        have hNeed : 8 * (n + 2) ≤ need.toNat := by
          rw [← hNeedDef]; exact hR1.trans (le_allocSize hR2)
        obtain ⟨g2, hG2⟩ := State.exists_set? (state := g1) (index := cap) (.i64 r)
          (by rw [hFG1.params, hFG1.locals, hF1.params, hF1.locals]; omega)
        have hFG2 := hFG1.set? hG2 (.inl (by simp))
        obtain ⟨g3, hG3⟩ := State.exists_set? (state := g2) (index := dst)
          (.i64 (FixedArrayAllocate.root heap.top need heap.free))
          (by rw [hFG2.params, hFG2.locals, hF1.params, hF1.locals]; omega)
        have hFG3 := hFG2.set? hG3 (.inl (by simp))
        obtain ⟨g4, hG4⟩ := State.exists_set? (state := g3) (index := limit)
          (.i64 (UInt64.ofNat n)) (by rw [hFG3.params, hFG3.locals, hF1.params, hF1.locals]; omega)
        have hFG4 := hFG3.set? hG4 (.inl (by simp))
        obtain ⟨g5, hG5⟩ := State.exists_set? (state := g4) (index := index) (.i64 (UInt64.ofNat 0))
          (by rw [hFG4.params, hFG4.locals, hF1.params, hF1.locals]; omega)
        have hFG5 := hFG4.set? hG5 (.inl (by simp))
        have hSizeG2 : g2.get size = some (.i64 (UInt64.ofNat n)) := by
          rw [State.get_set?_ne hSC hG2, State.get_set?_ne hSL hG1, hSize2]
        have hCapG2 : g2.get cap = some (.i64 r) := State.get_set?_same hG2
        have hDstG5 : g5.get dst = some (.i64 (FixedArrayAllocate.root heap.top need heap.free)) := by
          rw [State.get_set?_ne hDI hG5, State.get_set?_ne hDL hG4, State.get_set?_same hG3]
        have hLimitG5 : g5.get limit = some (.i64 (UInt64.ofNat n)) := by
          rw [State.get_set?_ne hLI hG5, State.get_set?_same hG4]
        have hIndexG5 : g5.get index = some (.i64 (UInt64.ofNat 0)) := State.get_set?_same hG5
        refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = g1) ?_ <|
          Stmt.seq_spec (M := fun s st => s = initial ∧ st = g2) ?_ <|
          Stmt.seq_spec (M := fun s st => heap.Fits need ∧ s = heap.allocateStore initial need 1 ∧
            st = g3) ?_ <|
          Stmt.seq_spec (M := fun s st => heap.Fits need ∧ s = heap.allocateStore initial need 1 ∧
            st = g4) ?_ <|
          Stmt.seq_spec (M := fun s st => heap.Fits need ∧ s = heap.allocateStore initial need 1 ∧
            st = g5) ?_ <|
          Stmt.seq_spec (M := fun s st =>
            Stmt.AppendPost heap initial s1 scratch [cap, dst, limit, index] dst p xs s st ∧
              ∃ q, st.get dst = some (.i64 q) ∧ need.toNat ≤ capacityAt s q) ?_ ?_
        · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
          rintro s st ⟨hs, hst⟩
          subst s st
          exact ⟨UInt64.ofNat (n + 1), s2, g1, by rw [← hLen1]; simp [Expr.eval, hSize2, U64Op.apply],
            hG1, rfl, rfl⟩
        · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
          rintro s st ⟨hs, hst⟩
          subst s st
          exact ⟨r, g1, g2, hREval, hG2, rfl, rfl⟩
        · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
            (by simpa [hImports] using hAlloc) rfl).mono ?_ fun _ _ h => h
          rintro s st ⟨hs, hst⟩
          subst s st
          refine ⟨[.i64 r], g2, _, by simp [Expr.evalResults, Expr.eval, hCapG2],
            fun env => alloc_spec_or_abort hMemory32 hImports hAlloc env heap initial r hHeap hR2
              hCap, ?_⟩
          rintro s' out ⟨hFits, hs', hOut⟩
          rw [hNeedDef] at hFits hs' hOut
          exact ⟨g3, by simp [hOut, State.setAll, hG3], hFits, hs', rfl⟩
        · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
          rintro s st ⟨hFits, hs, hst⟩
          subst s st
          refine ⟨UInt64.ofNat n, g3, g4, ?_, hG4, hFits, rfl, rfl⟩
          simp [Expr.eval, State.get_set?_ne hSD hG3, hSizeG2]
        · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
          rintro s st ⟨hFits, hs, hst⟩
          subst s st
          exact ⟨UInt64.ofNat 0, g4, g5, by simp [Expr.eval], hG5, hFits, rfl, rfl⟩
        · apply Triple.of_forall
          rintro s st ⟨hFits, hs, hst⟩
          subst s st
          have hXApart := hOwned.disjoint_allocated hHeap need
          have hXA := hOwned.allocate 1 hHeap hFits
          have hBlock := hHeap.allocate_block 1 hFits
          have hCapacityA := allocated_capacity need heap.free
          have hBlockAddress := hBlock.address
          have hBlockBase := hBlock.base
          refine Stmt.growFill_spec (locals := [cap, dst, limit, index]) (before := s1) (start := g5)
            (all := xs) (element := .read src (.get index)) hImports hRelease
            (by simp [hDL, hDI, hLI]) (by simp [hDstBelow, hLimitBelow, hIndexBelow])
            (by simp) (by simp [hSrc0.2.1, hSrc0.2.2.1, hSrc0.2.2.2.1, hSrc0.2.2.2.2])
            hSrcBelow (by rw [hF1.params, hF1.locals]; omega) hHeap hOwned hn29 hFits (by omega)
            hFG5 hSrc1 hDstG5 hLimitG5 hIndexG5 fun j hj s st hW hFk hI => ?_
          have hXv : UInt64Array.At s p xs := by
            refine hXA.values.writesRange hW ?_
            simp only [regionsDisjoint] at hXApart
            omega
          have hSrcSt : st.get src = some (.i64 p) := by
            rw [hFk.get src hSrcBelow (by simp [hSrc0.2.2.1, hSrc0.2.2.2.1, hSrc0.2.2.2.2]),
              State.get_set?_ne hSrc0.2.2.2.2 hG5, State.get_set?_ne hSrc0.2.2.2.1 hG4,
              State.get_set?_ne hSrc0.2.2.1 hG3, State.get_set?_ne hSrc0.2.1 hG2,
              State.get_set?_ne hSrc0.2.2.2.1 hG1, hSrc2]
          obtain ⟨saved, hSaved⟩ := State.exists_set? (state := st) (index := scratch)
            (.i64 (UInt64.ofNat j)) (by
              have := hFk.params; have := hFk.locals
              have := hFG5.params; have := hFG5.locals
              rw [hF1.params, hF1.locals] at *; omega)
          have hEval := Expr.read_spec (array := src) (scratch := scratch) (state := st)
            (afterPosition := st) (k := UInt64.ofNat j) (position := .get index) hXv
            (by simp [Expr.eval, hI]) hSaved (by rw [State.get_set?_ne (by omega) hSaved, hSrcSt])
          rw [hNat j (by omega), getElem!_pos xs j hj] at hEval
          exact ⟨saved, hEval⟩
        · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
          rintro s st ⟨⟨heap1, q, hFr, hDq, hAt, hOw, hCaps, hB, hO⟩, q', hq', hcq⟩
          obtain rfl : q' = q := by rw [hDq] at hq'; exact (Value.i64.inj (Option.some.inj hq')).symm
          obtain ⟨st', hSt'⟩ := State.exists_set? (state := st) (index := src) (.i64 q')
            (by have := hFr.params; have := hFr.locals; rw [hF1.params, hF1.locals] at *; omega)
          have hKeep : ∀ j, j < scratch → j ∉ [cap, dst, limit, index] → j ≠ src →
              st'.get j = s1.get j := fun j hj hjn hjs => by
            rw [State.get_set?_ne hjs hSt', hFr.get j hj hjn]
          refine ⟨q', st, st', by simp [Expr.eval, hDq], hSt',
            ⟨heap1, q', (hF1.trans (hFr.weaken fun j hj => by simp [L] at hj ⊢; omega)).set? hSt'
              (.inl (by simp [L])), State.get_set?_same hSt', hAt, hOw, hCaps, hB, hO⟩,
            ⟨q', State.get_set?_same hSt', by omega⟩, ?_, ?_, ?_⟩
          · rw [hKeep size hSizeBelow (by simp [hSC, hSD, hSL, hSI]) (Ne.symm hSrc0.1), hSize1]
          · rw [hKeep k hKBelow (by simp [hK0.2.1, hK0.2.2.1, hK0.2.2.2.1, hK0.2.2.2.2]) hKSrc, hK1]
          · rw [hKeep v hVBelow (by simp [hV0.2.1, hV0.2.2.1, hV0.2.2.2.1, hV0.2.2.2.2]) hVSrc, hV1]
      · rintro s st ⟨hs, hst⟩
        subst s st
        have hNeedV : ((UInt64.ofNat n + 2) * 8).toNat = 8 * (n + 2) := by
          rw [UInt64.toNat_mul, UInt64.toNat_add, hSizeNat]
          simp
          omega
        by_cases hRm : 8 * (n + 2) ≤ capacityAt initial p
        · refine ⟨true, s2, ?_, rfl, rfl, hRm⟩
          simp [Expr.eval, hSize2, hCap2, U64Op.apply, UInt64.le_iff_toNat_le, hNeedV, hcNat, hRm]
        · refine ⟨false, s2, ?_, rfl, rfl, hRm⟩
          simp [Expr.eval, hSize2, hCap2, U64Op.apply, UInt64.le_iff_toNat_le, hNeedV, hcNat, hRm]
    · apply Triple.of_forall
      rintro s st ⟨⟨heap1, q1, hFr, hDq, hAt, hOw, hCaps, hB, hO⟩, ⟨q, hq, hcq⟩, hsz, hkk, hvv⟩
      obtain rfl : q1 = q := by rw [hDq] at hq; exact Value.i64.inj (Option.some.inj hq)
      refine (Stmt.insertShift_spec (initial := s) (before := st) (heap := heap1) (p := q1)
        (xs := xs) (Ne.symm hSrc0.2.2.2.2 |>.symm) (Ne.symm hK0.2.2.2.2 |>.symm)
        (Ne.symm hV0.2.2.2.2 |>.symm) hSI hSrcBelow hKBelow hIndexBelow hVBelow hSizeBelow
        (by rw [hFr.params, hFr.locals]; omega) hDq hsz hkk hvv hk hAt hOw hcq).mono
          (fun _ _ h => h) fun s' st' h => ?_
      exact Stmt.AppendPost.trans hFr hB hO hCaps h (by simp)
  · -- Past the end: the length becomes 0.
    have hPtr32 := hArray.pointerAddress_toNat
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = s1) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨p, s1, 0, s1, by simp [Expr.eval, hSrc1], by simp [Expr.eval], hArray.lengthBound,
        ?_⟩
      have hValues := arrayAt_shrink (m := 0) hArray (Nat.zero_le _)
      rw [show xs.take 0 = #[] by simp, ← insert_out xs vw (by omega : xs.size < kw.toNat)] at hValues
      exact Stmt.AppendPost.inPlace hHeap hOwned
        ((Memory.WritesRange.write64 _ _ _ _ _ (by rw [hPtr32]) (by rw [hPtr32])).mono
          le_rfl (by omega)) hValues (by rw [insert_out xs vw (by omega)]; simp; omega) hF1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨false, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.le_iff_toNat_le, hNat n (by omega), hk]

end Project.IR
