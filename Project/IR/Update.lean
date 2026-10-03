import Project.IR.Append
import Project.Pipeline.Records

/-!
The templates that update an owned array in its own block, so that the caller's array becomes
the result: `set!` writes one element, and `eraseIdxIfInBounds` moves the later elements down
by one and then shortens the length.  `Stmt.fill_inv` proves their loops under an invariant.
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

end Project.IR
