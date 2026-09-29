import Project.IR.ArrayLiteral
import Project.IR.Loop
import LeanExe.Build

/-!
The rule lemma for the compiler's copying template.  The compiler implements
Lean's array operations and `LeanExe.build` by allocating a new array and storing
each element, computed by an expression of its index.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Local `dst` receives a new array of `count` elements, with the count held in
local `limit`; element `i` is the value of `element` while local `index` holds
`i`. -/
def Stmt.build (dst limit index : Nat) (count element : Expr .u64) : Stmt :=
  .seq (.assign limit count) <|
  .seq (.call 1 [.bin .mul (.bin .add (.get limit) (.const 1)) (.const 8)] (some dst)) <|
  .seq (.store (.get dst) (.get limit)) <|
  .seq (.assign index (.const 0)) <|
  .while (.ltU (.get index) (.get limit)) <|
    .seq (.store (.bin .add (.get dst) (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8)))
        element)
      (.assign index (.bin .add (.get index) (.const 1)))

theorem build_size (n : UInt64) (f : UInt64 → UInt64) : (LeanExe.build n f).size = n.toNat := by
  simp [LeanExe.build]

theorem build_getElem (n : UInt64) (f : UInt64 → UInt64) (k : Nat)
    (hk : k < (LeanExe.build n f).size) :
    (LeanExe.build n f)[k] = f (UInt64.ofNat k) := by
  simp [LeanExe.build]

theorem element_address (ptr : UInt64) (k : Nat) :
    (ptr + (UInt64.ofNat k + 1) * 8).toUInt32 = UInt64Array.wordAddress ptr (k + 1) := by
  unfold UInt64Array.wordAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- `set!` is the copying template with an element function that replaces one
position. -/
theorem set!_eq_build (xs : Array UInt64) (k v : UInt64) (hSize : xs.size < 2 ^ 64) :
    xs.set! k.toNat v =
      LeanExe.build (UInt64.ofNat xs.size) fun j => if j = k then v else xs[j.toNat]! := by
  have hn : (UInt64.ofNat xs.size).toNat = xs.size := UInt64.toNat_ofNat_of_lt' hSize
  apply Array.ext
  · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, build_size, hn]
  · intro j hj _
    rw [build_getElem]
    have hj' : j < xs.size := by simpa using hj
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hj']
    have hj64 : (UInt64.ofNat j).toNat = j :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [hj64, getElem!_pos xs j hj']
    by_cases hk : k.toNat = j
    · have : UInt64.ofNat j = k := by rw [← hk, UInt64.ofNat_toNat]
      simp [hk, this]
    · have : UInt64.ofNat j ≠ k := fun h => hk (by rw [← h, hj64])
      simp [hk, this]

/-- `insertIdx!` is the copying template with one more element, or an empty array
when the position is past the end, where `insertIdx!` panics and returns the
default. -/
theorem insertIdx!_eq_build (xs : Array UInt64) (k v : UInt64) (hSize : xs.size + 1 < 2 ^ 64) :
    xs.insertIdx! k.toNat v =
      LeanExe.build (if k.toNat ≤ xs.size then UInt64.ofNat (xs.size + 1) else 0) fun j =>
        if j < k then xs[j.toNat]! else if j = k then v else xs[(j - 1).toNat]! := by
  have hU : UInt64.size = 2 ^ 64 := rfl
  by_cases hk : k.toNat ≤ xs.size
  · have hn : (UInt64.ofNat (xs.size + 1)).toNat = xs.size + 1 :=
      UInt64.toNat_ofNat_of_lt' (by omega)
    simp only [Array.insertIdx!, hk, dite_true, ite_true]
    apply Array.ext
    · rw [Array.size_insertIdx hk, build_size, hn]
    · intro j hj _
      rw [build_getElem, Array.getElem_insertIdx hk]
      have hj' : j < xs.size + 1 := by simpa [Array.size_insertIdx hk] using hj
      have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by omega)
      have hLess : UInt64.ofNat j < k ↔ j < k.toNat := by
        rw [UInt64.lt_iff_toNat_lt, hj64]
      have hEq : UInt64.ofNat j = k ↔ j = k.toNat := by
        constructor
        · intro h; rw [← h, hj64]
        · intro h; rw [h, UInt64.ofNat_toNat]
      by_cases h1 : j < k.toNat
      · simp only [h1, dite_true, hLess.mpr h1, ite_true, hj64, getElem!_pos xs j (by omega)]
      · by_cases h2 : j = k.toNat
        · simp [h2]
        · have hSub : (UInt64.ofNat j - 1).toNat = j - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hj64]; simp; omega),
              hj64]
            simp
          have hn1 : ¬UInt64.ofNat j < k := fun h => h1 (hLess.mp h)
          have hn2 : UInt64.ofNat j ≠ k := fun h => h2 (hEq.mp h)
          simp only [h1, h2, dite_false, hn1, hn2, ite_false, hSub,
            getElem!_pos xs (j - 1) (by omega)]
  · simp only [Array.insertIdx!, hk, dite_false, ite_false]
    apply Array.ext
    · simp [build_size]
      rfl
    · intro j hj
      have hEmpty : (default : Array UInt64).size = 0 := rfl
      exact absurd hj (by simp [panicWithPosWithDecl, panic, panicCore, hEmpty])

/-- Borrowed arrays stay laid out while a new block is written: they lie outside
it. -/
theorem borrowed_at_after_writes {heap : Heap} {initial current : Store Unit} {m : Module}
    {need ptr : UInt64} {p : UInt64} {ws : Array UInt64} {size : Nat}
    (hHeap : heap.At initial) (hRoomNeed : heap.Room initial m (48 + need.toNat))
    (hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr)
    (hBase : 4096 + 48 ≤ ptr.toNat)
    (hFits : 8 * (size + 1) ≤ (allocatedCapacity need heap.free).toNat)
    (hBorrowed : heap.Borrowed initial p ws)
    (hWrites : Memory.WritesRange (heap.allocateStore initial need 1) current ptr.toNat
      (ptr.toNat + 8 * (size + 1))) :
    UInt64Array.At current p ws := by
  have hDisjoint := hBorrowed.disjoint_allocated hHeap need
  rw [hPtrDef] at hDisjoint
  unfold regionsDisjoint at hDisjoint
  exact (hBorrowed.allocate 1 hHeap hRoomNeed).values.writesRange hWrites (by omega)

/-- The copying template allocates `8 * (n + 1)` bytes, stores the length `n`, and
stores `f i` at each index `i`, leaving the pointer in `dst`, with the facts of
`Heap.NewArray` for an array equal to `LeanExe.build n f`.  The element
expression may read any borrowed array. -/
theorem Stmt.build_spec {typeIdx scratch dst limit index : Nat} {count element : Expr .u64}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (f : UInt64 → UInt64)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hSpace : heap.Room initial m (48 + 8 * (n.toNat + 1)))
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hElement : ∀ (k : Nat) (store : Store Unit) (state : State), k < n.toNat →
      (∀ p ws, heap.Borrowed initial p ws → UInt64Array.At store p ws) →
      State.Frame scratch [dst, limit, index] before state →
      state.get index = some (.i64 (UInt64.ofNat k)) →
      ∃ next, element.eval store.mem scratch state = some (f (UInt64.ofNat k), next)) :
    Triple m (.build dst limit index count element) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch [dst, limit, index] before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (n.toNat + 1)))) store ptr
          (LeanExe.build n f) (48 + 8 * (n.toNat + 1))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDstLimit, hDstIndex⟩, hLimitIndex⟩ := hLocals
  obtain ⟨hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hAddress := hSpace.address
  have hAllSize : (LeanExe.build n f).size = n.toNat := build_size n f
  generalize hAllDef : LeanExe.build n f = all at hAllSize ⊢
  have hNeed : (UInt64.ofNat (8 * (n.toNat + 1))).toNat = 8 * (n.toNat + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hSize := allocSize_words n.toNat (by omega)
  have hNeedValue : (n + 1) * 8 = UInt64.ofNat (8 * (n.toNat + 1)) := by
    apply UInt64.toNat_inj.mp
    rw [hNeed]
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  generalize hNeedDef : UInt64.ofNat (8 * (n.toNat + 1)) = need at hNeed hSize hNeedValue ⊢
  have hRoomNeed : heap.Room initial m (48 + need.toNat) := by rw [hNeed]; exact hSpace
  have hBlock := hHeap.allocate_block 1 hRoomNeed
  have hCapacity := allocated_capacity need heap.free
  generalize hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr at hBlock ⊢
  have hBlockAddress := hBlock.address
  have hBlockMemory := hBlock.memory
  have hBlockBase := hBlock.base
  have hPtr32 : ptr.toUInt32.toNat = ptr.toNat := by
    rw [Memory.toUInt32_toNat]; omega
  have hBorrowedAt : ∀ (current : Store Unit),
      Memory.WritesRange (heap.allocateStore initial need 1) current ptr.toNat
        (ptr.toNat + 8 * (all.size + 1)) →
      ∀ p ws, heap.Borrowed initial p ws → UInt64Array.At current p ws :=
    fun current hWrites p ws hBorrowed => borrowed_at_after_writes hHeap hRoomNeed hPtrDef
      hBlockBase (by rw [hAllSize, ← hNeed]; exact hCapacity) hBorrowed hWrites
  -- The count, the allocation, the length word, and the first index.
  obtain ⟨c1, hCountEval⟩ := hCount
  have hFrameC := Expr.eval_frame [dst, limit, index] count initial.mem scratch before c1 _
    hCountEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := c1) (index := limit) (.i64 n)
    (by have := hFrameC.params; have := hFrameC.locals; omega)
  have hFrame1 := hFrameC.set? hSet1 (Or.inl (by simp))
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := dst) (.i64 ptr)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (Or.inl (by simp))
  have hPtr2 : s2.get dst = some (.i64 ptr) := State.get_set?_same hSet2
  have hLimit2 : s2.get limit = some (.i64 n) := by
    rw [State.get_set?_ne (Ne.symm hDstLimit) hSet2, State.get_set?_same hSet1]
  obtain ⟨s3, hSet3⟩ := State.exists_set? (state := s2) (index := index) (.i64 0)
    (by have := hFrame2.params; have := hFrame2.locals; omega)
  have hFrame3 := hFrame2.set? hSet3 (Or.inl (by simp))
  set storeA := heap.allocateStore initial need 1
  let store2 : Store Unit := { storeA with mem := storeA.mem.write64 ptr.toUInt32 n }
  have hPrefix2 : UInt64Array.PrefixAt store2 ptr all 0 := by
    refine UInt64Array.PrefixAt.empty _ _ _ ?_ ?_ ?_
    · rw [hAllSize]; omega
    · simp only [store2, Wasm.Mem.write64_pages, hAllSize]; omega
    · rw [hAllSize, UInt64.ofNat_toNat]; exact Memory.read64_write64 ..
  have hWrites2 : Memory.WritesRange storeA store2 ptr.toNat (ptr.toNat + 8 * (all.size + 1)) :=
    Memory.WritesRange.write64 _ ptr.toUInt32 _ _ _ (by omega) (by omega)
  let Inv : Store Unit → State → Prop := fun store state =>
    ∃ k, k ≤ all.size ∧ UInt64Array.PrefixAt store ptr all k ∧
      Memory.WritesRange storeA store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) ∧
      State.Frame scratch [dst, limit, index] before state ∧
      state.get dst = some (.i64 ptr) ∧ state.get limit = some (.i64 n) ∧
      state.get index = some (.i64 (UInt64.ofNat k))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 k) => all.size - k.toNat
    | _ => 0
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    Stmt.seq_spec (M := fun store state => store = storeA ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s3) ?_ <|
    (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨n, c1, s1, hCountEval, hSet1, rfl, rfl⟩
  · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨[need], s1, _, by simp [Expr.evalAll, Expr.eval, State.get_set?_same hSet1,
        U64Op.apply, hNeedValue],
      fun env => alloc_spec hMemory32 hImports hFunc env heap initial need hHeap
        (by rw [hSize]; exact hRoomNeed), ?_⟩
    rintro store' out ⟨hStore', hOut⟩
    rw [hSize] at hStore' hOut
    exact ⟨ptr, s2, by rw [hOut, hPtrDef], hSet2, hStore', rfl⟩
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨ptr, s2, n, s2, by simp [Expr.eval, hPtr2], by simp [Expr.eval, hLimit2],
      by rw [hPtr32]; omega, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, s2, s3, rfl, hSet3, rfl, rfl⟩
  · rintro store state ⟨k, -, -, -, -, -, hLimitGet, hIndexGet⟩
    exact ⟨decide (UInt64.ofNat k < n), state, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨k, hk, hPrefix, hWrites, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, rfl, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega)] at hLess
    rw [← hAllSize] at hLess
    obtain ⟨t1, hElementEval⟩ := hElement k store current (by omega)
      (hBorrowedAt store hWrites) hFrame hIndexGet
    have hFrameT1 := hFrame.trans (Expr.eval_frame _ element store.mem scratch current t1 _
      hElementEval)
    have hKeep : ∀ j, j < scratch → t1.get j = current.get j := fun j hj =>
      (Expr.eval_frame [] element store.mem scratch current t1 _ hElementEval).get j hj (by simp)
    have hValue : all[k] = f (UInt64.ofNat k) := by
      subst hAllDef; exact build_getElem n f k hLess
    obtain ⟨t2, hSetT2⟩ := State.exists_set? (state := t1) (index := index)
      (.i64 (UInt64.ofNat k + 1))
      (by have := hFrameT1.params; have := hFrameT1.locals; omega)
    refine Stmt.seq_spec (M := fun s st => s = UInt64Array.writeElement store ptr k all[k] ∧
        st = t1) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨ptr + (UInt64.ofNat k + 1) * 8, current, f (UInt64.ofNat k), t1,
        by simp [Expr.eval, hDstGet, hIndexGet, U64Op.apply], hElementEval, ?_, ?_, rfl⟩
      · rw [element_address]; exact hPrefix.elementBound k hLess
      · rw [element_address, hValue]; rfl
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨UInt64.ofNat k + 1, t1, t2,
        by simp [Expr.eval, hKeep index hIndexBelow, hIndexGet, U64Op.apply], hSetT2,
        ⟨k + 1, hLess, hPrefix.write_next hLess,
          hWrites.trans (UInt64Array.writeElement_frame store ptr all.size k all[k] hPrefix.1 hLess),
          hFrameT1.set? hSetT2 (Or.inl (by simp)), ?_, ?_, ?_⟩, ?_⟩
      · rw [State.get_set?_ne hDstIndex hSetT2, hKeep dst hDstBelow, hDstGet]
      · rw [State.get_set?_ne hLimitIndex hSetT2, hKeep limit hLimitBelow, hLimitGet]
      · rw [State.get_set?_same hSetT2]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      · simp only [measure, State.get_set?_same hSetT2, hIndexGet, UInt64.toNat_add,
          UInt64.toNat_ofNat', UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨0, Nat.zero_le _, hPrefix2, hWrites2, hFrame3, ?_, ?_, State.get_set?_same hSet3⟩
    · rw [State.get_set?_ne hDstIndex hSet3, hPtr2]
    · rw [State.get_set?_ne hLimitIndex hSet3, hLimit2]
  · rintro store state ⟨current, ⟨k, hk, hPrefix, hWrites, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega)] at hNotLess
    obtain rfl : k = all.size := by omega
    have hWithin : WritesWithin storeA store ptr.toNat (allocatedCapacity need heap.free).toNat := by
      refine ⟨by rw [hWrites.1], hWrites.2.1, fun address hOutside => hWrites.2.2 address ?_⟩
      omega
    subst hPtrDef hAllDef
    have hNew := Heap.newArray_of_writes hHeap hRoomNeed hWithin hPrefix.complete (by omega)
      (by rw [hWrites.1]; exact heap.allocateStore_memoryCaps initial need 1)
    rw [hNeed] at hNew
    exact ⟨_, hFrame, hDstGet, hNew⟩

end Project.IR
