import Project.IR.ArrayLiteral
import Project.IR.Loop
import Project.IR.Read
import LeanExe.Build

/-!
The rule lemma for the compiler's copying template.  The compiler implements
Lean's array operations and `LeanExe.build` by allocating a new array and storing
each element, computed by an expression of its index.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module} {a : Bool}

/-- The loop of the array templates: for each index `i` from the value of local `index`
below the value of local `limit`, `body` runs and the value of `element` is stored as
element `i` of the array at local `dst`. -/
def Stmt.fill (dst limit index : Nat) (body : Stmt) (element : Expr .u64) : Stmt :=
  .while (.ltU (.get index) (.get limit)) <|
    .seq body <|
    .seq (.store (.bin .add (.get dst) (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8)))
        element)
      (.assign index (.bin .add (.get index) (.const 1)))

/-- Local `dst` receives a new array of `count` elements, with the count held in
local `limit`.  The code traps when the count is `2 ^ 29` or more, since such an array
does not fit in 32-bit memory.  For each index `i`, held in local `index`, `body` runs
and element `i` is then the value of `element`. -/
def Stmt.buildWith (dst limit index : Nat) (count : Expr .u64) (body : Stmt)
    (element : Expr .u64) : Stmt :=
  .seq (.assign limit count) <|
  .seq (.ite (.ltU (.get limit) (.const 536870912)) .skip .abort) <|
  .seq (.call 0 [⟨.u64, .bin .mul (.bin .add (.get limit) (.const 1)) (.const 8)⟩] [dst]) <|
  .seq (.store (.get dst) (.get limit)) <|
  .seq (.assign index (.const 0)) <|
  .fill dst limit index body element

/-- The template with no statement per element: element `i` is the value of
`element` while local `index` holds `i`.  Its code is that of `buildWith` with
`.skip`, which emits nothing. -/
def Stmt.build (dst limit index : Nat) (count element : Expr .u64) : Stmt :=
  .buildWith dst limit index count .skip element

theorem build_size (n : UInt64) (f : UInt64 → UInt64) : (LeanExe.build n f).size = n.toNat := by
  simp [LeanExe.build]

theorem build_getElem (n : UInt64) (f : UInt64 → UInt64) (k : Nat)
    (hk : k < (LeanExe.build n f).size) :
    (LeanExe.build n f)[k] = f (UInt64.ofNat k) := by
  simp [LeanExe.build]

theorem build_map (n : UInt64) (g : UInt64 → α) (h : α → β) :
    (LeanExe.build n g).map h = LeanExe.build n (fun i => h (g i)) := by
  simp [LeanExe.build, Array.map_ofFn, Function.comp_def]

theorem element_address (ptr : UInt64) (k : Nat) :
    (ptr + (UInt64.ofNat k + 1) * 8).toUInt32 = UInt64Array.wordAddress ptr (k + 1) := by
  unfold UInt64Array.wordAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- An array equals its copy by the copying template. -/
theorem copy_eq_build (xs : Array UInt64) (hSize : xs.size < 2 ^ 64) :
    xs = LeanExe.build (UInt64.ofNat xs.size) fun j => xs[j.toNat]! := by
  have hn : (UInt64.ofNat xs.size).toNat = xs.size := UInt64.toNat_ofNat_of_lt' hSize
  apply Array.ext
  · rw [build_size, hn]
  · intro j hj _
    rw [build_getElem]
    have hj64 : (UInt64.ofNat j).toNat = j :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [hj64, getElem!_pos xs j hj]

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

/-- `eraseIdxIfInBounds` is the copying template with one element fewer, or a copy
when the position is past the end. -/
theorem eraseIdxIfInBounds_eq_build (xs : Array UInt64) (k : UInt64) (hSize : xs.size < 2 ^ 64) :
    xs.eraseIdxIfInBounds k.toNat =
      LeanExe.build (if k < UInt64.ofNat xs.size then UInt64.ofNat xs.size - 1
        else UInt64.ofNat xs.size) fun j => if j < k then xs[j.toNat]! else xs[(j + 1).toNat]! := by
  have hn : (UInt64.ofNat xs.size).toNat = xs.size := UInt64.toNat_ofNat_of_lt' hSize
  have hLt : k < UInt64.ofNat xs.size ↔ k.toNat < xs.size := by
    rw [UInt64.lt_iff_toNat_lt, hn]
  by_cases hk : k.toNat < xs.size
  · simp only [Array.eraseIdxIfInBounds, hk, dite_true, hLt.mpr hk, ite_true]
    have hCount : (UInt64.ofNat xs.size - 1).toNat = xs.size - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
      simp
    apply Array.ext
    · rw [Array.size_eraseIdx, build_size, hCount]
    · intro j hj _
      rw [build_getElem, Array.getElem_eraseIdx hk]
      have hj' : j < xs.size - 1 := by simpa [Array.size_eraseIdx] using hj
      have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hLess : UInt64.ofNat j < k ↔ j < k.toNat := by
        rw [UInt64.lt_iff_toNat_lt, hj64]
      by_cases h1 : j < k.toNat
      · simp only [h1, dite_true, hLess.mpr h1, ite_true, hj64, getElem!_pos xs j (by omega)]
      · have hAdd : (UInt64.ofNat j + 1).toNat = j + 1 := by
          rw [UInt64.toNat_add, hj64]
          simp only [UInt64.reduceToNat]
          omega
        simp only [h1, dite_false, (not_congr hLess).mpr h1, ite_false, hAdd,
          getElem!_pos xs (j + 1) (by omega)]
  · simp only [Array.eraseIdxIfInBounds, hk, dite_false, (not_congr hLt).mpr hk, ite_false]
    apply Array.ext
    · rw [build_size, hn]
    · intro j hj _
      rw [build_getElem]
      have hj' : j < xs.size := by simpa [build_size, hn] using hj
      have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hLess : UInt64.ofNat j < k := by rw [UInt64.lt_iff_toNat_lt, hj64]; omega
      simp only [hLess, ite_true, hj64, getElem!_pos xs j hj']

/-- Borrowed arrays stay laid out while a new block is written: they lie outside
it. -/
theorem borrowed_at_after_writes {heap : Heap} {initial current : Store Unit}
    {need ptr : UInt64} {p : UInt64} {ws : Array UInt64} {size : Nat}
    (hHeap : heap.At initial) (hFitsNeed : heap.Fits need)
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
  exact (hBorrowed.allocate 1 hHeap hFitsNeed).values.writesRange hWrites (by omega)

/-- The fill loop, entered with the array's length word and its first `k0` elements in
place, where `k0` is the value of local `index`, stores the remaining elements of `all`.  It
writes memory only in the array's words, and locals only among `dst`, `limit`, `index`,
and `body`'s `writes`. -/
theorem Stmt.fill_spec {scratch dst limit index : Nat} {element : Expr .u64} {body : Stmt}
    {writes : List Nat} {before : State} {base start : Store Unit} {ptr : UInt64}
    {all : Array UInt64} {k0 : Nat}
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length) (hSize : all.size < 536870912)
    (hk0 : k0 ≤ all.size) (hPrefix : UInt64Array.PrefixAt start ptr all k0)
    (hWrites : Memory.WritesRange base start ptr.toNat (ptr.toNat + 8 * (all.size + 1)))
    (hDst : before.get dst = some (.i64 ptr))
    (hLimit : before.get limit = some (.i64 (UInt64.ofNat all.size)))
    (hIndex : before.get index = some (.i64 (UInt64.ofNat k0)))
    (hBody : ∀ (k : Nat) (hk : k < all.size) (store : Store Unit) (state : State), k0 ≤ k →
      Memory.WritesRange base store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat k)) →
      TripleA a m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∃ next, element.eval s.mem scratch st = some (all[k], next))) :
    TripleA a m (.fill dst limit index body element) scratch
      (fun store state => store = start ∧ state = before)
      (fun store state => UInt64Array.At store ptr all ∧
        Memory.WritesRange base store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) ∧
        State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDstLimit, hDstIndex⟩, hLimitIndex⟩ := hLocals
  obtain ⟨hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hDstOut : dst ∉ writes := fun h => hApart dst h (by simp)
  have hLimitOut : limit ∉ writes := fun h => hApart limit h (by simp)
  have hIndexOut : index ∉ writes := fun h => hApart index h (by simp)
  let n : UInt64 := UInt64.ofNat all.size
  have hN : n.toNat = all.size := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  let Inv : Store Unit → State → Prop := fun store state =>
    ∃ k, k0 ≤ k ∧ k ≤ all.size ∧ UInt64Array.PrefixAt store ptr all k ∧
      Memory.WritesRange base store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) ∧
      State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
      state.get dst = some (.i64 ptr) ∧ state.get limit = some (.i64 n) ∧
      state.get index = some (.i64 (UInt64.ofNat k))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 k) => all.size - k.toNat
    | _ => 0
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro store state ⟨k, -, -, -, -, -, -, hLimitGet, hIndexGet⟩
    exact ⟨decide (UInt64.ofNat k < n), state, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply TripleA.of_forall
    rintro store state ⟨current, ⟨k, hkLow, hk, hPrefix, hWrites, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, rfl, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hLess
    refine Stmt.seq_spec (hBody k hLess store current hkLow hWrites hFrame hIndexGet) ?_
    apply TripleA.of_forall
    rintro s b ⟨hs, hFrameB, t1, hElementEval⟩
    subst s
    have hFrameBW : State.Frame scratch ([dst, limit, index] ++ writes) before b :=
      hFrame.trans (hFrameB.weaken fun j hj => List.mem_append_right _ hj)
    have hDstB : b.get dst = some (.i64 ptr) := (hFrameB.get dst hDstBelow hDstOut).trans hDstGet
    have hLimitB : b.get limit = some (.i64 n) :=
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
    refine Stmt.seq_spec (M := fun s st => s = UInt64Array.writeElement store ptr k all[k] ∧
        st = t1) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨ptr + (UInt64.ofNat k + 1) * 8, b, all[k], t1,
        by simp [Expr.eval, hDstB, hIndexB, U64Op.apply], hElementEval, ?_, ?_, rfl⟩
      · rw [element_address]; exact hPrefix.elementBound k hLess
      · rw [element_address]; rfl
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, hst⟩
      subst s st
      refine ⟨UInt64.ofNat k + 1, t1, t2,
        by simp [Expr.eval, hKeep index hIndexBelow, hIndexB, U64Op.apply], hSetT2,
        ⟨k + 1, by omega, hLess, hPrefix.write_next hLess,
          hWrites.trans (UInt64Array.writeElement_frame store ptr all.size k all[k] hPrefix.1 hLess),
          hFrameT1.set? hSetT2 (Or.inl (by simp)), ?_, ?_, ?_⟩, ?_⟩
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
    exact ⟨k0, le_rfl, hk0, hPrefix, hWrites, State.Frame.refl _ _ _, hDst, hLimit, hIndex⟩
  · rintro store state ⟨current, ⟨k, -, hk, hPrefix, hWrites, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hNotLess
    obtain rfl : k = all.size := by omega
    exact ⟨hPrefix.complete, hWrites, hFrame, hDstGet⟩

/-- The copying template allocates `8 * (n + 1)` bytes, stores the length `n`, and
stores `f i` at each index `i`, leaving the pointer in `dst`, with the facts of
`Heap.NewArray` for an array equal to `LeanExe.build n f`.  For each index, `body`
keeps the store, writes only the locals `writes`, and leaves a state in which
`element` evaluates to `f i`; both may read any borrowed array. -/
theorem Stmt.buildWith_specA {typeIdx scratch dst limit index : Nat} {count element : Expr .u64}
    {body : Stmt} {writes : List Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (f : UInt64 → UInt64)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hLength : a = false → n.toNat < 536870912)
    (hSpace : a = false → heap.Room initial m (UInt64.ofNat (8 * (n.toNat + 1))))
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hBody : ∀ (k : Nat) (store : Store Unit) (state : State), k < n.toNat →
      (∀ p ws, heap.Borrowed initial p ws → UInt64Array.At store p ws) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat k)) →
      TripleA a m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∃ next, element.eval s.mem scratch st = some (f (UInt64.ofNat k), next))) :
    TripleA a m (.buildWith dst limit index count body element) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (n.toNat + 1)))) store ptr
          (LeanExe.build n f) ∧
        store.mem.pages =
          (heap.allocateStore initial (UInt64.ofNat (8 * (n.toNat + 1))) 1).mem.pages) := by
  have hLocals0 := hLocals
  have hBelow0 := hBelow
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDstLimit, hDstIndex⟩, hLimitIndex⟩ := hLocals
  obtain ⟨hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  have hDstOut : dst ∉ writes := fun h => hApart dst h (by simp)
  have hLimitOut : limit ∉ writes := fun h => hApart limit h (by simp)
  have hIndexOut : index ∉ writes := fun h => hApart index h (by simp)
  have hAllSize : (LeanExe.build n f).size = n.toNat := build_size n f
  generalize hAllDef : LeanExe.build n f = all at hAllSize ⊢
  -- The count, and the check of the length.
  obtain ⟨c1, hCountEval⟩ := hCount
  have hFrameC := Expr.eval_frame [dst, limit, index] count initial.mem scratch before c1 _
    hCountEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := c1) (index := limit) (.i64 n)
    (by have := hFrameC.params; have := hFrameC.locals; omega)
  have hFrame1 := hFrameC.set? hSet1 (Or.inl (by simp))
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1 ∧ n.toNat < 536870912)
      ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨n, c1, s1, hCountEval, hSet1, rfl, rfl⟩
  · refine (Stmt.ite_spec
      (PThen := fun store state => store = initial ∧ state = s1 ∧ n.toNat < 536870912)
      (PElse := fun _ _ => a = true) Stmt.skip_spec Stmt.abort_specA).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    by_cases hn : n < 536870912
    · refine ⟨true, s1, by simp [Expr.eval, State.get_set?_same hSet1, hn], ?_⟩
      exact ⟨rfl, rfl, by rw [UInt64.lt_iff_toNat_lt] at hn; exact hn⟩
    · refine ⟨false, s1, by simp [Expr.eval, State.get_set?_same hSet1, hn], ?_⟩
      cases a
      · exact absurd (hLength rfl) (by rw [UInt64.lt_iff_toNat_lt] at hn; exact hn)
      · rfl
  by_cases hn : n.toNat < 536870912
  swap
  · exact TripleA.of_false.mono (fun _ _ h => absurd h.2.2 hn) fun _ _ h => h
  refine (?_ : TripleA a m _ scratch (fun store state => store = initial ∧ state = s1) _).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h
  have hNeed : (UInt64.ofNat (8 * (n.toNat + 1))).toNat = 8 * (n.toNat + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hSize := allocSize_words n.toNat (by omega)
  have hNeedValue : (n + 1) * 8 = UInt64.ofNat (8 * (n.toNat + 1)) := by
    apply UInt64.toNat_inj.mp
    rw [hNeed]
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  generalize hNeedDef : UInt64.ofNat (8 * (n.toNat + 1)) = need at hNeed hSize hNeedValue hSpace ⊢
  by_cases hFitsNeed : heap.Fits need
  swap
  · -- The block does not fit, so `alloc` traps.
    refine Stmt.seq_spec (M := fun _ _ => False) ?_ TripleA.of_false
    refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨[.i64 need], s1, _, by simp [Expr.evalResults, Expr.eval, State.get_set?_same hSet1,
        U64Op.apply, hNeedValue],
      fun env => alloc_spec_runs a hMemory32 hImports hFunc env heap initial need hHeap
        (by omega) hCap (fun h => by rw [hSize]; exact hSpace h), ?_⟩
    rintro store' out ⟨hFits', -, -⟩
    rw [hSize] at hFits'
    exact absurd hFits' hFitsNeed
  have hBlock := hHeap.allocate_block 1 hFitsNeed
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
    fun current hWrites p ws hBorrowed => borrowed_at_after_writes hHeap hFitsNeed hPtrDef
      hBlockBase (by rw [hAllSize, ← hNeed]; exact hCapacity) hBorrowed hWrites
  -- The allocation, the length word, and the first index.
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := dst) (.i64 ptr)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (Or.inl (by simp))
  have hPtr2 : s2.get dst = some (.i64 ptr) := State.get_set?_same hSet2
  have hLimit2 : s2.get limit = some (.i64 n) := by
    rw [State.get_set?_ne (Ne.symm hDstLimit) hSet2, State.get_set?_same hSet1]
  obtain ⟨s3, hSet3⟩ := State.exists_set? (state := s2) (index := index) (.i64 0)
    (by have := hFrame2.params; have := hFrame2.locals; omega)
  have hFrame3 := hFrame2.set? hSet3 (Or.inl (by simp))
  have hPtr3 : s3.get dst = some (.i64 ptr) := by rw [State.get_set?_ne hDstIndex hSet3, hPtr2]
  have hLimit3 : s3.get limit = some (.i64 n) := by
    rw [State.get_set?_ne hLimitIndex hSet3, hLimit2]
  set storeA := heap.allocateStore initial need 1
  let store2 : Store Unit := { storeA with mem := storeA.mem.write64 ptr.toUInt32 n }
  have hPrefix2 : UInt64Array.PrefixAt store2 ptr all 0 := by
    refine UInt64Array.PrefixAt.empty _ _ _ ?_ ?_ ?_
    · rw [hAllSize]; omega
    · simp only [store2, Wasm.Mem.write64_pages, hAllSize]; omega
    · rw [hAllSize, UInt64.ofNat_toNat]; exact Memory.read64_write64 ..
  have hWrites2 : Memory.WritesRange storeA store2 ptr.toNat (ptr.toNat + 8 * (all.size + 1)) :=
    Memory.WritesRange.write64 _ ptr.toUInt32 _ _ _ (by omega) (by omega)
  have hValue : ∀ k (hk : k < all.size), all[k] = f (UInt64.ofNat k) := fun k hk => by
    subst hAllDef; exact build_getElem n f k hk
  refine Stmt.seq_spec (M := fun store state => store = storeA ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s3) ?_ <|
    ((Stmt.fill_spec (base := storeA) (ptr := ptr) (all := all) hLocals0 hBelow0 hApart
      (by rw [hFrame3.params, hFrame3.locals]; exact hRoom) (by omega) (Nat.zero_le _) hPrefix2
      hWrites2 hPtr3 (by rw [hLimit3, hAllSize, UInt64.ofNat_toNat]) (State.get_set?_same hSet3)
      fun k hk store state _ hWrites hFrame hIndex =>
        (hBody k store state (by omega) (hBorrowedAt store hWrites)
          (hFrame3.weaken (fun j hj => List.mem_append_left _ hj) |>.trans hFrame) hIndex).mono
          (fun _ _ h => h) fun s st ⟨hs, hF, next, hEval⟩ =>
            ⟨hs, hF, next, by rw [hValue k hk]; exact hEval⟩).mono (fun _ _ h => h) ?_)
  · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨[.i64 need], s1, _, by simp [Expr.evalResults, Expr.eval, State.get_set?_same hSet1,
        U64Op.apply, hNeedValue],
      fun env => alloc_spec_runs a hMemory32 hImports hFunc env heap initial need hHeap
        (by omega) hCap (fun h => by rw [hSize]; exact hSpace h), ?_⟩
    rintro store' out ⟨-, hStore', hOut⟩
    rw [hSize] at hStore' hOut
    exact ⟨s2, by simp [hOut, hPtrDef, State.setAll, hSet2], hStore', rfl⟩
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨ptr, s2, n, s2, by simp [Expr.eval, hPtr2], by simp [Expr.eval, hLimit2],
      by rw [hPtr32]; omega, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, s2, s3, rfl, hSet3, rfl, rfl⟩
  · rintro store state ⟨hAt, hWrites, hFrame, hDstGet⟩
    have hWithin : WritesWithin storeA store ptr.toNat (allocatedCapacity need heap.free).toNat := by
      refine ⟨by rw [hWrites.1], hWrites.2.1, fun address hOutside => hWrites.2.2 address ?_⟩
      omega
    subst hPtrDef hAllDef
    have hNew := Heap.newArray_of_writes hHeap hFitsNeed hWithin hAt (by omega)
      (by rw [hWrites.1]; exact heap.allocateStore_memoryCaps initial need 1)
    exact ⟨_, hFrame3.weaken (fun j hj => List.mem_append_left _ hj) |>.trans hFrame, hDstGet,
      hNew, hWithin.pages⟩

/-- The copying template allocates `8 * (n + 1)` bytes, stores the length `n`, and
stores `f i` at each index `i`, leaving the pointer in `dst`, with the facts of
`Heap.NewArray` for an array equal to `LeanExe.build n f`.  For each index, `body`
keeps the store, writes only the locals `writes`, and leaves a state in which
`element` evaluates to `f i`; both may read any borrowed array. -/
theorem Stmt.buildWith_spec {typeIdx scratch dst limit index : Nat} {count element : Expr .u64}
    {body : Stmt} {writes : List Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (f : UInt64 → UInt64)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hBody : ∀ (k : Nat) (store : Store Unit) (state : State), k < n.toNat →
      (∀ p ws, heap.Borrowed initial p ws → UInt64Array.At store p ws) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat k)) →
      Triple m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∃ next, element.eval s.mem scratch st = some (f (UInt64.ofNat k), next))) :
    Triple m (.buildWith dst limit index count body element) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (n.toNat + 1)))) store ptr
          (LeanExe.build n f)) :=
  (Stmt.buildWith_specA (a := true) f hMemory32 hImports hFunc hLocals hBelow hApart hRoom hHeap hCap
    (fun h => nomatch h) (fun h => nomatch h) hCount hBody).mono (fun _ _ h => h)
    fun _ _ ⟨ptr, hF, hD, hN, _⟩ => ⟨ptr, hF, hD, hN⟩

/-- `Stmt.buildWith_spec` for the template with no statement per element: the
element expression evaluates to `f i` in any state that keeps `dst`, `limit`, and
`index`. -/
theorem Stmt.build_spec {typeIdx scratch dst limit index : Nat} {count element : Expr .u64}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (f : UInt64 → UInt64)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
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
          (LeanExe.build n f)) := by
  refine (Stmt.buildWith_spec (writes := []) f hMemory32 hImports hFunc hLocals hBelow
    (by simp) hRoom hHeap hCap hCount fun k store state hk hAt hFrame hIndex => ?_).mono
      (fun _ _ h => h) fun _ _ h => by simpa using h
  obtain ⟨next, hEval⟩ := hElement k store state hk hAt (by simpa using hFrame) hIndex
  refine Stmt.skip_spec.mono ?_ fun _ _ h => h
  rintro s st ⟨rfl, rfl⟩
  exact ⟨rfl, State.Frame.refl _ _ _, next, hEval⟩

/-- Local `dst` receives a copy of the array in local `src`: its size goes into local
`size`, and the copying template reads each element. -/
def Stmt.copy (dst limit index size src : Nat) : Stmt :=
  .seq (.arraySize size src) (.build dst limit index (.get size) (.read src (.get index)))

/-- The copy in local `dst` is a new array equal to the source. -/
theorem Stmt.copy_spec {typeIdx scratch src size dst limit index : Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {ptr : UInt64} {xs : Array UInt64}
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [size, dst, limit, index].Nodup)
    (hBelow : ∀ j ∈ [size, dst, limit, index], j < scratch)
    (hSrc : src ∉ [size, dst, limit, index]) (hSrcBelow : src < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hPtr : before.get src = some (.i64 ptr)) (hArray : heap.Borrowed initial ptr xs) :
    Triple m (.copy dst limit index size src) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ p, State.Frame scratch [size, dst, limit, index] before state ∧
        state.get dst = some (.i64 p) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (xs.size + 1)))) store p xs) := by
  have hA := hArray.values
  have hFit := hA.1
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hSrc
  have hSizeBelow := hBelow size (by simp)
  have hn : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  let s1 := before.update size (.i64 (UInt64.ofNat xs.size))
  have hS1 : s1.params.length + s1.locals.length = before.params.length + before.locals.length := by
    simp [s1, State.update_params_length, State.update_locals_length]
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1)
    ((Stmt.arraySize_spec hA hPtr (by omega)).mono (fun _ _ h => h) ?_) ?_
  · rintro store state ⟨rfl, hSet⟩
    rw [State.set?_eq_update _ (by omega)] at hSet
    exact ⟨rfl, (Option.some.inj hSet).symm⟩
  refine (Stmt.build_spec (n := UInt64.ofNat xs.size) (fun j => xs[j.toNat]!) hMemory32 hImports
    hFunc (List.nodup_cons.mp hLocals).2 (fun j hj => hBelow j (List.mem_cons_of_mem _ hj))
    (by omega) hHeap hCap
    ⟨s1, by simp [Expr.eval, s1, State.get_update_same (value := .i64 (UInt64.ofNat xs.size))
      (show size < before.params.length + before.locals.length by omega)]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro k store state _ hAt hFrame hIndex
    have hState : state.params.length + state.locals.length =
        before.params.length + before.locals.length := by
      rw [hFrame.params, hFrame.locals, hS1]
    have hSrcState : state.get src = some (.i64 ptr) := by
      rw [hFrame.get src hSrcBelow (by simp; omega)]
      simp only [s1]
      rw [State.get_update_ne (by omega), hPtr]
    refine ⟨state.update scratch (.i64 (UInt64.ofNat k)), Expr.read_spec (hAt ptr xs hArray)
      (by simp [Expr.eval, hIndex]) (State.set?_eq_update _ (by omega)) ?_⟩
    rw [State.get_update_ne (by omega), hSrcState]
  · rintro store state ⟨p, hFrame, hDst, hNew⟩
    rw [← copy_eq_build xs (by omega), hn] at hNew
    refine ⟨p, ⟨?_, ?_, fun j hj hOut => ?_⟩, hDst, hNew⟩
    · rw [hFrame.params]; simp [s1, State.update_params_length]
    · rw [hFrame.locals]; simp [s1, State.update_locals_length]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hOut
      rw [hFrame.get j hj (by simp; omega)]
      exact State.get_update_ne hOut.1

/-- A pushed array is the build of its size plus one elements: the old ones, then `v`. -/
theorem push_eq_build (xs : Array UInt64) (v : UInt64) (hSize : xs.size + 1 < 2 ^ 64) :
    xs.push v =
      LeanExe.build (UInt64.ofNat xs.size + 1) fun j =>
        if j < UInt64.ofNat xs.size then xs[j.toNat]! else v := by
  have hU : UInt64.size = 2 ^ 64 := rfl
  have hn : (UInt64.ofNat xs.size).toNat = xs.size := UInt64.toNat_ofNat_of_lt' (by omega)
  have hn1 : (UInt64.ofNat xs.size + 1).toNat = xs.size + 1 := by
    rw [UInt64.toNat_add, hn]; simp only [UInt64.reduceToNat]; omega
  apply Array.ext
  · rw [Array.size_push, build_size, hn1]
  · intro j hj _
    rw [build_getElem]
    have hj' : j < xs.size + 1 := by simpa [build_size, hn1] using hj
    have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by omega)
    have hLess : UInt64.ofNat j < UInt64.ofNat xs.size ↔ j < xs.size := by
      rw [UInt64.lt_iff_toNat_lt, hj64, hn]
    rw [Array.getElem_push]
    by_cases h : j < xs.size
    · simp only [h, dite_true, hLess.mpr h, ite_true, hj64, getElem!_pos xs j h]
    · simp only [h, dite_false, (not_congr hLess).mpr h, ite_false]

/-- The build statement of a borrowed `push`, after the size load: local `dst` receives a new
array equal to `xs.push w`. -/
theorem Stmt.pushBuild_spec {typeIdx scratch src size v dst limit index : Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {ptr w : UInt64} {xs : Array UInt64}
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ [src, size, v], j ∉ [dst, limit, index] ∧ j < scratch)
    (hRoom : scratch < before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hPtr : before.get src = some (.i64 ptr))
    (hSize : before.get size = some (.i64 (UInt64.ofNat xs.size)))
    (hV : before.get v = some (.i64 w)) (hArray : heap.Borrowed initial ptr xs) :
    Triple m (.build dst limit index (.bin .add (.get size) (.const 1))
        (.ite (.ltU (.get index) (.get size)) (.read src (.get index)) (.get v))) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ p, State.Frame scratch [dst, limit, index] before state ∧
        state.get dst = some (.i64 p) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (xs.size + 1 + 1)))) store p
          (xs.push w)) := by
  have hA := hArray.values
  have hFit := hA.1
  have hU : UInt64.size = 2 ^ 64 := rfl
  have hn1 : (UInt64.ofNat xs.size + 1).toNat = xs.size + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
    simp only [UInt64.reduceToNat]; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hApart
  obtain ⟨⟨hSrcOut, hSrcBelow⟩, ⟨hSizeOut, hSizeBelow⟩, ⟨hVOut, hVBelow⟩⟩ := hApart
  refine (Stmt.build_spec (n := UInt64.ofNat xs.size + 1)
    (fun j => if j < UInt64.ofNat xs.size then xs[j.toNat]! else w) hMemory32 hImports hFunc
    hLocals hBelow (by omega) hHeap hCap
    ⟨before, by simp [Expr.eval, hSize, U64Op.apply]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hSrcState : state.get src = some (.i64 ptr) := by
      rw [hFrame.get src hSrcBelow (by simpa using hSrcOut), hPtr]
    have hSizeState : state.get size = some (.i64 (UInt64.ofNat xs.size)) := by
      rw [hFrame.get size hSizeBelow (by simpa using hSizeOut), hSize]
    have hVState : state.get v = some (.i64 w) := by
      rw [hFrame.get v hVBelow (by simpa using hVOut), hV]
    have hState : scratch < state.params.length + state.locals.length := by
      rw [hFrame.params, hFrame.locals]; omega
    by_cases hLess : UInt64.ofNat k < UInt64.ofNat xs.size
    · have hRead := Expr.read_spec (array := src) (position := .get index) (scratch := scratch)
        (state := state) (k := UInt64.ofNat k)
        (hAt ptr xs hArray) (by simp [Expr.eval, hIndex]) (State.set?_eq_update _ hState)
        (by rw [State.get_update_ne (by omega), hSrcState])
      exact ⟨state.update scratch (.i64 (UInt64.ofNat k)), by
        simpa [Expr.eval, hIndex, hSizeState, hLess] using hRead⟩
    · exact ⟨state, by simp [Expr.eval, hIndex, hSizeState, hLess, hVState]⟩
  · rintro store state ⟨p, hFrame, hDst, hNew⟩
    rw [← push_eq_build xs w (by omega), hn1] at hNew
    exact ⟨p, hFrame, hDst, hNew⟩

end Project.IR
