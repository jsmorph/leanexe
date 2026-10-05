import Project.IR.Build
import Project.IR.RecordRead

/-!
The template that builds an array of records.  An element of `k` components occupies words
`i · k` to `i · k + k - 1`, so the array is `flatWords (LeanExe.build n g)`, the layout that
`Represent (Array α)` gives a flat `α`.  For each index, a statement computes the element's
components into locals, and the template stores their words.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module} {a : Bool}

/-- The word of local `c` of type `type`: a word local's value, or a float local's bit
pattern. -/
def Expr.word (c : Nat) : ScalarType → Expr .u64
  | .f64 => .toBits (.getF c)
  | .f32 => .toBits32 (.getF32 c)
  | _ => .get c

/-- `e` evaluates to `w` in `state`, in every memory and at every scratch index, and leaves
the state unchanged. -/
def Expr.Yields (e : Expr .u64) (state : State) (w : UInt64) : Prop :=
  ∀ mem scratch, e.eval mem scratch state = some (w, state)

theorem Expr.yields_get {state : State} {c : Nat} {w : UInt64}
    (h : state.get c = some (.i64 w)) : Expr.Yields (.get c) state w := fun _ _ => by
  simp [Expr.eval, h]

theorem Expr.yields_toBits {state : State} {c : Nat} {b : UInt64}
    (h : state.get c = some (.f64 b)) : Expr.Yields (.toBits (.getF c)) state b := fun _ _ => by
  simp [Expr.eval, h]

/-- The address of word `i · k + j` of the array at local `dst`, where local `index` holds
`i`. -/
def recordAddress (dst index k j : Nat) : Expr .u64 :=
  .bin .add (.get dst) (.bin .mul (.bin .add (.bin .mul (.get index) (.const (UInt64.ofNat k)))
    (.const (UInt64.ofNat (j + 1)))) (.const 8))

/-- Stores the values of `elements` as words `i · k + j` onward of the array at local `dst`,
where local `index` holds `i`. -/
def Stmt.storeWords (dst index k : Nat) : Nat → List (Expr .u64) → Stmt
  | _, [] => .skip
  | j, e :: rest => .seq (.store (recordAddress dst index k j) e) (storeWords dst index k (j + 1) rest)

/-- The loop of the record template: for each index `i` from the value of local `index` below
the value of local `limit`, `body` runs and the values of the `k` expressions `elements` are
stored as words `i · k` to `i · k + k - 1` of the array at local `dst`. -/
def Stmt.fillRecords (dst limit index : Nat) (body : Stmt) (elements : List (Expr .u64)) :
    Stmt :=
  .while (.ltU (.get index) (.get limit)) <|
    .seq body <|
    .seq (.storeWords dst index elements.length 0 elements)
      (.assign index (.bin .add (.get index) (.const 1)))

/-- Local `dst` receives a new array of `count` records of `k` words, where `k` is the number
of `elements`, with the count held in local `limit`.  The code traps when the array would hold
`2 ^ 29` words or more, since it would not fit in 32-bit memory.  For each index `i`, held in
local `index`, `body` runs and the values of `elements` are then words `i · k` to
`i · k + k - 1`. -/
def Stmt.buildRecords (dst limit index : Nat) (count : Expr .u64) (body : Stmt)
    (elements : List (Expr .u64)) : Stmt :=
  .seq (.assign limit count) <|
  .seq (.ite (.ltU (.get limit) (.const (UInt64.ofNat (536870911 / elements.length + 1))))
    .skip .abort) <|
  .seq (.call 0 [⟨.u64, .bin .mul (.bin .add (.bin .mul (.get limit)
    (.const (UInt64.ofNat elements.length))) (.const 1)) (.const 8)⟩] [dst]) <|
  .seq (.store (.get dst) (.bin .mul (.get limit) (.const (UInt64.ofNat elements.length)))) <|
  .seq (.assign index (.const 0)) <|
  .fillRecords dst limit index body elements

theorem record_address (ptr : UInt64) (i k j : Nat) :
    (ptr + (UInt64.ofNat i * UInt64.ofNat k + UInt64.ofNat (j + 1)) * 8).toUInt32 =
      UInt64Array.wordAddress ptr (i * k + j + 1) := by
  have h : (UInt64.ofNat i * UInt64.ofNat k + UInt64.ofNat (j + 1)) * 8 =
      UInt64.ofNat (8 * (i * k + j + 1)) := by
    rw [show 8 * (i * k + j + 1) = (i * k + (j + 1)) * 8 by omega,
      UInt64.ofNat_mul (i * k + (j + 1)) 8, UInt64.ofNat_add (i * k) (j + 1),
      UInt64.ofNat_mul i k]
    rfl
  unfold UInt64Array.wordAddress
  rw [h]

/-- The stores of one record: with words `0` to `i · k + j - 1` in place, storing the values
of `elements` puts words `i · k + j` onward in place. -/
theorem Stmt.storeWords_spec {scratch dst index k i : Nat} {state : State} {ptr : UInt64}
    {all : Array UInt64} {base : Store Unit}
    (hDst : state.get dst = some (.i64 ptr))
    (hIndex : state.get index = some (.i64 (UInt64.ofNat i))) :
    ∀ (elements : List (Expr .u64)) (j : Nat) (s0 : Store Unit),
      i * k + j + elements.length ≤ all.size →
      UInt64Array.PrefixAt s0 ptr all (i * k + j) →
      Memory.WritesRange base s0 ptr.toNat (ptr.toNat + 8 * (all.size + 1)) →
      (∀ j' (h : j' < elements.length), Expr.Yields elements[j'] state all[i * k + j + j']!) →
      TripleA a m (.storeWords dst index k j elements) scratch
        (fun s st => s = s0 ∧ st = state)
        (fun s st => st = state ∧
          UInt64Array.PrefixAt s ptr all (i * k + j + elements.length) ∧
          Memory.WritesRange base s ptr.toNat (ptr.toNat + 8 * (all.size + 1))) := by
  intro elements
  induction elements with
  | nil =>
    intro j s0 _ hPrefix hWrites _
    exact Stmt.skip_spec.mono (fun _ _ h => h) fun s st ⟨hs, hst⟩ => by
      subst hs hst
      exact ⟨rfl, hPrefix, hWrites⟩
  | cons e rest ih =>
    intro j s0 hRoom hPrefix hWrites hYields
    simp only [List.length_cons] at hRoom
    have hLess : i * k + j < all.size := by omega
    have hE := hYields 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero, getElem!_pos all (i * k + j) hLess] at hE
    let written := UInt64Array.writeElement s0 ptr (i * k + j) all[i * k + j]
    refine Stmt.seq_spec (M := fun s st => s = written ∧ st = state) ?_ ?_
    · refine Stmt.store_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      refine ⟨ptr + (UInt64.ofNat i * UInt64.ofNat k + UInt64.ofNat (j + 1)) * 8, st,
        all[i * k + j], st, by simp [recordAddress, Expr.eval, hDst, hIndex, U64Op.apply],
        hE s.mem scratch, ?_, ?_⟩
      · rw [record_address]; exact hPrefix.elementBound _ hLess
      · rw [record_address]; exact ⟨rfl, rfl⟩
    · have hNext := hPrefix.write_next hLess
      rw [show i * k + j + 1 = i * k + (j + 1) by omega] at hNext
      refine (ih (j + 1) written (by omega) hNext
        (hWrites.trans (UInt64Array.writeElement_frame s0 ptr all.size _ _ hPrefix.1 hLess))
        fun j' h => ?_).mono (fun _ _ h => h) fun s st ⟨h1, h2, h3⟩ => ⟨h1, ?_, h3⟩
      · have := hYields (j' + 1) (by simp; omega)
        rw [show i * k + (j + 1) + j' = i * k + j + (j' + 1) by omega]
        simpa using this
      · rw [List.length_cons,
          show i * k + j + (rest.length + 1) = i * k + (j + 1) + rest.length by omega]
        exact h2

/-- The record fill loop, entered with the array's length word in place and local `index` at
0, stores every word of `all`, the `k` words of each of `n` records. -/
theorem Stmt.fillRecords_spec {scratch dst limit index : Nat} {elements : List (Expr .u64)}
    {body : Stmt} {writes : List Nat} {before : State} {base start : Store Unit} {ptr : UInt64}
    {all : Array UInt64} {n : Nat}
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hK : 0 < elements.length) (hAllSize : all.size = n * elements.length)
    (hSize : all.size < 536870912)
    (hPrefix : UInt64Array.PrefixAt start ptr all 0)
    (hWrites : Memory.WritesRange base start ptr.toNat (ptr.toNat + 8 * (all.size + 1)))
    (hDst : before.get dst = some (.i64 ptr))
    (hLimit : before.get limit = some (.i64 (UInt64.ofNat n)))
    (hIndex : before.get index = some (.i64 0))
    (hBody : ∀ (i : Nat) (store : Store Unit) (state : State), i < n →
      Memory.WritesRange base store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat i)) →
      TripleA a m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∀ j (hj : j < elements.length),
            Expr.Yields elements[j] st all[i * elements.length + j]!)) :
    TripleA a m (.fillRecords dst limit index body elements) scratch
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
  set k := elements.length with hk
  have hn : n ≤ all.size := by rw [hAllSize]; exact Nat.le_mul_of_pos_right _ hK
  have hN : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  let Inv : Store Unit → State → Prop := fun store state =>
    ∃ i, i ≤ n ∧ UInt64Array.PrefixAt store ptr all (i * k) ∧
      Memory.WritesRange base store ptr.toNat (ptr.toNat + 8 * (all.size + 1)) ∧
      State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
      state.get dst = some (.i64 ptr) ∧ state.get limit = some (.i64 (UInt64.ofNat n)) ∧
      state.get index = some (.i64 (UInt64.ofNat i))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 i) => n - i.toNat
    | _ => 0
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro store state ⟨i, -, -, -, -, -, hLimitGet, hIndexGet⟩
    exact ⟨decide (UInt64.ofNat i < UInt64.ofNat n), state,
      by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply TripleA.of_forall
    rintro store state ⟨current, ⟨i, hi, hPrefixI, hWritesI, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, rfl, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hLess
    have hRecord : i * k + k ≤ all.size := by
      rw [hAllSize, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hLess
    refine Stmt.seq_spec (hBody i store current hLess hWritesI hFrame hIndexGet) ?_
    apply TripleA.of_forall
    rintro s b ⟨hs, hFrameB, hYields⟩
    subst s
    have hFrameBW : State.Frame scratch ([dst, limit, index] ++ writes) before b :=
      hFrame.trans (hFrameB.weaken fun j hj => List.mem_append_right _ hj)
    have hDstB : b.get dst = some (.i64 ptr) := (hFrameB.get dst hDstBelow hDstOut).trans hDstGet
    have hLimitB : b.get limit = some (.i64 (UInt64.ofNat n)) :=
      (hFrameB.get limit hLimitBelow hLimitOut).trans hLimitGet
    have hIndexB : b.get index = some (.i64 (UInt64.ofNat i)) :=
      (hFrameB.get index hIndexBelow hIndexOut).trans hIndexGet
    obtain ⟨t2, hSetT2⟩ := State.exists_set? (state := b) (index := index)
      (.i64 (UInt64.ofNat i + 1))
      (by have := hFrameBW.params; have := hFrameBW.locals; omega)
    refine Stmt.seq_spec (M := fun s st => st = b ∧
        UInt64Array.PrefixAt s ptr all (i * k + 0 + k) ∧
        Memory.WritesRange base s ptr.toNat (ptr.toNat + 8 * (all.size + 1))) ?_ ?_
    · rw [← hk]
      refine Stmt.storeWords_spec hDstB hIndexB elements 0 store (by omega)
        (by simpa using hPrefixI) hWritesI fun j h => ?_
      simpa [hk] using hYields j (by omega)
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hst, hPrefixS, hWritesS⟩
      rw [hst]
      refine ⟨UInt64.ofNat i + 1, b, t2,
        by simp [Expr.eval, hIndexB, U64Op.apply], hSetT2,
        ⟨i + 1, by omega, by rw [Nat.succ_mul]; simpa using hPrefixS, hWritesS,
          hFrameBW.set? hSetT2 (Or.inl (by simp)), ?_, ?_, ?_⟩, ?_⟩
      · rw [State.get_set?_ne hDstIndex hSetT2, hDstB]
      · rw [State.get_set?_ne hLimitIndex hSetT2, hLimitB]
      · rw [State.get_set?_same hSetT2]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      · simp only [measure, State.get_set?_same hSetT2, hIndexGet, UInt64.toNat_add,
          UInt64.toNat_ofNat', UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · rintro store state ⟨rfl, rfl⟩
    exact ⟨0, Nat.zero_le _, by simpa using hPrefix, hWrites, State.Frame.refl _ _ _, hDst,
      hLimit, by simpa using hIndex⟩
  · rintro store state ⟨current, ⟨i, hi, hPrefixI, hWritesI, hFrame, hDstGet, hLimitGet,
      hIndexGet⟩, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff (by omega), hN] at hNotLess
    obtain rfl : i = n := by omega
    rw [← hAllSize] at hPrefixI
    exact ⟨hPrefixI.complete, hWritesI, hFrame, hDstGet⟩

theorem build_size' (n : UInt64) (g : UInt64 → α) : (LeanExe.build n g).size = n.toNat := by
  simp [LeanExe.build]

/-- Word `i · k + j` of the built array of records is component `j` of element `i`. -/
theorem flatWords_build [Scalar α] [Inhabited α] {k : Nat}
    (hk : ∀ x : α, (Scalar.values x).length = k) (n : UInt64) (g : UInt64 → α) {i j : Nat}
    (hi : i < n.toNat) (hj : j < k) :
    (flatWords (LeanExe.build n g))[i * k + j]! =
      ((Scalar.values (g (UInt64.ofNat i))).map Value.word)[j]! := by
  rw [getElem!_def, flatWords, List.getElem?_toArray,
    flatMap_getElem? (by simp [hk]) hj, Array.getElem?_toList,
    Array.getElem?_eq_getElem (by rw [build_size']; exact hi)]
  simp only [Option.bind_some]
  rw [show (LeanExe.build n g)[i]'(by rw [build_size']; exact hi) = g (UInt64.ofNat i) by
    simp [LeanExe.build], getElem!_def]

/-- The record template allocates `8 · (n · k + 1)` bytes, stores the length `n · k`, and
stores the `k` words of `g i` for each index `i`, leaving the pointer in `dst`, with the facts
of `Heap.NewArray` for `flatWords (LeanExe.build n g)`, the stored form of the array of
records.  For each index, `body` keeps the store, writes only the locals `writes`, and leaves a
state in which element expression `j` yields word `j` of `g i`; `body` may read any borrowed
array. -/
theorem Stmt.buildRecords_specA [Scalar α] [Inhabited α] {typeIdx scratch dst limit index : Nat}
    {count : Expr .u64} {body : Stmt} {elements : List (Expr .u64)} {writes : List Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (g : UInt64 → α)
    (hk : ∀ x : α, (Scalar.values x).length = elements.length) (hK : 0 < elements.length)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hLength : a = false → n.toNat ≤ 536870911 / elements.length)
    (hSpace : a = false →
      heap.Room initial m (UInt64.ofNat (8 * (n.toNat * elements.length + 1))))
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hBody : ∀ (i : Nat) (store : Store Unit) (state : State), i < n.toNat →
      (∀ p ws, heap.Borrowed initial p ws → UInt64Array.At store p ws) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat i)) →
      TripleA a m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∀ j (hj : j < elements.length), Expr.Yields elements[j] st
            ((Scalar.values (g (UInt64.ofNat i))).map Value.word)[j]!)) :
    TripleA a m (.buildRecords dst limit index count body elements) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial
          (heap.allocate (UInt64.ofNat (8 * (n.toNat * elements.length + 1)))) store ptr
          (flatWords (LeanExe.build n g))) := by
  have hLocals0 := hLocals
  have hBelow0 := hBelow
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hDstLimit, hDstIndex⟩, hLimitIndex⟩ := hLocals
  obtain ⟨hDstBelow, hLimitBelow, hIndexBelow⟩ := hBelow
  set k := elements.length with hkDef
  have hAllSize : (flatWords (LeanExe.build n g)).size = n.toNat * k := by
    rw [flatWords_size hk, build_size']
  have hValue : ∀ i j, i < n.toNat → j < k → (flatWords (LeanExe.build n g))[i * k + j]! =
      ((Scalar.values (g (UInt64.ofNat i))).map Value.word)[j]! :=
    fun i j hi hj => flatWords_build hk n g hi hj
  generalize hAllDef : flatWords (LeanExe.build n g) = all at hAllSize hValue ⊢
  -- The count, and the check of the length.
  obtain ⟨c1, hCountEval⟩ := hCount
  have hFrameC := Expr.eval_frame [dst, limit, index] count initial.mem scratch before c1 _
    hCountEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := c1) (index := limit) (.i64 n)
    (by have := hFrameC.params; have := hFrameC.locals; omega)
  have hFrame1 := hFrameC.set? hSet1 (Or.inl (by simp))
  have hBound : (UInt64.ofNat (536870911 / k + 1)).toNat = 536870911 / k + 1 :=
    UInt64.toNat_ofNat_of_lt' (by have := Nat.div_le_self 536870911 k; simp [UInt64.size]; omega)
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1 ∧
      n.toNat * k < 536870912) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨n, c1, s1, hCountEval, hSet1, rfl, rfl⟩
  · refine (Stmt.ite_spec
      (PThen := fun store state => store = initial ∧ state = s1 ∧ n.toNat * k < 536870912)
      (PElse := fun _ _ => a = true) Stmt.skip_spec Stmt.abort_specA).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    by_cases hn : n < UInt64.ofNat (536870911 / k + 1)
    · refine ⟨true, s1, by simp [Expr.eval, State.get_set?_same hSet1, ← hkDef, -UInt64.ofNat_add, hn], ?_⟩
      refine ⟨rfl, rfl, ?_⟩
      rw [UInt64.lt_iff_toNat_lt, hBound] at hn
      have := Nat.div_mul_le_self 536870911 k
      have : n.toNat * k ≤ 536870911 / k * k := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨false, s1, by simp [Expr.eval, State.get_set?_same hSet1, ← hkDef, -UInt64.ofNat_add, hn],
        ?_⟩
      cases a
      · have hL := hLength rfl
        rw [UInt64.lt_iff_toNat_lt, hBound] at hn
        omega
      · rfl
  by_cases hn : n.toNat * k < 536870912
  swap
  · exact TripleA.of_false.mono (fun _ _ h => absurd h.2.2 hn) fun _ _ h => h
  refine (?_ : TripleA a m _ scratch (fun store state => store = initial ∧ state = s1) _).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h
  have hnLe : n.toNat ≤ n.toNat * k := Nat.le_mul_of_pos_right _ hK
  have hNeed : (UInt64.ofNat (8 * (n.toNat * k + 1))).toNat = 8 * (n.toNat * k + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hSize := allocSize_words (n.toNat * k) (by omega)
  have hWords : n * UInt64.ofNat k = UInt64.ofNat (n.toNat * k) := by
    rw [UInt64.ofNat_mul, UInt64.ofNat_toNat]
  have hNeedValue : (n * UInt64.ofNat k + 1) * 8 = UInt64.ofNat (8 * (n.toNat * k + 1)) := by
    rw [hWords]
    apply UInt64.toNat_inj.mp
    rw [hNeed]
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  generalize hNeedDef : UInt64.ofNat (8 * (n.toNat * k + 1)) = need at hNeed hSize hNeedValue hSpace ⊢
  by_cases hFitsNeed : heap.Fits need
  swap
  · -- The block does not fit, so `alloc` traps.
    refine Stmt.seq_spec (M := fun _ _ => False) ?_ TripleA.of_false
    refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨[.i64 need], s1, _, by simp [Expr.evalResults, Expr.eval, State.get_set?_same hSet1,
        U64Op.apply, ← hkDef, hNeedValue],
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
  let store2 : Store Unit :=
    { storeA with mem := storeA.mem.write64 ptr.toUInt32 (n * UInt64.ofNat k) }
  have hPrefix2 : UInt64Array.PrefixAt store2 ptr all 0 := by
    refine UInt64Array.PrefixAt.empty _ _ _ ?_ ?_ ?_
    · rw [hAllSize]; omega
    · simp only [store2, Wasm.Mem.write64_pages, hAllSize]; omega
    · rw [hAllSize, ← hWords]; exact Memory.read64_write64 ..
  have hWrites2 : Memory.WritesRange storeA store2 ptr.toNat (ptr.toNat + 8 * (all.size + 1)) :=
    Memory.WritesRange.write64 _ ptr.toUInt32 _ _ _ (by omega) (by omega)
  refine Stmt.seq_spec (M := fun store state => store = storeA ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s2) ?_ <|
    Stmt.seq_spec (M := fun store state => store = store2 ∧ state = s3) ?_ <|
    ((Stmt.fillRecords_spec (base := storeA) (ptr := ptr) (all := all) (n := n.toNat)
      hLocals0 hBelow0 hApart (by rw [hFrame3.params, hFrame3.locals]; exact hRoom)
      hK hAllSize (by omega) hPrefix2 hWrites2 hPtr3
      (by rw [hLimit3, UInt64.ofNat_toNat]) (State.get_set?_same hSet3)
      fun i store state hi hWrites hFrame hIndex =>
        (hBody i store state hi (hBorrowedAt store hWrites)
          (hFrame3.weaken (fun j hj => List.mem_append_left _ hj) |>.trans hFrame) hIndex).mono
          (fun _ _ h => h) fun s st ⟨hs, hF, hYields⟩ =>
            ⟨hs, hF, fun j hj => by
              show elements[j].Yields st all[i * k + j]!
              rw [hValue i j hi hj]
              exact hYields j hj⟩).mono (fun _ _ h => h) ?_)
  · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨[.i64 need], s1, _, by simp [Expr.evalResults, Expr.eval, State.get_set?_same hSet1,
        U64Op.apply, ← hkDef, hNeedValue],
      fun env => alloc_spec_runs a hMemory32 hImports hFunc env heap initial need hHeap
        (by omega) hCap (fun h => by rw [hSize]; exact hSpace h), ?_⟩
    rintro store' out ⟨-, hStore', hOut⟩
    rw [hSize] at hStore' hOut
    exact ⟨s2, by simp [hOut, hPtrDef, State.setAll, hSet2], hStore', rfl⟩
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨ptr, s2, n * UInt64.ofNat k, s2, by simp [Expr.eval, hPtr2],
      by simp [Expr.eval, hLimit2, U64Op.apply, hkDef], by rw [hPtr32]; omega, rfl, rfl⟩
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
      hNew⟩

/-- The record template allocates `8 · (n · k + 1)` bytes, stores the length `n · k`, and
stores the `k` words of `g i` for each index `i`, leaving the pointer in `dst`, with the facts
of `Heap.NewArray` for `flatWords (LeanExe.build n g)`, the stored form of the array of
records.  For each index, `body` keeps the store, writes only the locals `writes`, and leaves a
state in which element expression `j` yields word `j` of `g i`; `body` may read any borrowed
array. -/
theorem Stmt.buildRecords_spec [Scalar α] [Inhabited α] {typeIdx scratch dst limit index : Nat}
    {count : Expr .u64} {body : Stmt} {elements : List (Expr .u64)} {writes : List Nat}
    {initial : Store Unit} {before : State} {heap : Heap} {n : UInt64} (g : UInt64 → α)
    (hk : ∀ x : α, (Scalar.values x).length = elements.length) (hK : 0 < elements.length)
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [dst, limit, index].Nodup) (hBelow : ∀ j ∈ [dst, limit, index], j < scratch)
    (hApart : ∀ j ∈ writes, j ∉ [dst, limit, index])
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hBody : ∀ (i : Nat) (store : Store Unit) (state : State), i < n.toNat →
      (∀ p ws, heap.Borrowed initial p ws → UInt64Array.At store p ws) →
      State.Frame scratch ([dst, limit, index] ++ writes) before state →
      state.get index = some (.i64 (UInt64.ofNat i)) →
      Triple m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => s = store ∧ State.Frame scratch writes state st ∧
          ∀ j (hj : j < elements.length), Expr.Yields elements[j] st
            ((Scalar.values (g (UInt64.ofNat i))).map Value.word)[j]!)) :
    Triple m (.buildRecords dst limit index count body elements) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch ([dst, limit, index] ++ writes) before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial
          (heap.allocate (UInt64.ofNat (8 * (n.toNat * elements.length + 1)))) store ptr
          (flatWords (LeanExe.build n g))) :=
  Stmt.buildRecords_specA (a := true) g hk hK hMemory32 hImports hFunc hLocals hBelow hApart hRoom
    hHeap hCap (fun h => nomatch h) (fun h => nomatch h) hCount hBody

end Project.IR
