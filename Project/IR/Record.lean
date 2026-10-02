import Project.IR.ArrayLiteral
import Project.Pipeline.Records

/-!
The rule lemma for the compiler's record template.  A record of `k` slots is a call of
`alloc` for `8 * k` payload bytes, stores of its kind, width, and child mask into the header
that `alloc` wrote for an array, and one store per slot.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Stores `values` in the slots from `index` on of the record at local `dst`. -/
def Stmt.storeSlots (dst : Nat) : Nat → List (Expr .u64) → Stmt
  | _, [] => .skip
  | index, value :: rest =>
      .seq (.store (.bin .add (.get dst) (.const (UInt64.ofNat (8 * index)))) value)
        (Stmt.storeSlots dst (index + 1) rest)

/-- Local `dst` receives a new record of kind 1 that holds `values`, with child mask
`mask`. -/
def Stmt.record (dst : Nat) (values : List (Expr .u64)) (mask : UInt64) : Stmt :=
  .seq (.call 0 [⟨.u64, .const (UInt64.ofNat (8 * values.length))⟩] [dst]) <|
  .seq (.store (.bin .sub (.get dst) (.const 24)) (.const 1)) <|
  .seq (.store (.bin .sub (.get dst) (.const 16)) (.const (UInt64.ofNat values.length))) <|
  .seq (.store (.bin .sub (.get dst) (.const 8)) (.const mask)) <|
  Stmt.storeSlots dst 0 values

/-- The slot stores leave each word in its slot and write only inside the slots. -/
theorem Stmt.storeSlots_spec {scratch dst : Nat} {before : State} {ptr : UInt64}
    {words : List UInt64} (hDst : dst < scratch)
    (hBound : ptr.toNat + 8 * words.length < 4294967296) (values : List (Expr .u64)) :
    ∀ (index : Nat) (start : Store Unit) (state : State),
      index + values.length = words.length →
      ptr.toNat + 8 * words.length ≤ start.mem.pages * 65536 →
      List.Forall₂ (fun value word => ∀ mem st, State.Frame scratch [dst] before st →
        ∃ next, value.eval mem scratch st = some (word, next)) values (words.drop index) →
      (∀ i (_ : i < index) (hw : i < words.length),
        start.mem.read64 (slotAddress ptr i) = words[i]) →
      State.Frame scratch [dst] before state → state.get dst = some (.i64 ptr) →
      Triple m (Stmt.storeSlots dst index values) scratch
        (fun s t => s = start ∧ t = state)
        (fun s t => (∀ i (hw : i < words.length), s.mem.read64 (slotAddress ptr i) = words[i]) ∧
          State.Frame scratch [dst] before t ∧ t.get dst = some (.i64 ptr) ∧
          Memory.WritesRange start s (ptr.toNat + 8 * index) (ptr.toNat + 8 * words.length)) := by
  induction values with
  | nil =>
      intro index start state hSize _ _ hPrefix hFrame hPtr
      simp only [List.length_nil, Nat.add_zero] at hSize
      subst hSize
      refine Stmt.skip_spec.mono ?_ fun _ _ h => h
      rintro s t ⟨hs, ht⟩
      subst s t
      exact ⟨fun i hw => hPrefix i hw hw, hFrame, hPtr, .refl _ _ _⟩
  | cons value rest ih =>
      intro index start state hSize hMemory hValues hPrefix hFrame hPtr
      simp only [List.length_cons] at hSize
      have hIndex : index < words.length := by omega
      rw [List.drop_eq_getElem_cons hIndex] at hValues
      obtain ⟨hValue, hRest⟩ := List.forall₂_cons.mp hValues
      obtain ⟨next, hEval⟩ := hValue start.mem state hFrame
      have hNextFrame :=
        hFrame.trans (Expr.eval_frame [dst] value start.mem scratch state next _ hEval)
      have hNextPtr : next.get dst = some (.i64 ptr) := by
        rw [Expr.eval_preserves_below value start.mem scratch state next _ dst hEval hDst, hPtr]
      have hAddress : (slotAddress ptr index).toNat = ptr.toNat + 8 * index :=
        slotAddress_toNat (by omega)
      let written : Store Unit :=
        { start with mem := start.mem.write64 (slotAddress ptr index) words[index] }
      have hWrite : Memory.WritesRange start written (ptr.toNat + 8 * index)
          (ptr.toNat + 8 * words.length) :=
        Memory.WritesRange.write64 _ _ _ _ _ (by omega) (by omega)
      refine Stmt.seq_spec (M := fun s t => s = written ∧ t = next) ?_
        ((ih (index + 1) written next (by omega)
          (by simpa only [written, Wasm.Mem.write64_pages] using hMemory) hRest
          (fun i hi hw => ?_) hNextFrame hNextPtr).mono
            (fun _ _ h => h) ?_)
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s t ⟨hs, ht⟩
        subst s t
        refine ⟨ptr + UInt64.ofNat (8 * index), state, words[index], next,
          by simp [Expr.eval, hPtr, U64Op.apply], hEval, ?_, rfl, rfl⟩
        · show (slotAddress ptr index).toNat + 8 ≤ _
          rw [hAddress]; omega
      · by_cases hEq : i = index
        · subst hEq
          exact Memory.read64_write64 ..
        · have hiAddress : (slotAddress ptr i).toNat = ptr.toNat + 8 * i :=
            slotAddress_toNat (by omega)
          rw [Memory.WritesRange.read64 (Memory.WritesRange.write64 start (slotAddress ptr index)
            words[index] (ptr.toNat + 8 * index) (ptr.toNat + 8 * index + 8) (by omega)
            (by omega)) _ (by rw [hiAddress]; omega)]
          exact hPrefix i (by omega) hw
      · rintro s t ⟨hComplete, hFrame', hPtr', hWrites⟩
        exact ⟨hComplete, hFrame', hPtr', hWrite.trans (hWrites.mono (by omega) (le_refl _))⟩

/-- A record template allocates a block for its slots, writes the record's kind, width, and
child mask into the header, and stores the slots, leaving its pointer in `dst` with the facts
of `Heap.NewRecord`. -/
theorem Stmt.record_spec {typeIdx scratch dst : Nat} {values : List (Expr .u64)} {mask : UInt64}
    {initial : Store Unit} {before : State} {heap : Heap} {words : List UInt64}
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hDst : dst < scratch) (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hCount : 0 < values.length) (hShort : values.length ≤ 64)
    (hValues : List.Forall₂ (fun value word => ∀ mem state, State.Frame scratch [dst] before state →
      ∃ next, value.eval mem scratch state = some (word, next)) values words) :
    Triple m (.record dst values mask) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch [dst] before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewRecord initial (heap.allocate (UInt64.ofNat (8 * values.length))) store ptr words
          mask) := by
  have hLength : values.length = words.length := hValues.length_eq
  have hNeed : (UInt64.ofNat (8 * values.length)).toNat = 8 * values.length :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hSize : allocSize (UInt64.ofNat (8 * values.length)) = UInt64.ofNat (8 * values.length) := by
    have h := allocSize_words (values.length - 1) (by omega)
    rwa [show values.length - 1 + 1 = values.length by omega] at h
  generalize hNeedDef : UInt64.ofNat (8 * values.length) = need at hNeed hSize ⊢
  by_cases hFitsNeed : heap.Fits need
  swap
  · -- The block does not fit, so `alloc` traps.
    refine Stmt.seq_spec (M := fun _ _ => False) ?_ Triple.of_false
    refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro s t ⟨hs, ht⟩
    subst s t
    refine ⟨[.i64 need], before, _, by rw [← hNeedDef]; rfl,
      fun env => alloc_spec_or_abort hMemory32 hImports hFunc env heap initial need hHeap
        (by omega) hCap, ?_⟩
    rintro store' out ⟨hFits', -, -⟩
    rw [hSize] at hFits'
    exact absurd hFits' hFitsNeed
  have hBlock := hHeap.allocate_block 1 hFitsNeed
  have hCapacity := allocated_capacity need heap.free
  have hBlockAddress := hBlock.address
  have hBlockMemory := hBlock.memory
  have hBlockBase := hBlock.base
  have hBlockCapacity := hBlock.capacity_eq
  generalize hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr at hBlock ⊢
  generalize hCapDef : allocatedCapacity need heap.free = cap at hBlock hCapacity
  have hBlockAddress' : ptr.toNat + cap.toNat < 4294967296 := by subst hPtrDef hCapDef; exact hBlockAddress
  have hBlockMemory' : ptr.toNat + cap.toNat ≤ (heap.allocateStore initial need 1).mem.pages * 65536 := by
    subst hPtrDef hCapDef; exact hBlockMemory
  have hBlockBase' : 4096 + 48 ≤ ptr.toNat := by subst hPtrDef; exact hBlockBase
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := dst) (.i64 ptr) (by omega)
  have hFrame1 := (State.Frame.refl scratch [dst] before).set? hSet1 (Or.inl (by simp))
  have hPtr1 := State.get_set?_same hSet1
  have hHeaderAddress : ∀ k : UInt64, k.toNat ≤ 48 → (ptr - k).toUInt32.toNat = ptr.toNat - k.toNat :=
    fun k hk => headerAddress_toNat (by omega) (by omega)
  let store1 := heap.allocateStore initial need 1
  let store2 : Store Unit := { store1 with mem := store1.mem.write64 (ptr - 24).toUInt32 1 }
  let store3 : Store Unit :=
    { store2 with mem := store2.mem.write64 (ptr - 16).toUInt32 (UInt64.ofNat values.length) }
  let store4 : Store Unit := { store3 with mem := store3.mem.write64 (ptr - 8).toUInt32 mask }
  have h24 := hHeaderAddress 24 (by decide)
  have h16 := hHeaderAddress 16 (by decide)
  have h8 := hHeaderAddress 8 (by decide)
  have hW2 : Memory.WritesRange store1 store2 (ptr.toNat - 24) (ptr.toNat + 8 * words.length) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [h24]; rfl) (by rw [h24]; simp; omega)
  have hW3 : Memory.WritesRange store2 store3 (ptr.toNat - 24) (ptr.toNat + 8 * words.length) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [h16]; simp; omega) (by rw [h16]; simp; omega)
  have hW4 : Memory.WritesRange store3 store4 (ptr.toNat - 24) (ptr.toNat + 8 * words.length) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [h8]; simp; omega) (by rw [h8]; simp; omega)
  have hPages4 : store4.mem.pages = store1.mem.pages := by
    simp only [store4, store3, store2, Wasm.Mem.write64_pages]
  have hSlotsFit : ptr.toNat + 8 * words.length ≤ cap.toNat + ptr.toNat := by omega
  have hMem4 : ptr.toNat + 8 * words.length ≤ store4.mem.pages * 65536 := by
    rw [hPages4]; exact le_trans (by omega) hBlockMemory'
  refine Stmt.seq_spec (M := fun s t => s = store1 ∧ t = s1) ?_ <|
    Stmt.seq_spec (M := fun s t => s = store2 ∧ t = s1) ?_ <|
    Stmt.seq_spec (M := fun s t => s = store3 ∧ t = s1) ?_ <|
    Stmt.seq_spec (M := fun s t => s = store4 ∧ t = s1) ?_ <|
    (Stmt.storeSlots_spec (words := words) hDst (by omega) values 0 store4 s1 (by omega)
      hMem4 (by simpa using hValues) (fun i hi => absurd hi (Nat.not_lt_zero i))
      hFrame1 hPtr1).mono (fun _ _ h => h) ?_
  · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro s t ⟨hs, ht⟩
    subst s t
    refine ⟨[.i64 need], before, _, by rw [← hNeedDef]; rfl,
      fun env => alloc_spec_or_abort hMemory32 hImports hFunc env heap initial need hHeap
        (by omega) hCap, ?_⟩
    rintro store' out ⟨-, hStore', hOut⟩
    rw [hSize] at hStore' hOut
    exact ⟨s1, by simp [hOut, hPtrDef, State.setAll, hSet1], hStore', rfl⟩
  · refine Stmt.store_spec.mono (fun s t ⟨hs, ht⟩ => ?_) fun _ _ h => h
    rw [hs, ht]
    refine ⟨ptr - 24, s1, 1, s1, by simp [Expr.eval, hPtr1, U64Op.apply], rfl, ?_, rfl, rfl⟩
    rw [h24]; simp; omega
  · refine Stmt.store_spec.mono (fun s t ⟨hs, ht⟩ => ?_) fun _ _ h => h
    rw [hs, ht]
    refine ⟨ptr - 16, s1, UInt64.ofNat values.length, s1, by simp [Expr.eval, hPtr1, U64Op.apply],
      rfl, ?_, rfl, rfl⟩
    rw [h16]; simp only [store2, Wasm.Mem.write64_pages]; simp; omega
  · refine Stmt.store_spec.mono (fun s t ⟨hs, ht⟩ => ?_) fun _ _ h => h
    rw [hs, ht]
    refine ⟨ptr - 8, s1, mask, s1, by simp [Expr.eval, hPtr1, U64Op.apply], rfl, ?_, rfl, rfl⟩
    rw [h8]; simp only [store3, store2, Wasm.Mem.write64_pages]; simp; omega
  rintro s t ⟨hSlots, hFrame, hPtr, hWrites⟩
  have hKind : Memory.WritesRange store2 s (ptr.toNat - 16) (ptr.toNat + 8 * words.length) :=
    (Memory.WritesRange.write64 _ _ _ _ _ (by rw [h16]; rfl) (by rw [h16]; simp; omega)).trans
      ((Memory.WritesRange.write64 _ _ _ _ _ (by rw [h8]; simp; omega)
        (by rw [h8]; simp; omega)).trans (hWrites.mono (by omega) (le_refl _)))
  have hWidth : Memory.WritesRange store3 s (ptr.toNat - 8) (ptr.toNat + 8 * words.length) :=
    (Memory.WritesRange.write64 _ _ _ _ _ (by rw [h8]; rfl) (by rw [h8]; simp; omega)).trans
      (hWrites.mono (by omega) (le_refl _))
  have hMask : Memory.WritesRange store4 s ptr.toNat (ptr.toNat + 8 * words.length) :=
    hWrites.mono (by omega) (le_refl _)
  have hAll : Memory.WritesRange store1 s (ptr.toNat - 24) (ptr.toNat + 8 * words.length) :=
    hW2.trans (hKind.mono (by omega) (le_refl _))
  have hCap1 : capacityAt store1 ptr = cap.toNat := hBlock.capacity_eq
  have hCapS : capacityAt s ptr = cap.toNat := by
    unfold capacityAt at hCap1 ⊢
    rw [hAll.read64 _ (by rw [hHeaderAddress 32 (by decide)]; simp; omega), hCap1]
  have hFresh := hBlock.fresh
  obtain ⟨hMagic1, hCount1, -, -, -, -⟩ := hFresh
  have hGlobals : s.memoryCaps = store1.memoryCaps := by rw [hAll.1]
  refine ⟨ptr, hFrame, hPtr, ⟨?_, fun slots hLen hMaskOf => ?_, hSlots, fun r hR => ?_, ?_, ?_⟩⟩
  · refine (hHeap.allocate 1 hFitsNeed).writesApart hAll fun node hNode => ?_
    have hSep := hBlock.separate node hNode
    simp only [regionsDisjoint] at hSep ⊢
    omega
  · refine ⟨hBlockBase', ?_, ?_, ?_, ?_, ?_, by omega, by rw [hCapS]; omega, by rw [hCapS]; omega,
      ?_, ?_⟩
    · rw [hAll.read64 _ (by rw [hHeaderAddress 48 (by decide)]; simp; omega)]; exact hMagic1
    · rw [hAll.read64 _ (by rw [hHeaderAddress 40 (by decide)]; simp; omega)]; exact hCount1
    · rw [hKind.read64 _ (by rw [h24]; simp; omega)]; exact Memory.read64_write64 ..
    · rw [hWidth.read64 _ (by rw [h16]; simp; omega), hLen, ← hLength]
      exact Memory.read64_write64 ..
    · rw [hMask.read64 _ (by rw [h8]; simp; omega), hMaskOf]; exact Memory.read64_write64 ..
    · rw [hCapS]; have := hBlock.below; exact this
    · rw [hCapS]; exact hBlock.separate
  · obtain ⟨hR', hBytes, hApart⟩ := hR.allocate 1 hHeap hFitsNeed
    rw [hPtrDef, hCapDef] at hApart
    refine ⟨fun a hLow hHigh => ?_, hR', ?_⟩
    · rw [hAll.2.2 a (by simp only [regionsDisjoint] at hApart; omega)]
      exact hBytes a hLow hHigh
    · simp only [block, hCapS]; exact hApart
  · rw [hAll.2.1]; exact allocated_pages_ge initial heap.top need 1 heap.free
  · rw [hGlobals]; exact heap.allocateStore_memoryCaps initial need 1

end Project.IR
