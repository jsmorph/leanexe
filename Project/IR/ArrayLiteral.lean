import Project.IR.Stmt
import Project.Pipeline.RuntimeSpec
import Project.ProofKit.ArrayPrefix

/-!
The rule lemma for the compiler's array-literal template.  The compiler
translates `#[v₀, …, vₖ₋₁]` to a call of `alloc` for `8 * (k + 1)` payload bytes,
a store of the length word, and one store per element.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Stores `values` as the elements from `index` on of the array at local `dst`. -/
def Stmt.storeElements (dst : Nat) : Nat → List (Expr .u64) → Stmt
  | _, [] => .skip
  | index, value :: rest =>
      .seq (.store (.bin .add (.get dst) (.const (UInt64.ofNat (8 * (index + 1))))) value)
        (Stmt.storeElements dst (index + 1) rest)

/-- Local `dst` receives a new array that holds the values of `values`. -/
def Stmt.arrayLiteral (dst : Nat) (values : List (Expr .u64)) : Stmt :=
  .seq (.call 0 [.const (UInt64.ofNat (8 * (values.length + 1)))] [dst])
    (.seq (.store (.get dst) (.const (UInt64.ofNat values.length)))
      (Stmt.storeElements dst 0 values))

theorem allocSize_words (k : Nat) (hk : 8 * (k + 1) < 4294967296) :
    allocSize (UInt64.ofNat (8 * (k + 1))) = UInt64.ofNat (8 * (k + 1)) := by
  have hRound : (UInt64.ofNat (8 * (k + 1)) + 7) / 8 * 8 = UInt64.ofNat (8 * (k + 1)) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.toNat_ofNat',
      UInt64.reduceToNat]
    omega
  unfold allocSize
  rw [hRound, if_neg]
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat]
  omega

/-- The element stores fill an array whose length word is stored, keeping every
local below scratch except `dst`'s scratch neighbors, and write only inside the
array. -/
theorem Stmt.storeElements_spec {scratch dst : Nat} {before : State} {ptr : UInt64}
    {all : Array UInt64} (hDst : dst < scratch) (values : List (Expr .u64)) :
    ∀ (index : Nat) (start : Store Unit) (state : State),
      index + values.length = all.size →
      List.Forall₂ (fun value word => ∀ mem st, State.Frame scratch [dst] before st →
        ∃ next, value.eval mem scratch st = some (word, next)) values (all.toList.drop index) →
      UInt64Array.PrefixAt start ptr all index →
      State.Frame scratch [dst] before state → state.get dst = some (.i64 ptr) →
      Triple m (Stmt.storeElements dst index values) scratch
        (fun s t => s = start ∧ t = state)
        (fun s t => UInt64Array.PrefixAt s ptr all all.size ∧ State.Frame scratch [dst] before t ∧
          t.get dst = some (.i64 ptr) ∧
          Memory.WritesRange start s ptr.toNat (ptr.toNat + 8 * (all.size + 1))) := by
  induction values with
  | nil =>
      intro index start state hSize _ hPrefix hFrame hPtr
      simp only [List.length_nil, Nat.add_zero] at hSize
      subst hSize
      refine Stmt.skip_spec.mono ?_ fun _ _ h => h
      rintro s t ⟨hs, ht⟩
      subst s t
      exact ⟨hPrefix, hFrame, hPtr, .refl _ _ _⟩
  | cons value rest ih =>
      intro index start state hSize hValues hPrefix hFrame hPtr
      simp only [List.length_cons] at hSize
      have hIndex : index < all.size := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hIndex)] at hValues
      obtain ⟨hValue, hRest⟩ := List.forall₂_cons.mp hValues
      simp only [Array.getElem_toList] at hValue
      obtain ⟨next, hEval⟩ := hValue start.mem state hFrame
      have hNextFrame := hFrame.trans (Expr.eval_frame [dst] value start.mem scratch state next _ hEval)
      have hNextPtr : next.get dst = some (.i64 ptr) := by
        rw [Expr.eval_preserves_below value start.mem scratch state next _ dst hEval hDst, hPtr]
      refine Stmt.seq_spec
        (M := fun s t => s = UInt64Array.writeElement start ptr index all[index] ∧ t = next) ?_
        ((ih (index + 1) _ next (by omega) hRest
          (hPrefix.write_next hIndex) hNextFrame hNextPtr).mono (fun _ _ h => h) ?_)
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s t ⟨hs, ht⟩
        subst s t
        exact ⟨ptr + UInt64.ofNat (8 * (index + 1)), state, all[index], next,
          by simp [Expr.eval, hPtr, U64Op.apply], hEval, hPrefix.elementBound index hIndex, rfl,
          rfl⟩
      · rintro s t ⟨hComplete, hFrame', hPtr', hWrites⟩
        exact ⟨hComplete, hFrame', hPtr',
          (UInt64Array.writeElement_frame start ptr all.size index all[index] hPrefix.1
            hIndex).trans hWrites⟩

/-- An array literal allocates a block for its elements, stores the length and
the elements, and leaves its pointer in `dst`, with the facts of
`Heap.NewArray` for `heap.allocate`. -/
theorem Stmt.arrayLiteral_spec {typeIdx scratch dst : Nat} {values : List (Expr .u64)}
    {initial : Store Unit} {before : State} {heap : Heap} {words : List UInt64}
    (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hDst : dst < scratch) (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hHeap : heap.At initial) (hSpace : heap.Room initial m (48 + 8 * (values.length + 1)))
    (hValues : List.Forall₂ (fun value word => ∀ mem state, State.Frame scratch [dst] before state →
      ∃ next, value.eval mem scratch state = some (word, next)) values words) :
    Triple m (.arrayLiteral dst values) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => ∃ ptr, State.Frame scratch [dst] before state ∧
        state.get dst = some (.i64 ptr) ∧
        heap.NewArray initial (heap.allocate (UInt64.ofNat (8 * (values.length + 1)))) store ptr
          words.toArray (48 + 8 * (values.length + 1))) := by
  have hLength : values.length = words.length := hValues.length_eq
  have hAddress := hSpace.address
  have hNeed : (UInt64.ofNat (8 * (values.length + 1))).toNat = 8 * (values.length + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hSize := allocSize_words values.length (by omega)
  generalize hNeedDef : UInt64.ofNat (8 * (values.length + 1)) = need at hNeed hSize ⊢
  have hRoomNeed : heap.Room initial m (48 + need.toNat) := by rw [hNeed]; exact hSpace
  have hBlock := hHeap.allocate_block 1 hRoomNeed
  have hCapacity := allocated_capacity need heap.free
  have hBlockAddress := hBlock.address
  have hBlockMemory := hBlock.memory
  generalize hPtrDef : FixedArrayAllocate.root heap.top need heap.free = ptr at hBlock ⊢
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := dst) (.i64 ptr) (by omega)
  have hFrame1 := (State.Frame.refl scratch [dst] before).set? hSet1 (Or.inl (by simp))
  have hPtr1 := State.get_set?_same hSet1
  have hPtr32 : ptr.toUInt32.toNat = ptr.toNat := by
    rw [Memory.toUInt32_toNat]; subst hPtrDef; omega
  let store2 : Store Unit := { heap.allocateStore initial need 1 with
    mem := (heap.allocateStore initial need 1).mem.write64 ptr.toUInt32
      (UInt64.ofNat words.toArray.size) }
  have hPrefix : UInt64Array.PrefixAt store2 ptr words.toArray 0 := by
    refine UInt64Array.PrefixAt.empty _ _ _ ?_ ?_ (Memory.read64_write64 ..)
    · simp only [List.size_toArray]; subst hPtrDef; omega
    · simp only [store2, Wasm.Mem.write64_pages, List.size_toArray]; subst hPtrDef; omega
  refine Stmt.seq_spec (M := fun s t => s = heap.allocateStore initial need 1 ∧ t = s1) ?_
    (Stmt.seq_spec (M := fun s t => s = store2 ∧ t = s1) ?_
      ((Stmt.storeElements_spec hDst values 0 store2 s1 (by simp [hLength])
        (by simpa using hValues) hPrefix hFrame1 hPtr1).mono (fun _ _ h => h) ?_))
  · refine (Stmt.call_spec (f := allocFunction typeIdx) (by simp [hImports])
      (by simpa [hImports] using hFunc) rfl).mono ?_ fun _ _ h => h
    rintro s t ⟨hs, ht⟩
    subst s t
    refine ⟨[need], before, _, by rw [← hNeedDef]; rfl,
      fun env => alloc_spec hMemory32 hImports hFunc env heap initial need hHeap
        (by rw [hSize]; exact hRoomNeed), ?_⟩
    rintro store' out ⟨hStore', hOut⟩
    rw [hSize] at hStore' hOut
    exact ⟨s1, by simp [hOut, hPtrDef, State.setAll, hSet1], hStore', rfl⟩
  · refine Stmt.store_spec.mono ?_ fun _ _ h => h
    rintro s t ⟨hs, ht⟩
    subst s t
    refine ⟨ptr, s1, UInt64.ofNat words.toArray.size, s1, by simp [Expr.eval, hPtr1], ?_, ?_,
      rfl, rfl⟩
    · simp [Expr.eval, hLength]
    · rw [hPtr32]; subst hPtrDef; omega
  · rintro s t ⟨hComplete, hFrame, hPtr, hWrites⟩
    have hAll : Memory.WritesRange (heap.allocateStore initial need 1) s ptr.toNat
        (ptr.toNat + 8 * (words.toArray.size + 1)) :=
      (Memory.WritesRange.write64 _ ptr.toUInt32 _ _ _ (by omega) (by omega)).trans hWrites
    have hWithin : WritesWithin (heap.allocateStore initial need 1) s ptr.toNat
        (allocatedCapacity need heap.free).toNat := by
      refine ⟨by rw [hAll.1], hAll.2.1, fun address hOutside => hAll.2.2 address ?_⟩
      simp only [List.size_toArray] at hAll ⊢
      omega
    subst hPtrDef
    have hNew := Heap.newArray_of_writes hHeap hRoomNeed hWithin hComplete.complete
      (by simp only [List.size_toArray]; omega)
      (by rw [hAll.1]; exact heap.allocateStore_memoryCaps initial need 1)
    rw [hNeed] at hNew
    exact ⟨_, hFrame, hPtr, hNew⟩

end Project.IR
