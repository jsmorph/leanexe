import Project.ClobMatchFuel.BookAllocFit
import Project.ClobMatchFuel.BookAllocBump

/-!
# Allocator frames for live fixed arrays

The matching allocator may reuse a represented free node or extend the heap.
This module proves that either outcome preserves a disjoint refcount-one source
array, including the header needed by the later release call.
-/

namespace Project.ClobMatchFuel.AllocatorFrame

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

def OwnedOrderArrayAt (st : Store Unit) (ptr capacity : UInt64)
    (os : List OrderL) : Prop :=
  FreshOrderArrayAt st ptr capacity ∧ OrdersAt st ptr os

def OwnedTradeArrayAt (st : Store Unit) (ptr capacity : UInt64)
    (ts : List TradeL) : Prop :=
  FreshTradeArrayAt st ptr capacity ∧ TradesAt st ptr ts

def FreeListSeparatedFromFixedArray (nodes : List FreeNode)
    (ptr capacity : UInt64) : Prop :=
  ∀ node ∈ nodes, regionsDisjoint (fixedArrayRegion ptr capacity) node.region

theorem fixedArrayAllocFitStore_pages
    (st : Store Unit) (choice : FreeChoice) (stride : UInt64) :
    (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem.pages =
      st.mem.pages := by
  simp only [BookAllocFit.fixedArrayAllocFitStore,
    BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
    Mem.write64_pages]
  split <;> rfl

theorem fixedArrayAllocBumpStore_pages
    (st : Store Unit) (g0 need stride : UInt64) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.pages =
      st.mem.pages := by
    simp [BookAllocBump.fixedArrayAllocBumpStore, fixedArrayHeaderMem,
      Mem.write64_pages]

theorem fixedArrayAllocFitStore_global_of_ne_one
    (st : Store Unit) (choice : FreeChoice) (stride : UInt64)
    (i : Nat) (value : Value) (hi : i ≠ 1)
    (hValue : st.globals.globals[i]? = some value) :
    (BookAllocFit.fixedArrayAllocFitStore st choice stride).globals.globals[i]? =
      some value := by
  have hi' : 1 ≠ i := Ne.symm hi
  by_cases hPrevious : choice.previous = 0
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hi', hValue]
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hValue]

theorem fixedArrayAllocBumpStore_global_of_ne_zero
    (st : Store Unit) (g0 need stride : UInt64)
    (i : Nat) (value : Value) (hi : i ≠ 0)
    (hValue : st.globals.globals[i]? = some value) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).globals.globals[i]? =
      some value := by
  have hi' : 0 ≠ i := Ne.symm hi
  simp [BookAllocBump.fixedArrayAllocBumpStore, hi', hValue]

theorem flatWordsDisjoint_of_fixedArrayRegions
    {aPtr aCapacity bPtr bCapacity : UInt64} {aWords bWords : Nat}
    (ha48 : 48 ≤ aPtr.toNat) (hb48 : 48 ≤ bPtr.toNat)
    (haFit : (aWords + 1) * 8 ≤ aCapacity.toNat)
    (hbFit : (bWords + 1) * 8 ≤ bCapacity.toNat)
    (hsep : regionsDisjoint (fixedArrayRegion aPtr aCapacity)
      (fixedArrayRegion bPtr bCapacity)) :
    flatWordsDisjoint (flatWordsRegion aPtr aWords)
      (flatWordsRegion bPtr bWords) := by
  unfold regionsDisjoint fixedArrayRegion at hsep
  unfold flatWordsDisjoint flatWordsRegion
  omega

theorem MemEqOutsideFlatWords.fixedArray_bytes
    {before after : Store Unit} {target source capacity : UInt64}
    {targetWords : Nat}
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source capacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (a : Nat) (haLow : source.toNat - 48 ≤ a)
    (haHigh : a < source.toNat + capacity.toNat) :
    after.mem.bytes a = before.mem.bytes a := by
  apply hFrame
  unfold regionsDisjoint flatWordsRegion fixedArrayRegion at hsep
  omega

theorem OwnedOrderArrayAt.frame_outsideFlatWords
    {before after : Store Unit}
    {target source sourceCapacity : UInt64} {targetWords : Nat}
    {os : List OrderL}
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source sourceCapacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hOwned : OwnedOrderArrayAt before source sourceCapacity os) :
    OwnedOrderArrayAt after source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    exact MemEqOutsideFlatWords.fixedArray_bytes hsep hFrame a haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem OwnedTradeArrayAt.frame_outsideFlatWords
    {before after : Store Unit}
    {target source sourceCapacity : UInt64} {targetWords : Nat}
    {ts : List TradeL}
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source sourceCapacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hOwned : OwnedTradeArrayAt before source sourceCapacity ts) :
    OwnedTradeArrayAt after source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    exact MemEqOutsideFlatWords.fixedArray_bytes hsep hFrame a haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem FreeListAt.frame_outsideFlatWords
    {before after : Store Unit} {nodes : List FreeNode}
    {target : UInt64} {targetWords : Nat}
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : ∀ node ∈ nodes,
      regionsDisjoint (flatWordsRegion target targetWords) node.region)
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hList : FreeListAt before.mem nodes) :
    FreeListAt after.mem nodes := by
  refine FreeListAt.frame hPages ?_ hList
  intro node hNode offset hOffset
  obtain ⟨hNode48, hNode32, _⟩ := hList.mem_bounds hNode
  have hNodeSep := hsep node hNode
  have hOffsetLow : 8 ≤ offset.toNat := by
    rcases hOffset with rfl | rfl | rfl <;> decide
  have hOffsetHigh : offset.toNat ≤ 48 := by
    rcases hOffset with rfl | rfl | rfl <;> decide
  apply read64_congr
  intro i hi
  apply hFrame
  rw [toUInt32_toNat, toNat_sub_le _ _ (by omega),
    Nat.mod_eq_of_lt (by omega)]
  unfold regionsDisjoint flatWordsRegion FreeNode.region at hNodeSep
  omega

theorem takeFirstFitFrom_some_freeHead
    {mem : Mem} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    freeHead choice.remaining =
      if choice.previous = 0 then choice.next else freeHead nodes := by
  obtain ⟨skipped, tail, hNodes, hPrevious, hNext, hRemaining, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  rw [hRemaining]
  cases skipped with
  | nil =>
      simp only [previousRoot] at hPrevious
      simp [hPrevious, hNext]
  | cons head rest =>
      have hSkipped : head :: rest ≠ [] := by simp
      let predecessor := (head :: rest).getLast hSkipped
      have hSplit : (head :: rest).dropLast ++ [predecessor] = head :: rest :=
        List.dropLast_append_getLast hSkipped
      have hPreviousRoot : choice.previous = predecessor.root := by
        rw [hPrevious, ← hSplit, previousRoot_append_singleton]
      have hPredecessorMem :
          predecessor ∈ (head :: rest) ++ choice.node :: tail := by
        rw [← hSplit]
        simp
      have hPreviousNonzero : choice.previous ≠ 0 := by
        rw [hPreviousRoot]
        exact hList.roots_ne_zero predecessor hPredecessorMem
      simp [hPreviousNonzero, freeHead]

theorem fixedArrayAllocFitStore_global0
    {st : Store Unit} {choice : FreeChoice} {stride g0 : UInt64}
    (hg0 : st.globals.globals[0]? = some (.i64 g0)) :
    (BookAllocFit.fixedArrayAllocFitStore st choice stride).globals.globals[0]? =
      some (.i64 g0) := by
  by_cases hPrevious : choice.previous = 0
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg0]
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg0]

theorem fixedArrayAllocFitStore_global1
    {st : Store Unit} {nodes : List FreeNode} {need stride : UInt64}
    {choice : FreeChoice}
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    (BookAllocFit.fixedArrayAllocFitStore st choice stride).globals.globals[1]? =
      some (.i64 (freeHead choice.remaining)) := by
  have hLength : 1 < st.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hg1).1
  rw [takeFirstFitFrom_some_freeHead hList hTake]
  by_cases hPrevious : choice.previous = 0
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hLength]
  · simp [BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg1]

theorem fixedArrayAllocBumpStore_global0
    (st : Store Unit) (g0 need stride : UInt64)
    (hg0 : st.globals.globals[0]? = some (.i64 g0)) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).globals.globals[0]? =
      some (.i64 (g0 + 48 + need)) := by
  have hLength : 0 < st.globals.globals.length :=
    (List.getElem?_eq_some_iff.mp hg0).1
  simp [BookAllocBump.fixedArrayAllocBumpStore, hLength]

theorem fixedArrayAllocBumpStore_global1
    (st : Store Unit) (g0 need stride head : UInt64)
    (hg1 : st.globals.globals[1]? = some (.i64 head)) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).globals.globals[1]? =
      some (.i64 head) := by
  simp [BookAllocBump.fixedArrayAllocBumpStore, hg1]

theorem freeListAt_fixedArrayAllocFitStore_after
    {before after : Store Unit} {nodes : List FreeNode}
    {need stride : UInt64} {targetWords : Nat} {choice : FreeChoice}
    (hList : FreeListAt before.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hWordsFit : (targetWords + 1) * 8 ≤ choice.node.capacity.toNat)
    (hPages : after.mem.pages =
      (BookAllocFit.fixedArrayAllocFitStore before choice stride).mem.pages)
    (hFrame : MemEqOutsideFlatWords
      (BookAllocFit.fixedArrayAllocFitStore before choice stride) after
      choice.node.root targetWords) :
    FreeListAt after.mem choice.remaining := by
  have hAllocList : FreeListAt
      (BookAllocFit.fixedArrayAllocFitStore before choice stride).mem
      choice.remaining := by
    simpa [BookAllocFit.fixedArrayAllocFitStore] using
      BookAllocFit.freeListAt_fixedArrayAllocFitMem stride hList hTake
  apply FreeListAt.frame_outsideFlatWords hPages _ hFrame hAllocList
  intro node hNode
  have hDisjoint := hList.takeFirstFitFrom_node_disjoint hTake node hNode
  obtain ⟨hChoice48, _, _⟩ :=
    hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
  unfold regionsDisjoint FreeNode.region at hDisjoint
  unfold regionsDisjoint flatWordsRegion FreeNode.region
  omega

theorem freeListAt_fixedArrayAllocBumpStore_after
    {before after : Store Unit} {nodes : List FreeNode}
    {g0 need stride : UInt64} {targetWords : Nat}
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hList : FreeListAt before.mem nodes)
    (hPages : after.mem.pages =
      (BookAllocBump.fixedArrayAllocBumpStore before g0 need stride).mem.pages)
    (hFrame : MemEqOutsideFlatWords
      (BookAllocBump.fixedArrayAllocBumpStore before g0 need stride) after
      (g0 + 48) targetWords) :
    FreeListAt after.mem nodes := by
  have hAllocList := BookAllocBump.freeListAt_fixedArrayAllocBumpStore before
    g0 need stride nodes hFit32 hBelow hList
  have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48, Nat.mod_eq_of_lt (by omega)]
  apply FreeListAt.frame_outsideFlatWords hPages _ hFrame hAllocList
  intro node hNode
  obtain ⟨hNode48, _, _⟩ := hList.mem_bounds hNode
  have hNodeBelow := hBelow node hNode
  unfold regionsDisjoint flatWordsRegion FreeNode.region
  right
  rw [hTargetNat]
  omega

theorem fixedArrayAllocFitMem_bytes
    {mem : Mem} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64} {a : Nat}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (haLow : source.toNat - 48 ≤ a)
    (haHigh : a < source.toNat + sourceCapacity.toNat) :
    (BookAllocFit.fixedArrayAllocFitMem mem choice stride).bytes a =
      mem.bytes a := by
  have frameWrite (current : Mem) (writer : FreeNode)
      (hWriter : writer ∈ nodes) (offset value : UInt64)
      (hOffsetLow : 8 ≤ offset.toNat)
      (hOffsetHigh : offset.toNat ≤ 48) :
      (current.write64 ((writer.root - offset).toUInt32) value).bytes a =
        current.bytes a := by
    obtain ⟨hWriter48, hWriter32, _⟩ := hList.mem_bounds hWriter
    have hdisjoint := hsep writer hWriter
    apply write64_bytes_ne
    rw [toUInt32_toNat,
      toNat_sub_le writer.root offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
    unfold FreeListSeparatedFromFixedArray fixedArrayRegion regionsDisjoint
      FreeNode.region at hdisjoint
    omega
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  have hUnlink : (unlinkFreeChoice mem choice).bytes a = mem.bytes a := by
    by_cases hPrevious : choice.previous = 0
    · simp [unlinkFreeChoice, hPrevious]
    · obtain ⟨skipped, tail, hnodes, hprevious, _, _, _⟩ :=
        takeFirstFitFrom_some_decompose hTake
      have hSkipped : skipped ≠ [] := by
        intro hEmpty
        subst skipped
        simp only [previousRoot] at hprevious
        exact hPrevious hprevious
      let predecessor := skipped.getLast hSkipped
      have hsplit : skipped.dropLast ++ [predecessor] = skipped :=
        List.dropLast_append_getLast hSkipped
      have hPreviousRoot : choice.previous = predecessor.root := by
        rw [hprevious, ← hsplit, previousRoot_append_singleton]
      have hPredecessorMem : predecessor ∈ nodes := by
        rw [hnodes, ← hsplit]
        simp
      rw [unlinkFreeChoice, if_neg hPrevious, hPreviousRoot]
      exact frameWrite mem predecessor hPredecessorMem 8 choice.next
        (by decide) (by decide)
  unfold BookAllocFit.fixedArrayAllocFitMem
  rw [frameWrite _ choice.node hChoiceMem 8 0 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 16 stride (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 24 2 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 32 choice.node.capacity
      (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 40 1 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 48 5501223100278326855
      (by decide) (by decide),
    hUnlink]

theorem ownedOrderArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64}
    {os : List OrderL}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt
      (BookAllocFit.fixedArrayAllocFitStore st choice stride)
      source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem.bytes a =
          st.mem.bytes a := by
    intro a haLow haHigh
    exact fixedArrayAllocFitMem_bytes hList hTake hsep haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region
      (st := st)
      (st' := BookAllocFit.fixedArrayAllocFitStore st choice stride)
      hSource32 hSource48 hCapacity (by
        simp only [BookAllocFit.fixedArrayAllocFitStore,
          BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
          Mem.write64_pages]
        split <;> rfl) hBytes hOwned.2⟩

theorem ownedTradeArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64}
    {ts : List TradeL}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt
      (BookAllocFit.fixedArrayAllocFitStore st choice stride)
      source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem.bytes a =
          st.mem.bytes a := by
    intro a haLow haHigh
    exact fixedArrayAllocFitMem_bytes hList hTake hsep haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region
      (st := st)
      (st' := BookAllocFit.fixedArrayAllocFitStore st choice stride)
      hSource32 hSource48 hCapacity (by
        simp only [BookAllocFit.fixedArrayAllocFitStore,
          BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
          Mem.write64_pages]
        split <;> rfl) hBytes hOwned.2⟩

theorem fixedArrayAllocBumpStore_bytes_below
    (st : Store Unit) (g0 need stride : UInt64) (a : Nat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (ha : a < g0.toNat) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
      st.mem.bytes a := by
  exact fixedArrayHeaderMem_bytes_before st.mem g0 need stride a
    (by omega) ha

theorem ownedOrderArrayAt_fixedArrayAllocBumpStore
    {st : Store Unit} {g0 need stride source sourceCapacity : UInt64}
    {os : List OrderL}
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact fixedArrayAllocBumpStore_bytes_below st g0 need stride a hFit32
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region
      (st := st)
      (st' := BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      hSource32 hSource48 hCapacity rfl hBytes hOwned.2⟩

theorem ownedTradeArrayAt_fixedArrayAllocBumpStore
    {st : Store Unit} {g0 need stride source sourceCapacity : UInt64}
    {ts : List TradeL}
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact fixedArrayAllocBumpStore_bytes_below st g0 need stride a hFit32
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region
      (st := st)
      (st' := BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      hSource32 hSource48 hCapacity rfl hBytes hOwned.2⟩

end Project.ClobMatchFuel.AllocatorFrame
