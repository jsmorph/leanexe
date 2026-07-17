import Project.ClobDepth.MissingStore

/-!
# Missing-price branch facts

These facts connect bump allocation and length initialization to the copy
invariant.  They also transport the completed append state back to the input
allocator state and owned source array.
-/

namespace Project.ClobDepth.MissingBranchFacts

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.MissingCopyInvariant

def target (g0 : UInt64) : UInt64 :=
  g0 + 48

def capacity (levels : List LevelL) : UInt64 :=
  fixedArrayBytesU (levels.length + 1) 2

def allocatedStore (st : Store Unit) (g0 g2 : UInt64)
    (levels : List LevelL) : Store Unit :=
  MissingFinish.finishStore
    (fixedArrayAllocBumpStore st g0 (capacity levels) 2)
    (target g0) (UInt64.ofNat (levels.length + 1)) g2

theorem allocatedStore_pages
    (st : Store Unit) (g0 g2 : UInt64) (levels : List LevelL) :
    (allocatedStore st g0 g2 levels).mem.pages = st.mem.pages := by
  simp [allocatedStore, MissingFinish.finishStore,
    fixedArrayAllocBumpStore_pages]

theorem allocatedStore_globals
    (st : Store Unit) (g0 g2 : UInt64) (levels : List LevelL) :
    (allocatedStore st g0 g2 levels).globals.globals =
      (st.globals.globals.set 0
        (.i64 (g0 + 48 + capacity levels))).set 2 (.i64 (g2 + 1)) := by
  rfl

theorem allocatedStore_bytes_before
    (st : Store Unit) (g0 g2 : UInt64) (levels : List LevelL)
    (hRoot : (target g0).toNat = g0.toNat + 48)
    (hTarget32 : (target g0).toNat < 4294967296)
    (a : Nat) (ha : a < g0.toNat) :
    (allocatedStore st g0 g2 levels).mem.bytes a = st.mem.bytes a := by
  unfold allocatedStore MissingFinish.finishStore target
  simp only [fixedArrayAllocBumpStore]
  rw [write64_bytes_lo _ _ _ (by
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by simpa [target] using hTarget32),
      show (g0 + 48).toNat = g0.toNat + 48 by simpa [target] using hRoot]
    omega)]
  exact fixedArrayHeaderMem_bytes_before st.mem g0 (capacity levels) 2 a
    (by omega) ha

theorem allocatedStore_fresh
    (st : Store Unit) (g0 g2 : UInt64) (levels : List LevelL)
    (hNeed8 : 8 ≤ (capacity levels).toNat)
    (hFit32 : g0.toNat + 48 + (capacity levels).toNat < 4294967296)
    (hRoot : (target g0).toNat = g0.toNat + 48) :
    FreshFixedArrayAt (allocatedStore st g0 g2 levels)
      (target g0) (capacity levels) 2 := by
  have hFresh := fixedArrayAllocBumpStore_spec st g0 (capacity levels) 2
    hNeed8 hFit32
  have hRoot' : (g0 + 48).toNat = g0.toNat + 48 := by
    simpa [target] using hRoot
  have hData :
      (g0 + 48).toNat ≤ (g0 + 48).toUInt32.toNat := by
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by rw [hRoot']; omega)]
  have hWritten := FreshFixedArrayAt.write64_data
    (value := UInt64.ofNat (levels.length + 1)) hFresh
    (by rw [hRoot']; omega) hData
  unfold FreshFixedArrayAt at hWritten ⊢
  simpa only [allocatedStore, MissingFinish.finishStore, target] using hWritten

theorem allocatedStore_length
    (st : Store Unit) (g0 g2 : UInt64) (levels : List LevelL) :
    (allocatedStore st g0 g2 levels).mem.read64 (target g0).toUInt32 =
      UInt64.ofNat (levels.length + 1) := by
  simp [allocatedStore, MissingFinish.finishStore,
    Mem.read64_write64_same]

theorem allocatedStore_source
    (st : Store Unit) (g0 g2 source sourceCapacity : UInt64)
    (levels : List LevelL)
    (hSource32 :
      source.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSourceCapacity :
      fixedArrayBytes levels.length 2 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hRoot : (target g0).toNat = g0.toNat + 48)
    (hTarget32 : (target g0).toNat < 4294967296)
    (hOwned : OwnedLevelArrayAt st source sourceCapacity levels) :
    OwnedLevelArrayAt (allocatedStore st g0 g2 levels)
      source sourceCapacity levels := by
  apply hOwned.frame_region hSource32 hSource48 hSourceCapacity
    (allocatedStore_pages st g0 g2 levels)
  intro a _ ha
  exact allocatedStore_bytes_before st g0 g2 levels hRoot hTarget32 a
    (by omega)

theorem copyInvariant_initial
    (st : Store Unit) (base : Locals) (g0 g2 source sourceCapacity : UInt64)
    (levels : List LevelL)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hCounter : base.locals[15]? = some (.i64 0))
    (hNeed8 : 8 ≤ (capacity levels).toNat)
    (hFit32 : g0.toNat + 48 + (capacity levels).toNat < 4294967296)
    (hRoot : (target g0).toNat = g0.toNat + 48)
    (hSource32 :
      source.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSourceCapacity :
      fixedArrayBytes levels.length 2 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedLevelArrayAt st source sourceCapacity levels) :
    CopyInvariant (allocatedStore st g0 g2 levels) base (target g0) source
      (capacity levels) levels (allocatedStore st g0 g2 levels) base := by
  apply MissingCopyInvariant.initial _ _ _ _ _ _ hLocals hValues hCounter
    (allocatedStore_fresh st g0 g2 levels hNeed8 hFit32 hRoot)
    (allocatedStore_length st g0 g2 levels)
  exact (allocatedStore_source st g0 g2 source sourceCapacity levels
    hSource32 hSource48 hSourceCapacity hSourceBelow hRoot
    (by rw [hRoot]; omega) hOwned).2

structure ResultState (st0 st : Store Unit) (g0 g2 source sourceCapacity :
    UInt64) (levels : List LevelL) (level : LevelL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals =
    (st0.globals.globals.set 0
      (.i64 (g0 + 48 + capacity levels))).set 2 (.i64 (g2 + 1))
  resultOwned : OwnedLevelArrayAt st (target g0) (capacity levels)
    (levels ++ [level])
  sourceOwned : OwnedLevelArrayAt st source sourceCapacity levels
  bytesBefore : ∀ a : Nat, a < g0.toNat →
    st.mem.bytes a = st0.mem.bytes a

theorem ResultState.of_finish
    {st0 st : Store Unit} {g0 g2 source sourceCapacity : UInt64}
    {levels : List LevelL} {level : LevelL}
    (hFinish : MissingStoreFacts.FinishState
      (allocatedStore st0 g0 g2 levels) st (target g0) source
      (capacity levels) levels level)
    (hSource32 :
      source.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSourceCapacity :
      fixedArrayBytes levels.length 2 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hRoot : (target g0).toNat = g0.toNat + 48)
    (hTarget32 : (target g0).toNat < 4294967296)
    (hOwned : OwnedLevelArrayAt st0 source sourceCapacity levels) :
    ResultState st0 st g0 g2 source sourceCapacity levels level := by
  have hPages : st.mem.pages = st0.mem.pages :=
    hFinish.pages.trans (allocatedStore_pages st0 g0 g2 levels)
  have hBefore (a : Nat) (ha : a < g0.toNat) :
      st.mem.bytes a = st0.mem.bytes a := by
    rw [hFinish.outside a (Or.inl (by omega))]
    exact allocatedStore_bytes_before st0 g0 g2 levels hRoot hTarget32 a ha
  refine {
    pages := hPages
    globals := hFinish.globals.trans
      (allocatedStore_globals st0 g0 g2 levels)
    resultOwned := hFinish.levelsOwned
    sourceOwned := ?_
    bytesBefore := hBefore }
  apply hOwned.frame_region hSource32 hSource48 hSourceCapacity hPages
  intro a _ ha
  exact hBefore a (by omega)

end Project.ClobDepth.MissingBranchFacts
