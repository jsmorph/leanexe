import Project.ClobLimit.LimitResidualAlloc
import Project.ClobMatchFuel.AllocatorFrame

/-!
# Residual allocation facts

The residual allocator creates a stride-five array above the matcher heap.
These theorems state its persistent page, global, header, length, and memory
facts.  They also preserve both represented matcher arrays below the old heap
top.
-/

namespace Project.ClobLimit.LimitResidualAllocFacts

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

theorem allocStore_pages (st : Store Unit) (g0 g2 need length : UInt64) :
    (LimitResidualAlloc.allocStore st g0 g2 need length).mem.pages =
      st.mem.pages := by
  simp [LimitResidualAlloc.allocStore, LimitResidualAlloc.allocMem,
    Project.Clob.fixedArrayAllocBumpStore_pages, Mem.write64_pages]

theorem allocStore_globals (st : Store Unit) (g0 g2 need length : UInt64) :
    (LimitResidualAlloc.allocStore st g0 g2 need length).globals.globals =
      ((st.globals.globals.set 0 (.i64 (g0 + 48 + need))).set 2
        (.i64 (g2 + 1))) := by
  simp [LimitResidualAlloc.allocStore, LimitResidualAlloc.allocGlobals,
    fixedArrayAllocBumpStore]

theorem allocStore_fresh
    (st : Store Unit) (g0 g2 need length : UInt64)
    (hNeed : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hRoot : (g0 + 48).toNat = g0.toNat + 48) :
    FreshOrderArrayAt
      (LimitResidualAlloc.allocStore st g0 g2 need length)
      (g0 + 48) need := by
  have hFresh := fixedArrayAllocBumpStore_spec st g0 need 5 hNeed hFit32
  have hData : (g0 + 48).toNat ≤ (g0 + 48).toUInt32.toNat := by
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have hWrite := FreshFixedArrayAt.write64_data (value := length) hFresh
    (by rw [hRoot]; omega) hData
  change FreshFixedArrayAt
    (LimitResidualAlloc.allocStore st g0 g2 need length) (g0 + 48) need 5
  unfold FreshFixedArrayAt at hWrite ⊢
  simpa [LimitResidualAlloc.allocStore, LimitResidualAlloc.allocMem] using
    hWrite

theorem allocStore_length
    (st : Store Unit) (g0 g2 need length : UInt64) :
    (LimitResidualAlloc.allocStore st g0 g2 need length).mem.read64
      (g0 + 48).toUInt32 = length := by
  simp [LimitResidualAlloc.allocStore, LimitResidualAlloc.allocMem,
    Mem.read64_write64_same]

theorem allocStore_bytes_before
    (st : Store Unit) (g0 g2 need length : UInt64) (a : Nat)
    (hNeed : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hRoot : (g0 + 48).toNat = g0.toNat + 48)
    (ha : a < g0.toNat) :
    (LimitResidualAlloc.allocStore st g0 g2 need length).mem.bytes a =
      st.mem.bytes a := by
  have hFrame := fixedArrayMem_bytes_before st.mem g0 need 5 length a
    (by omega) ha
  simpa [LimitResidualAlloc.allocStore, LimitResidualAlloc.allocMem,
    fixedArrayAllocBumpStore, fixedArrayMem, toUInt32_eq_ofNat, hRoot] using
    hFrame

theorem ownedOrderArrayAt_allocStore
    {st : Store Unit} {g0 g2 need length source sourceCapacity : UInt64}
    {os : List OrderL}
    (hNeed : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hRoot : (g0 + 48).toNat = g0.toNat + 48)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt
      (LimitResidualAlloc.allocStore st g0 g2 need length)
      source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (LimitResidualAlloc.allocStore st g0 g2 need length).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact allocStore_bytes_before st g0 g2 need length a hNeed hFit32 hRoot
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region hSource32 hSource48 hCapacity
      (allocStore_pages st g0 g2 need length) hBytes hOwned.2⟩

theorem ownedTradeArrayAt_allocStore
    {st : Store Unit} {g0 g2 need length source sourceCapacity : UInt64}
    {ts : List TradeL}
    (hNeed : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hRoot : (g0 + 48).toNat = g0.toNat + 48)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt
      (LimitResidualAlloc.allocStore st g0 g2 need length)
      source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (LimitResidualAlloc.allocStore st g0 g2 need length).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact allocStore_bytes_before st g0 g2 need length a hNeed hFit32 hRoot
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region hSource32 hSource48 hCapacity
      (allocStore_pages st g0 g2 need length) hBytes hOwned.2⟩

end Project.ClobLimit.LimitResidualAllocFacts
