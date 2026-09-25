import Project.ClobLimit.LimitResidualAllocFacts

namespace Project.ClobLimit.LimitResidualBounds

open Wasm Project.Runtime Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame Project.ProofKit LimitResidualAllocation

structure Facts (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData) : Prop where
  allocation : LimitResidualAllocFacts.Facts st ctx data
  needNat : (need ctx).toNat = orderArrayBytes (ctx.result.book.length + 1)
  needMin : 8 ≤ (need ctx).toNat
  total64 : ctx.result.book.length * 5 < UInt64.size
  totalU : (UInt64.ofNat ctx.result.book.length * 5).toNat = ctx.result.book.length * 5
  target32 : (root ctx data).toNat + ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296
  targetFit : (root ctx data).toNat + ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ st.mem.pages * 65536
  bookSeparated : flatWordsDisjoint
    (flatWordsRegion (root ctx data) ((ctx.result.book.length + 1) * 5))
    (flatWordsRegion data.book (ctx.result.book.length * 5))
  tradesSeparated : regionsDisjoint
    (flatWordsRegion (root ctx data) ((ctx.result.book.length + 1) * 5))
    (fixedArrayRegion data.trades data.tradesCapacity)
  bump : data.g0.toNat + 48 + (need ctx).toNat ≤ 4294967296 ∧
    (st.mem.pages < FixedArrayBump.requiredPages data.g0 (need ctx) →
      FixedArrayBump.requiredPages data.g0 (need ctx) ≤ st.memoryCap «module» 0)
  headerFit : (root ctx data).toUInt32.toNat + 8 ≤ (allocated st ctx data).mem.pages * 65536

theorem derive (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 < UInt64.size)
    (hFloor : 48 ≤ ctx.initialG0.toNat)
    (hFit32 : data.g0.toNat + 48 + (need ctx).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 + (need ctx).toNat ≤ st.mem.pages * 65536)
    (hOutput : MatchOutput.OutputAt ctx st data) : Facts st ctx data := by
  have hNeedNat : (need ctx).toNat = orderArrayBytes (ctx.result.book.length + 1) :=
    fixedArrayBytesU_toNat (ctx.result.book.length + 1) 5 hLength
      (by decide) (by
        change fixedArrayBytes (ctx.result.book.length + 1) 5 + 7 < UInt64.size at hBytes
        omega)
  have hNeedMin : 8 ≤ (need ctx).toNat := by
    rw [hNeedNat]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hTotal64 : ctx.result.book.length * 5 < UInt64.size := by
    unfold orderArrayBytes fixedArrayBytes at hBytes
    omega
  have hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat = ctx.result.book.length * 5 := by
    rw [UInt64.toNat_mul, toNat_ofNat_lt (by omega : ctx.result.book.length < UInt64.size)]
    change (ctx.result.book.length * 5) % UInt64.size = ctx.result.book.length * 5
    exact Nat.mod_eq_of_lt hTotal64
  have hAlloc := LimitResidualAllocFacts.derive st ctx data hOutput hFloor hNeedMin hFit32 hFit
  have hCapacity := hAlloc.capacityMin
  have hTarget32 := hAlloc.root32
  have hTargetFit := hAlloc.rootFit
  have hTarget48 := hAlloc.root48
  have hWords : ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ (capacity ctx data).toNat := by
    rw [hNeedNat] at hCapacity
    unfold orderArrayBytes fixedArrayBytes at hCapacity
    omega
  refine {
    allocation := hAlloc
    needNat := hNeedNat
    needMin := hNeedMin
    total64 := hTotal64
    totalU := hTotalU
    target32 := by omega
    targetFit := by omega
    bookSeparated := ?_
    tradesSeparated := ?_
    bump := ⟨by omega, ?_⟩
    headerFit := ?_ }
  · exact flatWordsDisjoint_of_fixedArrayRegions hTarget48 hOutput.book48 hWords
      (by have h := hOutput.bookCapacity; unfold fixedArrayBytes at h; omega) hAlloc.bookSeparate
  · have hSeparate := hAlloc.tradesSeparate
    unfold regionsDisjoint fixedArrayRegion flatWordsRegion at *
    omega
  · intro hGrow
    unfold FixedArrayBump.requiredPages at hGrow
    omega
  · rw [toUInt32_toNat, Nat.mod_eq_of_lt (by omega), hAlloc.pages]
    omega

end Project.ClobLimit.LimitResidualBounds
