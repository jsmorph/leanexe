import Project.ClobLimit.LimitResidualCopyInvariant

/-!
# Residual allocation bounds

The residual array allocation and its copy and finish phases use the same
normalized byte, address, and separation facts.  This module derives them once
from the matcher output and the allocation premises.
-/

namespace Project.ClobLimit.LimitResidualBounds

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation

structure Facts (st : Store Unit) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Prop where
  needNat :
    (orderArrayBytesU (ctx.result.book.length + 1)).toNat =
      orderArrayBytes (ctx.result.book.length + 1)
  needMin : 8 <=
    (orderArrayBytesU (ctx.result.book.length + 1)).toNat
  total64 : ctx.result.book.length * 5 < UInt64.size
  totalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
    ctx.result.book.length * 5
  targetNat : (data.g0 + 48).toNat = data.g0.toNat + 48
  target48 : 48 <= (data.g0 + 48).toNat
  source32 : data.book.toNat +
    (ctx.result.book.length * 5 + 1) * 8 < 4294967296
  target32 : (data.g0 + 48).toNat +
    ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296
  targetFit : (data.g0 + 48).toNat +
    ((ctx.result.book.length + 1) * 5 + 1) * 8 <=
      st.mem.pages * 65536
  separated : flatWordsDisjoint
    (flatWordsRegion (data.g0 + 48)
      ((ctx.result.book.length + 1) * 5))
    (flatWordsRegion data.book (ctx.result.book.length * 5))

theorem derive
    (st : Store Unit) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat <=
        st.mem.pages * 65536)
    (hOutput : InternalLoopResult.OutputAt ctx st data) :
    Facts st ctx data := by
  have hNeedNat :
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat =
        orderArrayBytes (ctx.result.book.length + 1) :=
    fixedArrayBytesU_toNat (ctx.result.book.length + 1) 5 hLength
      (by decide) (by
        change fixedArrayBytes (ctx.result.book.length + 1) 5 + 7 <
          UInt64.size at hBytes
        omega)
  have hNeedMin : 8 <=
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat := by
    rw [hNeedNat]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hTotal64 : ctx.result.book.length * 5 < UInt64.size := by
    unfold orderArrayBytes fixedArrayBytes at hBytes
    omega
  have hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
      ctx.result.book.length * 5 := by
    rw [UInt64.toNat_mul,
      toNat_ofNat_lt (by omega : ctx.result.book.length < UInt64.size)]
    have hFive : (5 : UInt64).toNat = 5 := rfl
    rw [hFive, Nat.mod_eq_of_lt hTotal64]
  have hTargetNat : (data.g0 + 48).toNat = data.g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat data.g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hTarget48 : 48 <= (data.g0 + 48).toNat := by
    rw [hTargetNat]
    omega
  have hSource32 : data.book.toNat +
      (ctx.result.book.length * 5 + 1) * 8 < 4294967296 := by
    have h := hOutput.book32
    unfold fixedArrayBytes at h
    omega
  have hTarget32 : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296 := by
    rw [hTargetNat]
    have hFit32Nat := hFit32
    rw [hNeedNat] at hFit32Nat
    unfold orderArrayBytes fixedArrayBytes at hFit32Nat
    omega
  have hTargetFit : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 <=
        st.mem.pages * 65536 := by
    rw [hTargetNat]
    have hFitNat := hFit
    rw [hNeedNat] at hFitNat
    unfold orderArrayBytes fixedArrayBytes at hFitNat
    omega
  have hSeparated : flatWordsDisjoint
      (flatWordsRegion (data.g0 + 48)
        ((ctx.result.book.length + 1) * 5))
      (flatWordsRegion data.book (ctx.result.book.length * 5)) := by
    unfold flatWordsDisjoint flatWordsRegion
    right
    have hCapacity := hOutput.bookCapacity
    have hBelow := hOutput.bookBelow
    unfold fixedArrayBytes at hCapacity
    rw [hTargetNat]
    omega
  exact {
    needNat := hNeedNat
    needMin := hNeedMin
    total64 := hTotal64
    totalU := hTotalU
    targetNat := hTargetNat
    target48 := hTarget48
    source32 := hSource32
    target32 := hTarget32
    targetFit := hTargetFit
    separated := hSeparated }

end Project.ClobLimit.LimitResidualBounds
