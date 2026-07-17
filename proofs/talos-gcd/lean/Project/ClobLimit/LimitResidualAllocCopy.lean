import Project.ClobLimit.LimitResidualCopy

/-!
# Residual allocation and copy

This module composes the fresh stride-five allocation with the flat-word copy.
The allocation bounds imply the copy bounds and separate the new payload from
the matcher-produced book.  The continuation receives the completed prefix
invariant and the exact residual local frame.
-/

namespace Project.ClobLimit.LimitResidualAllocCopy

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobMatchFuel.Allocation

set_option Elab.async false in
theorem residualAllocCopyProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (hTop : (data.g0 + 48 + orderArrayBytesU
      (ctx.result.book.length + 1)).toNat =
        data.g0.toNat + 48 +
          (orderArrayBytesU (ctx.result.book.length + 1)).toNat)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final,
      LimitResidualAlloc.CopyLocalsAt final order ctx data data.g0 →
      ∀ st1,
      CopyInvariant
        (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
          (orderArrayBytesU (ctx.result.book.length + 1))
          (UInt64.ofNat (ctx.result.book.length + 1)))
        final (data.g0 + 48) data.book
        (orderArrayBytesU (ctx.result.book.length + 1)) ctx.result.book st1
        (copyLoopFrame final (ctx.result.book.length * 5)) →
      wp «module» rest Q st1
        (copyLoopFrame final (ctx.result.book.length * 5)) env) :
    wp «module» (LimitEntry.residualAllocProg ++
      LimitEntry.residualCopyProg ++ rest) Q st base env := by
  have hNeedNat :
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat =
        orderArrayBytes (ctx.result.book.length + 1) :=
    fixedArrayBytesU_toNat (ctx.result.book.length + 1) 5 hLength
      (by decide) (by
        change fixedArrayBytes (ctx.result.book.length + 1) 5 + 7 <
          UInt64.size at hBytes
        omega)
  have hNeed : 8 ≤
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
  have hTarget48 : 48 ≤ (data.g0 + 48).toNat := by
    rw [hTargetNat]
    omega
  have hSource32 : data.book.toNat +
      (ctx.result.book.length * 5 + 1) * 8 < 4294967296 := by
    have h := hOutput.book32
    unfold fixedArrayBytes at h
    omega
  have hTarget32 : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 <
        4294967296 := by
    rw [hTargetNat]
    have hFit32Nat := hFit32
    rw [hNeedNat] at hFit32Nat
    unfold orderArrayBytes fixedArrayBytes at hFit32Nat
    omega
  have hTargetFit : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
        st.mem.pages * 65536 := by
    rw [hTargetNat]
    have hFitNat := hFit
    rw [hNeedNat] at hFitNat
    unfold orderArrayBytes fixedArrayBytes at hFitNat
    omega
  have hsep : flatWordsDisjoint
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
  rw [List.append_assoc]
  apply LimitResidualAlloc.residualAllocProg_spec env st base order ctx data
    hAlloc hLength hBytes hTop hFit32 hFit hOutput Q
    (LimitEntry.residualCopyProg ++ rest)
  intro final hCopy
  apply LimitResidualCopy.residualCopyProg_spec env
    (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
      (orderArrayBytesU (ctx.result.book.length + 1))
      (UInt64.ofNat (ctx.result.book.length + 1)))
    final order ctx data data.g0
    (orderArrayBytesU (ctx.result.book.length + 1)) hCopy hTotalU hTotal64
    hTargetNat hTarget48 hSource32 hTarget32
  · simpa only [LimitResidualAllocFacts.allocStore_pages] using hTargetFit
  · exact hsep
  · exact LimitResidualCopyInvariant.initial st final order ctx data hCopy
      hNeed hFit32 hTargetNat hOutput
  · exact hDone final hCopy

end Project.ClobLimit.LimitResidualAllocCopy
