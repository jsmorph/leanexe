import Project.ClobLimit.LimitResidualCopy
import Project.ClobLimit.LimitResidualBounds

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
  Project.ClobLimit.LimitResidualBounds
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
  have hBounds := LimitResidualBounds.derive st ctx data hLength hBytes
    hFit32 hFit hOutput
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
      (orderArrayBytesU (ctx.result.book.length + 1)) hCopy hBounds.totalU
    hBounds.total64 hBounds.targetNat hBounds.target48 hBounds.source32
    hBounds.target32
  · simpa only [LimitResidualAllocFacts.allocStore_pages] using
      hBounds.targetFit
  · exact hBounds.separated
  · exact LimitResidualCopyInvariant.initial st final order ctx data hCopy
      hBounds.needMin hFit32 hBounds.targetNat hOutput
  · exact hDone final hCopy

end Project.ClobLimit.LimitResidualAllocCopy
