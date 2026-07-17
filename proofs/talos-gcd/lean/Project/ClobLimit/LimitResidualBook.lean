import Project.ClobLimit.LimitResidualFinish

/-!
# Complete residual book program

This module composes residual allocation, payload copying, appended-order
stores, and result-local assignments.  Its continuation receives the final
represented book and exact result frame.
-/

namespace Project.ClobLimit.LimitResidualBook

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobLimit.LimitResidualFinishFacts
  Project.ClobLimit.LimitResidualBounds
  Project.ClobMatchFuel.Allocation

set_option Elab.async false in
theorem residualBookProg_spec
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
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat <=
        st.mem.pages * 65536)
    (hOutput : InternalLoopResult.OutputAt ctx st data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : forall st1,
      FinishState
        (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
          (orderArrayBytesU (ctx.result.book.length + 1))
          (UInt64.ofNat (ctx.result.book.length + 1)))
        st1 data.g0 (orderArrayBytesU (ctx.result.book.length + 1))
        data.book ctx.result.book
        { order with oqty := ctx.result.remaining } ->
      forall final, LimitResidualFinish.ResultLocalsAt final ctx data ->
        wp «module» rest Q st1 final env) :
    wp «module» (LimitEntry.residualAllocProg ++
      LimitEntry.residualCopyProg ++ LimitEntry.residualFinishProg ++ rest)
      Q st base env := by
  have hBounds := LimitResidualBounds.derive st ctx data hLength hBytes
    hFit32 hFit hOutput
  rw [List.append_assoc, List.append_assoc]
  apply LimitResidualAllocCopy.residualAllocCopyProg_spec env st base order
    ctx data hAlloc hLength hBytes hTop hFit32 hFit hOutput Q
      (LimitEntry.residualFinishProg ++ rest)
  intro final hCopy st1 hInvariant
  apply LimitResidualFinish.residualFinishProg_spec env
    (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
      (orderArrayBytesU (ctx.result.book.length + 1))
      (UInt64.ofNat (ctx.result.book.length + 1)))
    st1 final order ctx data
    (orderArrayBytesU (ctx.result.book.length + 1)) hCopy hInvariant
    hBounds.totalU hBounds.total64 hBounds.targetNat hBounds.target48
    hBounds.target32
  · simpa only [LimitResidualAllocFacts.allocStore_pages] using
      hBounds.targetFit
  · exact hDone

end Project.ClobLimit.LimitResidualBook
