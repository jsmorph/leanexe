import Project.ClobLimit.LimitResidualFinish
import Project.ClobLimit.LimitResidualAllocCopy

namespace Project.ClobLimit.LimitResidualBook

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobLimit.LimitResidualFinishFacts LimitResidualAllocation

theorem residualBookProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : MatchOutput.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hOutput : MatchOutput.OutputAt ctx st data)
    (hBounds : LimitResidualBounds.Facts st ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      FinishState (store st ctx data) st1 (root ctx data) (capacity ctx data)
        data.book ctx.result.book { order with oqty := ctx.result.remaining } →
      ∀ final, LimitResidualFinish.ResultLocalsAt final ctx data (root ctx data) →
        wp «module» rest Q st1 final env) :
    wp «module» (LimitEntry.residualAllocProg ++ LimitEntry.residualCopyProg ++
      LimitEntry.residualFinishProg ++ rest) Q st base env := by
  rw [List.append_assoc, List.append_assoc]
  apply LimitResidualAllocCopy.residualAllocCopyProg_spec env st base order ctx data
    hAlloc hOutput hBounds Q (LimitEntry.residualFinishProg ++ rest)
  intro final hCopy st1 hInvariant
  apply LimitResidualFinish.residualFinishProg_spec env (store st ctx data)
    st1 final order ctx data (root ctx data) (capacity ctx data) hCopy hInvariant
    hBounds.totalU hBounds.total64 hBounds.allocation.root48 hBounds.target32
  · rw [LimitResidualAllocFacts.store_pages hBounds.allocation]
    exact hBounds.targetFit
  · exact hDone

end Project.ClobLimit.LimitResidualBook
