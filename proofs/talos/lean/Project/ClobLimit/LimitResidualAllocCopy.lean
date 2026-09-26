import Project.ClobLimit.LimitResidualCopy
import Project.ClobLimit.LimitResidualBounds

namespace Project.ClobLimit.LimitResidualAllocCopy

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobMatchFuel.Allocation LimitResidualAllocation

theorem residualAllocCopyProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : MatchOutput.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hOutput : MatchOutput.OutputAt ctx st data)
    (hBounds : LimitResidualBounds.Facts st ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final,
      LimitResidualAlloc.CopyLocalsAt final order ctx data (root ctx data) →
      ∀ st1, CopyInvariant (store st ctx data) final (root ctx data) data.book
        (capacity ctx data) ctx.result.book st1
        (copyLoopFrame final (ctx.result.book.length * 5)) →
      wp «module» rest Q st1 (copyLoopFrame final (ctx.result.book.length * 5)) env) :
    wp «module» (LimitEntry.residualAllocProg ++ LimitEntry.residualCopyProg ++ rest)
      Q st base env := by
  rw [List.append_assoc]
  apply LimitResidualAlloc.residualAllocProg_spec env st base order ctx data
    hAlloc hOutput (fun _ => hBounds.bump) hBounds.headerFit Q (LimitEntry.residualCopyProg ++ rest)
  intro final hCopy
  apply LimitResidualCopy.residualCopyProg_spec env (store st ctx data)
    final order ctx data (root ctx data) (capacity ctx data) hCopy hBounds.totalU
    hBounds.total64 hBounds.allocation.root48
    (by have h := hOutput.book32; unfold fixedArrayBytes at h; omega)
    hBounds.target32
  · rw [LimitResidualAllocFacts.store_pages hBounds.allocation]
    exact hBounds.targetFit
  · exact hBounds.bookSeparated
  · exact LimitResidualCopyInvariant.initial st final order ctx data hCopy
      hBounds.needMin hBounds.allocation hOutput
  · exact hDone final hCopy

end Project.ClobLimit.LimitResidualAllocCopy
