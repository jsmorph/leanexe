import Project.ClobLimit.LimitResidualResult

/-!
# Complete valid residual branch

This module composes the residual status call, source preparation, allocation,
copying, append stores, and result assignments.  The caller supplies the final
allocation bounds and receives the complete physical residual result.
-/

namespace Project.ClobLimit.LimitResidualBranch

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant
  Project.ClobMatchFuel.Allocation

set_option Elab.async false in
theorem residualProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (hFloor : 48 ≤ ctx.initialG0.toNat)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat <=
        st.mem.pages * 65536)
    (hOutput : MatchOutput.OutputAt ctx st data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : forall st1,
      LimitResidualResult.ResultAt st st1 ctx data order ->
      forall final, LimitResidualFinish.ResultLocalsAt final ctx data (LimitResidualAllocation.root ctx data) ->
        wp «module» rest Q st1 final env) :
    wp «module» (LimitEntry.residualProg ++ rest) Q st
      { LimitRunMatchResult.residualConditionFrame book order ctx data with
        values := [] } env := by
  have hBounds := LimitResidualBounds.derive st ctx data hLength hBytes hFloor hFit32 hFit hOutput
  rw [LimitEntry.residualProg_decomposition]
  simp only [LimitEntry.residualPrepareProg,
    LimitEntry.residualArrayPrepareProg, List.append_assoc]
  apply LimitResidualStatus.residualStatusProg_spec env st book order ctx data
  apply LimitResidualPrepare.residualOrderPrepareProg_spec env st book order
    ctx data hOutput hLength
  intro prepared hOrder
  apply LimitResidualAllocPrepare.residualAllocPrepareProg_spec env st
    prepared order ctx data hOrder hOutput hLength hBytes
  intro allocated hAlloc
  apply LimitResidualBook.residualBookProg_spec env st allocated order ctx data
    hAlloc hOutput hBounds
  intro st1 hFinish final hResult
  exact hDone st1
    (LimitResidualResult.of_finish st st1 ctx data order hOutput hBounds hFinish)
    final hResult

end Project.ClobLimit.LimitResidualBranch
