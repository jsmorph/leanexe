import Project.ClobLimit.LimitResidualAllocFrame
import Project.ClobLimit.LimitResidualAllocation

namespace Project.ClobLimit.LimitResidualAlloc

open Wasm Project.Common Project.Clob Project.ClobLimit Project.Runtime
  Project.ClobLimit.MatchInvariant Project.ClobMatchFuel.Allocation
  Project.ProofKit

structure CopyLocalsAt (base : Locals) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData) (target : UInt64) : Prop where
  orderLocals : LimitResidualPrepare.OrderLocalsAt base order ctx data
  target : base.locals[40]? = some (.i64 target)
  counter : base.locals[41]? = some (.i64 0)

def copyFrame (base : Locals) (target : UInt64) : Locals :=
  { base with
    locals := (base.locals.set 40 (.i64 target)).set 41 (.i64 0)
    values := [] }

theorem copyFrame_copyLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData) (target : UInt64)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data) :
    CopyLocalsAt (copyFrame base target) order ctx data target := by
  rcases hOrder with ⟨hFields, hLength, hTotal, hAppendLength⟩
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBookResult, hTradesResult, hStatus,
      hSource, hOid, hTrader, hSide, hPrice, hRemaining, hScratch⟩
  constructor
  · constructor
    · refine {
        params := by simpa [copyFrame] using hParams
        locals := by simpa [copyFrame] using hLocals
        values := by simp [copyFrame]
        bookResult := by simpa [copyFrame] using hBookResult
        tradesResult := by simpa [copyFrame] using hTradesResult
        status := by simpa [copyFrame] using hStatus
        source := by simpa [copyFrame] using hSource
        oid := by simpa [copyFrame] using hOid
        trader := by simpa [copyFrame] using hTrader
        side := by simpa [copyFrame] using hSide
        price := by simpa [copyFrame] using hPrice
        remaining := by simpa [copyFrame] using hRemaining
        scratch := by simpa [copyFrame] using hScratch }
    · simpa [copyFrame] using hLength
    · simpa [copyFrame] using hTotal
    · simpa [copyFrame] using hAppendLength
  · simp [copyFrame, hLocals]
  · simp [copyFrame, hLocals]

def finishProg : Wasm.Program :=
  [.localGet 60, .localSet 46, .localGet 46, .wrapI64,
    .localGet 45, .store64 0, .constI64 0, .localSet 47]

set_option maxRecDepth 1048576 in
theorem program_eq : LimitEntry.residualAllocProg =
    FixedArrayAllocate.preparedProgram 55 5 ++ finishProg := by
  rfl

set_option maxRecDepth 1048576

theorem finish_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : MatchOutput.OutputData)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data)
    (hRoot : base.locals[54]? = some (.i64 (LimitResidualAllocation.root ctx data)))
    (hFit : (LimitResidualAllocation.root ctx data).toUInt32.toNat + 8 ≤
      (LimitResidualAllocation.allocated st ctx data).mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, CopyLocalsAt final order ctx data (LimitResidualAllocation.root ctx data) →
      wp «module» rest Q (LimitResidualAllocation.store st ctx data) final env) :
    wp «module» (finishProg ++ rest) Q (LimitResidualAllocation.allocated st ctx data) base env := by
  have hParams := hOrder.fields.params
  have hLocals := hOrder.fields.locals
  have hValues := hOrder.fields.values
  have hLength := getElem_of_some hOrder.appendLength
  have hResult := getElem_of_some hRoot
  simp only [finishProg, List.cons_append, List.nil_append]
  simp [wp_simp, hParams, hLocals, hValues, hLength, hResult]
  have hBound : (LimitResidualAllocation.root ctx data).toNat % 4294967296 + 8 ≤
      (LimitResidualAllocation.allocated st ctx data).mem.pages * 65536 := by
    simpa [toUInt32_toNat] using hFit
  rw [if_neg (Nat.not_lt.mpr hBound)]
  simpa [LimitResidualAllocation.store, copyFrame, toUInt32_eq_ofNat, UInt64.ofNat_add] using
    hNext (copyFrame base (LimitResidualAllocation.root ctx data))
      (copyFrame_copyLocals base order ctx data _ hOrder)

theorem residualAllocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : MatchOutput.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hOutput : MatchOutput.OutputAt ctx st data)
    (hBump : takeFirstFitFrom 0 (LimitResidualAllocation.need ctx) data.nodes = none →
      data.g0.toNat + 48 + (LimitResidualAllocation.need ctx).toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages data.g0 (LimitResidualAllocation.need ctx) ≤
        st.memoryCap «module» 0)
    (hFit : (LimitResidualAllocation.root ctx data).toUInt32.toNat + 8 ≤
      (LimitResidualAllocation.allocated st ctx data).mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, CopyLocalsAt final order ctx data (LimitResidualAllocation.root ctx data) →
      wp «module» rest Q (LimitResidualAllocation.store st ctx data) final env) :
    wp «module» (LimitEntry.residualAllocProg ++ rest) Q st base env := by
  obtain ⟨capacity, next, hFrame⟩ := LimitResidualAllocFrame.prepared base order ctx data hAlloc
  have hParams := hAlloc.orderLocals.fields.params
  have hLocals := hAlloc.orderLocals.fields.locals
  have hSaved : (base.locals.take 49).length = 49 := by simp [hLocals]
  rw [program_eq, List.append_assoc]
  rw [hFrame]
  apply FixedArrayAllocate.preparedProgram_spec «module» env st base.params
    (base.locals.take 49) [] 55 (by omega) data.g0 (LimitResidualAllocation.need ctx) 5
    capacity next ctx.expectedG2 data.nodes hOutput.global0 hOutput.global1 hOutput.global2
    hOutput.freeList hBump hOutput.pageLimit rfl
  intro previous current capacity next
  apply finish_spec env st _ order ctx data
  · exact LimitResidualAllocFrame.orderLocals base order ctx data hAlloc.orderLocals _ _ _ _ _ _
  · simp [FixedArraySearch.frame, hSaved, LimitResidualAllocation.root]
  · exact hFit
  · exact hNext

end Project.ClobLimit.LimitResidualAlloc
