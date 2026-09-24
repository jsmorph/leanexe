import Project.ClobLimit.LimitResidualAllocPrepare
import Project.ProofKit.FixedArrayAllocatePrepared

namespace Project.ClobLimit.LimitResidualAllocFrame

open Wasm Project.Common Project.Clob Project.ClobLimit Project.Runtime
  Project.ClobLimit.MatchInvariant Project.ClobMatchFuel.Allocation
  Project.ProofKit.FixedArraySearch

def frame (base : Locals) (need previous current capacity next result : UInt64) : Locals :=
  Project.ProofKit.FixedArraySearch.frame base.params (base.locals.take 49) []
    need previous current capacity next result

theorem orderLocals (base : Locals) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data)
    (need previous current capacity next result : UInt64) :
    LimitResidualPrepare.OrderLocalsAt
      (frame base need previous current capacity next result) order ctx data := by
  rcases hOrder with ⟨hFields, hLength, hTotal, hAppendLength⟩
  rcases hFields with
    ⟨hParams, hLocals, hValues, hBook, hTrades, hStatus, hSource,
      hOid, hTrader, hSide, hPrice, hRemaining, hScratch⟩
  constructor
  · refine {
      params := hParams
      locals := by simp [frame, Project.ProofKit.FixedArraySearch.frame, hLocals]
      values := rfl
      bookResult := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hBook
      tradesResult := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hTrades
      status := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hStatus
      source := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hSource
      oid := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hOid
      trader := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hTrader
      side := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hSide
      price := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hPrice
      remaining := by simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hRemaining
      scratch := ⟨capacity, next, by simp [frame, Project.ProofKit.FixedArraySearch.frame, hLocals]⟩ }
  · simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hLength
  · simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hTotal
  · simpa [frame, Project.ProofKit.FixedArraySearch.frame, hLocals] using hAppendLength

theorem prepared (base : Locals) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data) :
    ∃ capacity next : UInt64,
      base = frame base (orderArrayBytesU (ctx.result.book.length + 1))
        0 (freeHead data.nodes) capacity next 0 := by
  obtain ⟨capacity, next, hCapacity, hNext⟩ := hAlloc.orderLocals.fields.scratch
  refine ⟨capacity, next, ?_⟩
  have hLocals := hAlloc.orderLocals.fields.locals
  have hValues := hAlloc.orderLocals.fields.values
  apply Project.ProofKit.Frame.ext
  · rfl
  · apply List.ext_getElem?
    intro i
    by_cases hLow : i < 49
    · simp [frame, Project.ProofKit.FixedArraySearch.frame, hLocals, hLow, List.getElem?_append, List.getElem?_take]
    by_cases hHigh : i < 55
    · have h49 : 49 ≤ i := by omega
      interval_cases i <;>
        simp [frame, Project.ProofKit.FixedArraySearch.frame, hLocals,
          getElem_of_some hAlloc.need, getElem_of_some hAlloc.previous,
          getElem_of_some hAlloc.current, getElem_of_some hAlloc.result,
          getElem_of_some hCapacity, getElem_of_some hNext]
    · have hFrameLength :
          (frame base (orderArrayBytesU (ctx.result.book.length + 1))
            0 (freeHead data.nodes) capacity next 0).locals.length = 55 := by
        simp [frame, Project.ProofKit.FixedArraySearch.frame, hLocals]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · exact hValues

end Project.ClobLimit.LimitResidualAllocFrame
