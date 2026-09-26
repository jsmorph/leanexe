import Project.ClobLimit.HeapAppendAllocate
import Project.ClobLimit.HeapAppendFinish
import Project.ClobLimit.HeapAppendCopy

namespace Project.ClobLimit.HeapAppendFrames
open Wasm Project.Common Project.Clob Project.ClobLimit Project.ProofKit
open Project.ClobMatchFuel.LoopInvariant
open Project.ClobLimit.LimitResidualPrepare

def headerFrame (base : Locals) (ctx : Context) (previous current capacity next root : UInt64) : Locals :=
  let frame := HeapAppendAllocate.resultFrame base ctx previous current capacity next root
  { frame with locals := frame.locals.set 40 (.i64 root) }

theorem header_params (base : Locals) (ctx : Context) (previous current capacity next root : UInt64) :
    (headerFrame base ctx previous current capacity next root).params = base.params := rfl

theorem header_locals (base : Locals) (ctx : Context) (previous current capacity next root : UInt64)
    (hLocals : base.locals.length = 55) :
    (headerFrame base ctx previous current capacity next root).locals.length = 55 := by
  simp [headerFrame, HeapAppendAllocate.resultFrame, FixedArraySearch.frame, hLocals]

theorem header_get_before (base : Locals) (ctx : Context)
    (previous current capacity next root : UInt64) (i : Nat)
    (hi : i < 49) (hne : i ≠ 40) (hLocals : base.locals.length = 55) :
    (headerFrame base ctx previous current capacity next root).locals[i]? = base.locals[i]? := by
  simp [headerFrame, HeapAppendAllocate.resultFrame, FixedArraySearch.frame, hLocals,
    hi, Ne.symm hne, List.getElem?_append, List.getElem?_take]

structure CopyLocalsAt (frame : Locals) (root : UInt64) (order : OrderL)
    (ctx : Context) (data : HeapRunMatch.OutputData) : Prop where
  stores : HeapAppendFinish.StoreLocalsAt frame root ctx.result.book.length
    { order with oqty := ctx.result.remaining }
  source : frame.locals[36]? = some (.i64 data.book)
  total : frame.locals[38]? = some (.i64 (UInt64.ofNat ctx.result.book.length * 5))
  trades : frame.locals[23]? = some (.i64 data.trades)
  status : frame.locals[31]? = some (.i64 0)

theorem header_facts (base : Locals) (order : OrderL) (ctx : Context)
    (data : HeapRunMatch.OutputData) (previous current capacity next root : UInt64)
    (h : OrderLocalsAt base order ctx data) :
    CopyLocalsAt (headerFrame base ctx previous current capacity next root) root order ctx data := by
  have hl := h.fields.locals
  have hb := header_get_before base ctx previous current capacity next root
  refine {
    stores := {
      params := h.fields.params
      locals := header_locals base ctx previous current capacity next root hl
      values := rfl
      length := ?_
      target := ?_
      oid := ?_
      trader := ?_
      side := ?_
      price := ?_
      quantity := ?_ }
    source := ?_
    total := ?_
    trades := ?_
    status := ?_ }
  · exact (hb 37 (by decide) (by decide) hl).trans h.length
  · simp [headerFrame, HeapAppendAllocate.resultFrame, FixedArraySearch.frame, hl]
  · exact (hb 42 (by decide) (by decide) hl).trans h.fields.oid
  · exact (hb 43 (by decide) (by decide) hl).trans h.fields.trader
  · exact (hb 44 (by decide) (by decide) hl).trans h.fields.side
  · exact (hb 45 (by decide) (by decide) hl).trans h.fields.price
  · exact (hb 46 (by decide) (by decide) hl).trans h.fields.remaining
  · exact (hb 36 (by decide) (by decide) hl).trans h.fields.source
  · exact (hb 38 (by decide) (by decide) hl).trans h.total
  · exact (hb 23 (by decide) (by decide) hl).trans h.fields.tradesResult
  · exact (hb 31 (by decide) (by decide) hl).trans h.fields.status

theorem CopyLocalsAt.counter (h : CopyLocalsAt frame root order ctx data)
    (word : Nat) (hCounter : frame.validIndex 47) :
    CopyLocalsAt (FixedArrayCopy.counterFrame frame 47 word hCounter) root order ctx data := by
  rcases h with ⟨⟨hp, hl, hv, hn, hr, hi, ht, hs, hpr, hq⟩, hsrc, htotal, htrades, hstatus⟩
  constructor
  · constructor <;> simp_all [FixedArrayCopy.counterFrame, Locals.set, Locals.set?]
  all_goals simp_all [FixedArrayCopy.counterFrame, Locals.set, Locals.set?]

#print axioms header_facts
#print axioms CopyLocalsAt.counter
end Project.ClobLimit.HeapAppendFrames
