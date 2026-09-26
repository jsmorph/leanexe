import Project.ClobLimit.LimitResidualFinishFacts

/-!
# Residual book finish

The residual finish writes the five appended order fields and assigns the
three exported result locals.  The instruction theorem consumes the completed
copy invariant and applies the separately compiled book-finalization facts.
Its continuation receives the represented extended book and exact result
frame.
-/

namespace Project.ClobLimit.LimitResidualFinish

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant
  Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobLimit.LimitResidualFinishFacts
  Project.ClobMatchFuel.Allocation
  Project.ClobLimit.OrderAppendStore

set_option maxRecDepth 1048576


structure ResultLocalsAt (final : Locals) (ctx : Context)
    (data : MatchOutput.OutputData) (target : UInt64) : Prop where
  params : final.params.length = 6
  locals : final.locals.length = 55
  values : final.values = []
  status : final.locals[31]? = some (.i64 0)
  book : final.locals[33]? = some (.i64 target)
  trades : final.locals[35]? = some (.i64 data.trades)

def resultFrame (base : Locals) (data : MatchOutput.OutputData)
    (target : UInt64) (word : Nat) : Locals :=
  let copied := copyLoopFrame base word
  { copied with
    locals := (((copied.locals.set 32 (.i64 target)).set 33 (.i64 target)).set 34
      (base.locals[22]!)).set 35 (.i64 data.trades)
    values := [] }

theorem resultFrame_resultLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData) (target : UInt64) (word : Nat)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data target) :
    ResultLocalsAt (resultFrame base data target word) ctx data target := by
  have hParams := hCopy.orderLocals.fields.params
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  refine {
    params := by simpa [resultFrame, copyLoopFrame] using hParams
    locals := by simpa [resultFrame, copyLoopFrame] using hLocals
    values := by simp [resultFrame, copyLoopFrame]
    status := by
      simpa [resultFrame, copyLoopFrame, hLocals] using
        hCopy.orderLocals.fields.status
    book := by simp [resultFrame, copyLoopFrame, hLocals]
    trades := by simp [resultFrame, copyLoopFrame, hLocals] }

set_option maxHeartbeats 8000000 in
set_option Elab.async false in
theorem residualFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData) (target capacity : UInt64)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data target)
    (hInvariant : CopyInvariant st0 base target data.book capacity
      ctx.result.book st1
      (copyLoopFrame base (ctx.result.book.length * 5)))
    (hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
      ctx.result.book.length * 5)
    (hTotal64 : ctx.result.book.length * 5 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
        st0.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st2,
      FinishState st0 st2 target capacity data.book ctx.result.book
        { order with oqty := ctx.result.remaining } →
      ∀ final, ResultLocalsAt final ctx data target →
      wp «module» rest Q st2 final env) :
    wp «module» (LimitEntry.residualFinishProg ++ rest) Q st1
      (copyLoopFrame base (ctx.result.book.length * 5)) env := by
  have hState := hInvariant.at_end hCopy.orderLocals.fields.locals hTotalU
    hTotal64
  have hParams := hCopy.orderLocals.fields.params
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  have hLength : base.locals[37] =
      .i64 (UInt64.ofNat ctx.result.book.length) := getElem_of_some hCopy.orderLocals.length
  have hTarget : base.locals[40] = .i64 target := getElem_of_some hCopy.target
  have hOid : base.locals[42] = .i64 order.oid := getElem_of_some hCopy.orderLocals.fields.oid
  have hTrader : base.locals[43] = .i64 order.otrader := getElem_of_some hCopy.orderLocals.fields.trader
  have hSide : base.locals[44] = .i64 order.oside := getElem_of_some hCopy.orderLocals.fields.side
  have hPrice : base.locals[45] = .i64 order.oprice := getElem_of_some hCopy.orderLocals.fields.price
  have hRemaining : base.locals[46] = .i64 ctx.result.remaining := getElem_of_some hCopy.orderLocals.fields.remaining
  have hTrades : base.locals[23] = .i64 data.trades := getElem_of_some hCopy.orderLocals.fields.tradesResult
  have hLengthNat : (UInt64.ofNat ctx.result.book.length).toNat =
      ctx.result.book.length := toNat_ofNat_lt (by omega)
  simp only [LimitEntry.residualFinishProg, LimitEntry.residualStoreProg,
    LimitEntry.residualResultProg, copyLoopFrame, List.cons_append,
    List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hLength, hTarget, hOid, hTrader, hSide, hPrice, hRemaining, hTrades]
  try simp [hLengthNat, hTotalU]
  have hWriteBound (field : Nat) (hField1 : 1 ≤ field)
      (hField5 : field ≤ 5) :
      (target.toNat +
        (ctx.result.book.length * 5 + field) * 8) % 4294967296 + 8 ≤
          st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hState.pages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hWriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 2 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 3 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 4 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 5 (by omega) (by omega)))]
  have hFinish := LimitResidualFinishFacts.finish
    (order := { order with oqty := ctx.result.remaining }) hState
    hTarget48 hTarget32 hTargetFit
  have hResult := resultFrame_resultLocals base order ctx data target
    (ctx.result.book.length * 5) hCopy
  have hContinue := hNext
    (finishStore st1 target ctx.result.book.length
      { order with oqty := ctx.result.remaining }) hFinish
    (resultFrame base data target (ctx.result.book.length * 5)) hResult
  simpa [finishStore, appendOrderStore, resultFrame, copyLoopFrame, hLocals]
    using hContinue

end Project.ClobLimit.LimitResidualFinish
