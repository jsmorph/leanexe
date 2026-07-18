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
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobLimit.LimitResidualFinishFacts
  Project.ClobMatchFuel.Allocation
  Project.ClobPostOnly.AppendStore

set_option maxRecDepth 1048576


structure ResultLocalsAt (final : Locals) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Prop where
  params : final.params.length = 6
  locals : final.locals.length = 53
  values : final.values = []
  status : final.locals[31]? = some (.i64 0)
  book : final.locals[32]? = some (.i64 (data.g0 + 48))
  trades : final.locals[33]? = some (.i64 data.trades)

def resultFrame (base : Locals) (data : InternalLoopResult.OutputData)
    (word : Nat) : Locals :=
  let copied := copyLoopFrame base word
  { copied with
    locals := ((copied.locals.set 28 (.i64 (data.g0 + 48))).set 32
      (.i64 (data.g0 + 48))).set 33 (.i64 data.trades)
    values := [] }

theorem resultFrame_resultLocals
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (word : Nat)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data data.g0) :
    ResultLocalsAt (resultFrame base data word) ctx data := by
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

set_option Elab.async false in
theorem residualFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (capacity : UInt64)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data data.g0)
    (hInvariant : CopyInvariant st0 base (data.g0 + 48) data.book capacity
      ctx.result.book st1
      (copyLoopFrame base (ctx.result.book.length * 5)))
    (hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
      ctx.result.book.length * 5)
    (hTotal64 : ctx.result.book.length * 5 < UInt64.size)
    (hRoot : (data.g0 + 48).toNat = data.g0.toNat + 48)
    (hTarget48 : 48 ≤ (data.g0 + 48).toNat)
    (hTarget32 : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : (data.g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
        st0.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st2,
      FinishState st0 st2 data.g0 capacity data.book ctx.result.book
        { order with oqty := ctx.result.remaining } →
      ∀ final, ResultLocalsAt final ctx data →
      wp «module» rest Q st2 final env) :
    wp «module» (LimitEntry.residualFinishProg ++ rest) Q st1
      (copyLoopFrame base (ctx.result.book.length * 5)) env := by
  have hState := hInvariant.at_end hCopy.orderLocals.fields.locals hTotalU
    hTotal64
  have hParams := hCopy.orderLocals.fields.params
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  have hLength : base.locals[35] =
      .i64 (UInt64.ofNat ctx.result.book.length) := getElem_of_some hCopy.orderLocals.length
  have hTarget : base.locals[38] = .i64 (data.g0 + 48) := getElem_of_some hCopy.target
  have hOid : base.locals[40] = .i64 order.oid := getElem_of_some hCopy.orderLocals.fields.oid
  have hTrader : base.locals[41] = .i64 order.otrader := getElem_of_some hCopy.orderLocals.fields.trader
  have hSide : base.locals[42] = .i64 order.oside := getElem_of_some hCopy.orderLocals.fields.side
  have hPrice : base.locals[43] = .i64 order.oprice := getElem_of_some hCopy.orderLocals.fields.price
  have hRemaining : base.locals[44] = .i64 ctx.result.remaining := getElem_of_some hCopy.orderLocals.fields.remaining
  have hTrades : base.locals[23] = .i64 data.trades := getElem_of_some hCopy.orderLocals.fields.tradesResult
  have hLengthNat : (UInt64.ofNat ctx.result.book.length).toNat =
      ctx.result.book.length := toNat_ofNat_lt (by omega)
  simp only [LimitEntry.residualFinishProg, LimitEntry.residualStoreProg,
    LimitEntry.residualResultProg, copyLoopFrame, List.cons_append,
    List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hLength, hTarget, hOid, hTrader, hSide, hPrice, hRemaining, hTrades]
  try simp [hRoot, hLengthNat, hTotalU]
  have hWriteBound (field : Nat) (hField1 : 1 ≤ field)
      (hField5 : field ≤ 5) :
      (data.g0.toNat + 48 +
        (ctx.result.book.length * 5 + field) * 8) % 4294967296 + 8 ≤
          st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by rw [← hRoot]; omega), hState.pages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hWriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 2 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 3 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 4 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 5 (by omega) (by omega)))]
  have hFinish := LimitResidualFinishFacts.finish
    (order := { order with oqty := ctx.result.remaining }) hState hRoot
    hTarget48 hTarget32 hTargetFit
  have hResult := resultFrame_resultLocals base order ctx data
    (ctx.result.book.length * 5) hCopy
  have hContinue := hNext
    (finishStore st1 data.g0 ctx.result.book.length
      { order with oqty := ctx.result.remaining }) hFinish
    (resultFrame base data (ctx.result.book.length * 5)) hResult
  simpa [finishStore, appendOrderStore, resultFrame, copyLoopFrame, hRoot]
    using hContinue

end Project.ClobLimit.LimitResidualFinish
