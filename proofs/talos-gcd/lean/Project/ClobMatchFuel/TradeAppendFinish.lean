import Project.ClobMatchFuel.TradeAppendStore

/-!
# Matched-trade append finalization

The common matching branch writes four fields after copying the old trade
array.  This proof identifies those generated stores with `appendTradeStore`.
Its continuation receives the fresh root and the exact extended trade array.
-/

namespace Project.ClobMatchFuel.TradeAppendFinish

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.TradeAppendCopy
  Project.ClobMatchFuel.TradeAppendStore

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_trade_finish" "(" hParams:term "," hLocals:term ","
    hLength:term "," hTaker:term "," hMaker:term ","
    hPrice:term "," hQty:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hLength),
    ($hTaker), ($hMaker), ($hPrice), ($hQty)])

def tradeResultFrame (base : Locals) (target : UInt64)
    (totalWords : Nat) : Locals :=
  { tradeCopyFrame base target totalWords with values := [.i64 target] }

def tradeFinishProg : Wasm.Program :=
  [
  .localGet 70,
  .localGet 67,
  .constI64 4,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 72,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 4,
  .mulI64,
  .constI64 2,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 73,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 4,
  .mulI64,
  .constI64 3,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 74,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 4,
  .mulI64,
  .constI64 4,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 75,
  .store64 0,
  .localGet 70
]

set_option Elab.async false in
theorem tradeFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity : UInt64)
    (ts : List TradeL) (trade : TradeL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hLengthLocal : base.locals[58]? =
      some (.i64 (UInt64.ofNat ts.length)))
    (hTakerLocal : base.locals[63]? = some (.i64 trade.ttakerId))
    (hMakerLocal : base.locals[64]? = some (.i64 trade.tmakerId))
    (hPriceLocal : base.locals[65]? = some (.i64 trade.tprice))
    (hQtyLocal : base.locals[66]? = some (.i64 trade.tqty))
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat + ((ts.length + 1) * 4 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hSource : TradesAt st0 source ts)
    (hInv : tradeCopyInv st0 base target source g2 arrayCapacity
      (UInt64.ofNat (ts.length + 1)) ts st1
        (tradeCopyFrame base target (ts.length * 4)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone :
      TradesAt (appendTradeStore st1 target ts.length trade) target
          (ts ++ [trade]) →
        FreshTradeArrayAt (appendTradeStore st1 target ts.length trade)
          target arrayCapacity →
        wp «module» rest Q (appendTradeStore st1 target ts.length trade)
          (tradeResultFrame base target (ts.length * 4)) env) :
    wp «module» (tradeFinishProg ++ rest) Q st1
      (tradeCopyFrame base target (ts.length * 4)) env := by
  obtain ⟨word, hword, hFrame, hPages, _, hFresh, hLength, _, hCopied⟩ :=
    hInv
  have hTotal64 : ts.length * 4 < UInt64.size := by
    change ts.length * 4 < 18446744073709551616
    omega
  have hLength64 : ts.length < UInt64.size := by
    change ts.length < 18446744073709551616
    omega
  have hWordU : UInt64.ofNat ts.length * 4 = UInt64.ofNat word := by
    have h := congrArg (fun s : Locals => s.locals[62]?) hFrame
    simpa [tradeCopyFrame, hLocals] using h
  have hWordEq : word = ts.length * 4 := by
    have h := congrArg UInt64.toNat hWordU
    rw [UInt64.toNat_mul, toNat_ofNat_lt hLength64,
      show (4 : UInt64).toNat = 4 by rfl, Nat.mod_eq_of_lt hTotal64,
      toNat_ofNat_lt (by omega)] at h
    omega
  subst word
  have hTotalEq : UInt64.ofNat (ts.length * 4) =
      UInt64.ofNat ts.length * 4 := by
    apply UInt64.toNat.inj
    rw [toNat_ofNat_lt hTotal64, UInt64.toNat_mul,
      toNat_ofNat_lt hLength64]
    have h4 : (4 : UInt64).toNat = 4 := rfl
    rw [h4, Nat.mod_eq_of_lt hTotal64]
  have hLengthGet : base.locals[58] = .i64 (UInt64.ofNat ts.length) := by
    apply Option.some.inj
    calc
      some base.locals[58] = base.locals[58]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat ts.length)) := hLengthLocal
  have hTakerGet : base.locals[63] = .i64 trade.ttakerId := by
    apply Option.some.inj
    calc
      some base.locals[63] = base.locals[63]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.ttakerId) := hTakerLocal
  have hMakerGet : base.locals[64] = .i64 trade.tmakerId := by
    apply Option.some.inj
    calc
      some base.locals[64] = base.locals[64]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tmakerId) := hMakerLocal
  have hPriceGet : base.locals[65] = .i64 trade.tprice := by
    apply Option.some.inj
    calc
      some base.locals[65] = base.locals[65]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tprice) := hPriceLocal
  have hQtyGet : base.locals[66] = .i64 trade.tqty := by
    apply Option.some.inj
    calc
      some base.locals[66] = base.locals[66]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tqty) := hQtyLocal
  simp only [tradeFinishProg, tradeCopyFrame, List.cons_append,
    List.nil_append]
  wp_run_trade_finish (hParams, hLocals, hLengthGet, hTakerGet,
    hMakerGet, hPriceGet, hQtyGet)
  try simp
  have hBound (field : Nat) (hfield : field < 4) :
      (target.toNat + (ts.length * 4 + field + 1) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hPages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hBound 0 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 1 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 2 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 3 (by omega)))]
  have hTradesFinal := tradesAt_appendTradeStore st1 target ts trade
    hTarget32 (by simpa only [toUInt32_eq_ofNat] using hLength) (by
      rw [Nat.mod_eq_of_lt (by omega), hPages]
      omega)
    (by
      intro j hj field hfield
      exact (hCopied (j * 4 + field) (by omega)).trans
        (hSource.tradeWord_eq j field hj hfield))
    (by
      intro j hj field hfield
      rw [Nat.mod_eq_of_lt (by omega), hPages]
      omega)
  have hFreshFinal := freshTradeArrayAt_appendTradeStore st1 target
    arrayCapacity ts.length trade hTarget48 hTarget32 hFresh
  simpa only [appendTradeStore, tradeResultFrame, tradeCopyFrame,
    hTotalEq] using hDone hTradesFinal hFreshFinal

end Project.ClobMatchFuel.TradeAppendFinish
