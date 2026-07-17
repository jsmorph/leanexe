import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.TradeAllocAppend

/-!
# Partial-fill trade preparation

The partial-fill branch records its replacement book before allocating the
result trade array.  It reads the matched maker identifier and price, uses the
remaining taker quantity as the fill quantity, and prepares the trade allocator
locals.  This module proves that instruction bridge against the source arrays.
-/

namespace Project.ClobMatchFuel.PartialTradePrepare

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_prepare" "(" hParams:term "," hLocals:term ","
    hValues:term "," hTaker:term "," hBook:term "," hTrades:term ","
    hRemaining:term "," hIndex:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hTaker), ($hBook), ($hTrades), ($hRemaining), ($hIndex)])

def partialTradePrepareProg : Wasm.Program :=
  [
  .localSet 63,
  .localGet 63,
  .localSet 21,
  .localGet 17,
  .localSet 64,
  .localGet 64,
  .localSet 66,
  .localGet 9,
  .localSet 72,
  .localGet 15,
  .localSet 78,
  .localGet 33,
  .localSet 79,
  .localGet 79,
  .localGet 78,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 78,
    .localGet 79,
    .constI64 5,
    .mulI64,
    .constI64 1,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 73,
  .localGet 15,
  .localSet 78,
  .localGet 33,
  .localSet 79,
  .localGet 79,
  .localGet 78,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 78,
    .localGet 79,
    .constI64 5,
    .mulI64,
    .constI64 4,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 74,
  .localGet 18,
  .localSet 75,
  .localGet 66,
  .wrapI64,
  .load64 0,
  .localSet 67,
  .localGet 67,
  .constI64 4,
  .mulI64,
  .localSet 68,
  .localGet 67,
  .constI64 1,
  .addI64,
  .localSet 69
  ]

def partialTradePrepareFrame (base : Locals) (newBook oldBook oldTrades : UInt64)
    (taker maker : OrderL) (remaining : UInt64) (i : Nat)
    (ts : List TradeL) : Locals :=
  { base with
    locals := ((((((((((((((base.locals.set 54 (.i64 newBook)).set 12
      (.i64 newBook)).set 55 (.i64 oldTrades)).set 57
      (.i64 oldTrades)).set 63 (.i64 taker.oid)).set 69
      (.i64 oldBook)).set 70 (.i64 (UInt64.ofNat i))).set 64
      (.i64 maker.oid)).set 69 (.i64 oldBook)).set 70
      (.i64 (UInt64.ofNat i))).set 65 (.i64 maker.oprice)).set 66
      (.i64 remaining)).set 58 (.i64 (UInt64.ofNat ts.length))).set 59
      (.i64 (UInt64.ofNat ts.length * 4))).set 60
      (.i64 (UInt64.ofNat ts.length + 1))
    values := [] }

set_option Elab.async false in
theorem partialTradePrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newBook oldBook oldTrades remaining : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [.i64 newBook])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (hTrades : TradesAt st oldTrades ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (partialTradePrepareFrame base newBook oldBook oldTrades taker os[i]!
        remaining i ts) env) :
    wp «module» (partialTradePrepareProg ++ rest) Q st base env := by
  have hTakerGet : base.locals[0] = .i64 taker.oid := by
    apply Option.some.inj
    calc
      some base.locals[0] = base.locals[0]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 taker.oid) := hTakerLocal
  have hBookGet : base.locals[6] = .i64 oldBook := by
    apply Option.some.inj
    calc
      some base.locals[6] = base.locals[6]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 oldBook) := hBookLocal
  have hTradesGet : base.locals[8] = .i64 oldTrades := by
    apply Option.some.inj
    calc
      some base.locals[8] = base.locals[8]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 oldTrades) := hTradesLocal
  have hRemainingGet : base.locals[9] = .i64 remaining := by
    apply Option.some.inj
    calc
      some base.locals[9] = base.locals[9]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 remaining) := hRemainingLocal
  have hIndexGet : base.locals[24] = .i64 (UInt64.ofNat i) := by
    apply Option.some.inj
    calc
      some base.locals[24] = base.locals[24]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat i)) := hIndexLocal
  have hBookLengthRead :
      st.mem.read64 (UInt32.ofNat (oldBook.toNat % 4294967296)) =
        UInt64.ofNat os.length := hOrders.1.1
  have hBookLengthBound :
      oldBook.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hOrders.1.2
  have hTradesLengthRead :
      st.mem.read64 (UInt32.ofNat (oldTrades.toNat % 4294967296)) =
        UInt64.ofNat ts.length := hTrades.1.1
  have hTradesLengthBound :
      oldTrades.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hTrades.1.2
  have hFieldBound (field : Nat) (hfield : field < 5) :
      (oldBook.toNat + (i * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 :=
    hOrders.orderWord_bound i field hi hfield
  have hFieldRead (field : Nat) (hfield : field < 5) :
      st.mem.read64 (UInt32.ofNat
        ((oldBook.toNat + (i * 5 + field + 1) * 8) % 4294967296)) =
        os[i]!.word field := by
    simpa only [orderWord] using hOrders.orderWord_eq i field hi hfield
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hOrdersLength64]
    exact hi
  simp only [partialTradePrepareProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hTakerGet, hBookGet, hTradesGet,
    hRemainingGet, hIndexGet)
  rw [if_neg (Nat.not_lt.mpr hBookLengthBound), hBookLengthRead,
    if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hTakerGet, hBookGet, hTradesGet,
    hRemainingGet, hIndexGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 0 (by omega))),
    hFieldRead 0 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hTakerGet, hBookGet, hTradesGet,
    hRemainingGet, hIndexGet)
  rw [if_neg (Nat.not_lt.mpr hBookLengthBound), hBookLengthRead,
    if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hTakerGet, hBookGet, hTradesGet,
    hRemainingGet, hIndexGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 3 (by omega))),
    hFieldRead 3 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hTakerGet, hBookGet, hTradesGet,
    hRemainingGet, hIndexGet)
  rw [if_neg (Nat.not_lt.mpr hTradesLengthBound), hTradesLengthRead]
  simpa only [partialTradePrepareFrame,
    List.getElem!_eq_getElem?_getD] using hDone

end Project.ClobMatchFuel.PartialTradePrepare
