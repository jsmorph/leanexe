import Project.ClobLimit.InternalFullTradePrepare

/-!
# Full-fill trade finalization

The full-fill branch records its fresh trade root and computes the next
remaining quantity.  The selected maker contributes its full quantity to the
trade, so the continuation receives `remaining - os[i]!.oqty`.  This module
ends before the generated release and recursive-state transition.
-/

namespace Project.ClobLimit.InternalFullTradeFinish

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_finish" "(" hParams:term "," hLocals:term ","
    hValues:term "," hRemaining:term "," hBook:term ","
    hIndex:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hRemaining), ($hBook), ($hIndex)])

def fullTradeFinishProg : Wasm.Program :=
  [
  .localSet 38,
  .localGet 38,
  .localSet 39,
  .localGet 10,
  .localGet 7,
  .localSet 56,
  .localGet 25,
  .localSet 57,
  .localGet 57,
  .localGet 56,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 56,
    .localGet 57,
    .constI64 5,
    .mulI64,
    .constI64 5,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .subI64,
  .localSet 40
  ]

def fullTradeFinishFrame (base : Locals) (newTrades oldBook : UInt64)
    (i : Nat) (remaining makerQty : UInt64) : Locals :=
  { base with
    locals := ((((base.locals.set 27 (.i64 newTrades)).set 28
      (.i64 newTrades)).set 45 (.i64 oldBook)).set 46
      (.i64 (UInt64.ofNat i))).set 29 (.i64 (remaining - makerQty))
    values := [] }

set_option Elab.async false in
theorem fullTradeFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newTrades oldBook remaining : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [.i64 newTrades])
    (hRemainingLocal : base.params[10]? = some (.i64 remaining))
    (hBookLocal : base.params[7]? = some (.i64 oldBook))
    (hIndexLocal : base.locals[14]? = some (.i64 (UInt64.ofNat i)))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (fullTradeFinishFrame base newTrades oldBook i remaining os[i]!.oqty)
      env) :
    wp «module» (fullTradeFinishProg ++ rest) Q st base env := by
  have hRemainingGet : base.params[10] = .i64 remaining := by
    apply Option.some.inj
    calc
      some base.params[10] = base.params[10]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 remaining) := hRemainingLocal
  have hBookGet : base.params[7] = .i64 oldBook := by
    apply Option.some.inj
    calc
      some base.params[7] = base.params[7]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 oldBook) := hBookLocal
  have hIndexGet : base.locals[14] = .i64 (UInt64.ofNat i) := by
    apply Option.some.inj
    calc
      some base.locals[14] = base.locals[14]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat i)) := hIndexLocal
  have hBookLengthRead :
      st.mem.read64 (UInt32.ofNat (oldBook.toNat % 4294967296)) =
        UInt64.ofNat os.length := hOrders.1.1
  have hBookLengthBound :
      oldBook.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hOrders.1.2
  have hQtyBound :
      (oldBook.toNat + (i * 5 + 5) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
    simpa only [show i * 5 + 4 + 1 = i * 5 + 5 by omega] using
      hOrders.orderWord_bound i 4 hi (by omega)
  have hQtyRead :
      st.mem.read64 (UInt32.ofNat
        ((oldBook.toNat + (i * 5 + 5) * 8) % 4294967296)) =
        os[i]!.oqty := by
    have hRead := hOrders.orderWord_eq i 4 hi (by omega)
    simpa only [orderWord, OrderL.word,
      show i * 5 + 4 + 1 = i * 5 + 5 by omega] using hRead
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hOrdersLength64]
    exact hi
  simp only [fullTradeFinishProg, List.cons_append, List.nil_append]
  wp_run_finish (hParams, hLocals, hValues, hRemainingGet, hBookGet,
    hIndexGet)
  rw [if_neg (Nat.not_lt.mpr hBookLengthBound), hBookLengthRead,
    if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_finish (hParams, hLocals, hValues, hRemainingGet, hBookGet,
    hIndexGet)
  rw [if_neg (Nat.not_lt.mpr hQtyBound), hQtyRead]
  simpa only [fullTradeFinishFrame,
    List.getElem!_eq_getElem?_getD] using hDone

end Project.ClobLimit.InternalFullTradeFinish
