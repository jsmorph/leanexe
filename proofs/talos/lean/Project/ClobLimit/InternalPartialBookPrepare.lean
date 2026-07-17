import Project.ClobLimit.Program
import Project.Clob
import Interpreter.Wasm.Wp.Tactic

/-!
# Partial-fill book preparation

The partial-fill branch reads the selected maker before allocating a
replacement book.  It computes the reduced maker quantity and prepares the
book allocator's source, length, and copy locals.  This module proves that
instruction bridge against the represented source book.
-/

namespace Project.ClobLimit.InternalPartialBookPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_prepare" "(" hParams:term "," hLocals:term ","
    hValues:term "," hBook:term "," hIndex:term ","
    hRemaining:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hBook), ($hIndex), ($hRemaining)])

def partialBookPrefixProg : Wasm.Program :=
  [
  .localGet 7,
  .localSet 51,
  .localGet 25,
  .localSet 52,
  .localGet 51,
  .localSet 56,
  .localGet 52,
  .localSet 57,
  .localGet 7,
  .localSet 69,
  .localGet 25,
  .localSet 70,
  .localGet 70,
  .localGet 69,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 69,
    .localGet 70,
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
  .localSet 62,
  .localGet 7,
  .localSet 69,
  .localGet 25,
  .localSet 70,
  .localGet 70,
  .localGet 69,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 69,
    .localGet 70,
    .constI64 5,
    .mulI64,
    .constI64 2,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 63,
  .localGet 7,
  .localSet 69,
  .localGet 25,
  .localSet 70,
  .localGet 70,
  .localGet 69,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 69,
    .localGet 70,
    .constI64 5,
    .mulI64,
    .constI64 3,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 64,
  .localGet 7,
  .localSet 69,
  .localGet 25,
  .localSet 70,
  .localGet 70,
  .localGet 69,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 69,
    .localGet 70,
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
  .localSet 65,
  .localGet 7,
  .localSet 69,
  .localGet 25,
  .localSet 70,
  .localGet 70,
  .localGet 69,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 69,
    .localGet 70,
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
  .localGet 10,
  .subI64,
  .localSet 66,
  .localGet 56,
  .wrapI64,
  .load64 0,
  .localSet 58,
  .localGet 57,
  .localGet 58,
  .ltUI64
  ]

def partialBookPrepareLocals (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 40 (.i64 book)
  let locals := locals.set 41 (.i64 (UInt64.ofNat i))
  let locals := locals.set 45 (.i64 book)
  let locals := locals.set 46 (.i64 (UInt64.ofNat i))
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 51 (.i64 os[i]!.oid)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 52 (.i64 os[i]!.otrader)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 53 (.i64 os[i]!.oside)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 54 (.i64 os[i]!.oprice)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 55 (.i64 (os[i]!.oqty - remaining))
  let locals := locals.set 47 (.i64 (UInt64.ofNat os.length))
  locals.set 48 (.i64 (UInt64.ofNat os.length * 5))

def partialBookPrepareFrame (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with
    locals := partialBookPrepareLocals base book remaining os i
    values := [] }

def partialBookGuardLocals (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 40 (.i64 book)
  let locals := locals.set 41 (.i64 (UInt64.ofNat i))
  let locals := locals.set 45 (.i64 book)
  let locals := locals.set 46 (.i64 (UInt64.ofNat i))
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 51 (.i64 os[i]!.oid)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 52 (.i64 os[i]!.otrader)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 53 (.i64 os[i]!.oside)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 54 (.i64 os[i]!.oprice)
  let locals := locals.set 58 (.i64 book)
  let locals := locals.set 59 (.i64 (UInt64.ofNat i))
  let locals := locals.set 55 (.i64 (os[i]!.oqty - remaining))
  locals.set 47 (.i64 (UInt64.ofNat os.length))

def partialBookGuardFrame (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with
    locals := partialBookGuardLocals base book remaining os i
    values := [.i32 1] }

set_option Elab.async false in
theorem partialBookPrefixProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hBookLocal : base.params[7]? = some (.i64 book))
    (hIndexLocal : base.locals[14]? = some (.i64 (UInt64.ofNat i)))
    (hRemainingLocal : base.params[10]? = some (.i64 remaining))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (partialBookGuardFrame base book remaining os i) env) :
    wp «module» (partialBookPrefixProg ++ rest) Q st base env := by
  have hBookGet : base.params[7] = .i64 book := by
    apply Option.some.inj
    calc
      some base.params[7] = base.params[7]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 book) := hBookLocal
  have hIndexGet : base.locals[14] = .i64 (UInt64.ofNat i) := by
    apply Option.some.inj
    calc
      some base.locals[14] = base.locals[14]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat i)) := hIndexLocal
  have hRemainingGet : base.params[10] = .i64 remaining := by
    apply Option.some.inj
    calc
      some base.params[10] = base.params[10]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 remaining) := hRemainingLocal
  have hLengthRead :
      st.mem.read64 (UInt32.ofNat (book.toNat % 4294967296)) =
        UInt64.ofNat os.length := hOrders.1.1
  have hLengthBound :
      book.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hOrders.1.2
  have hFieldBound (field : Nat) (hfield : field < 5) :
      (book.toNat + (i * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 :=
    hOrders.orderWord_bound i field hi hfield
  have hFieldRead (field : Nat) (hfield : field < 5) :
      st.mem.read64 (UInt32.ofNat
        ((book.toNat + (i * 5 + field + 1) * 8) % 4294967296)) =
        os[i]!.word field := by
    simpa only [orderWord] using hOrders.orderWord_eq i field hi hfield
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hOrdersLength64]
    exact hi
  simp only [partialBookPrefixProg, List.cons_append, List.nil_append]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 0 (by omega))),
    hFieldRead 0 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 1 (by omega))),
    hFieldRead 1 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 2 (by omega))),
    hFieldRead 2 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 3 (by omega))),
    hFieldRead 3 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 4 (by omega))),
    hFieldRead 4 (by omega)]
  simp only [OrderL.word]
  wp_run_prepare (hParams, hLocals, hValues, hBookGet, hIndexGet,
    hRemainingGet)
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  simpa only [partialBookGuardFrame, partialBookGuardLocals,
    List.getElem!_eq_getElem?_getD] using hDone

end Project.ClobLimit.InternalPartialBookPrepare
