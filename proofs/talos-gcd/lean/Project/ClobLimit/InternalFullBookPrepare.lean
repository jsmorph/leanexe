import Project.ClobLimit.Program
import Project.BranchPost
import Project.Clob
import Interpreter.Wasm.Wp.Tactic

/-!
# Full-fill book preparation

The full-fill branch copies the taker and selected-book values into its
working locals.  It checks the selected index twice, then computes the erased
length and the two copy ranges.  The allocation and copy body remains an
opaque one-result continuation.
-/

namespace Project.ClobLimit.InternalFullBookPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def fullBookSuccessProg (updateProg : Wasm.Program) : Wasm.Program :=
  [
  .localGet 31,
  .localSet 56,
  .localGet 32,
  .localSet 57,
  .localGet 56,
  .wrapI64,
  .load64 0,
  .localSet 58,
  .localGet 57,
  .localGet 58,
  .ltUI64,
  .iff 0 1 ([
    .localGet 58,
    .constI64 1,
    .subI64,
    .localSet 61,
    .localGet 57,
    .constI64 5,
    .mulI64,
    .localSet 59,
    .localGet 61,
    .localGet 57,
    .subI64,
    .constI64 5,
    .mulI64,
    .localSet 60
  ] ++ updateProg) [
    .localGet 56
  ]
  ]

def fullBookBranchProg (updateProg : Wasm.Program) : Wasm.Program :=
  [
  .localGet 1,
  .localSet 26,
  .localGet 2,
  .localSet 27,
  .localGet 3,
  .localSet 28,
  .localGet 4,
  .localSet 29,
  .localGet 5,
  .localSet 30,
  .localGet 7,
  .localSet 31,
  .localGet 25,
  .localSet 32,
  .localGet 32,
  .localGet 31,
  .localSet 56,
  .localGet 56,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 (fullBookSuccessProg updateProg) [
    .unreachable
  ]
  ]

def fullBookPrepareLocals (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 15 (.i64 taker.oid)
  let locals := locals.set 16 (.i64 taker.otrader)
  let locals := locals.set 17 (.i64 taker.oside)
  let locals := locals.set 18 (.i64 taker.oprice)
  let locals := locals.set 19 (.i64 taker.oqty)
  let locals := locals.set 20 (.i64 book)
  let locals := locals.set 21 (.i64 (UInt64.ofNat i))
  let locals := locals.set 45 (.i64 book)
  let locals := locals.set 46 (.i64 (UInt64.ofNat i))
  let locals := locals.set 47 (.i64 (UInt64.ofNat os.length))
  let locals := locals.set 50 (.i64 (UInt64.ofNat (os.length - 1)))
  let locals := locals.set 48 (.i64 (UInt64.ofNat (i * 5)))
  locals.set 49 (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5)))

def fullBookPrepareFrame (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with
    locals := fullBookPrepareLocals base book taker os i
    values := [] }

set_option Elab.async false in
theorem fullBookBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book : UInt64) (taker : OrderL) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hOid : base.get 1 = some (.i64 taker.oid))
    (hTrader : base.get 2 = some (.i64 taker.otrader))
    (hSide : base.get 3 = some (.i64 taker.oside))
    (hPrice : base.get 4 = some (.i64 taker.oprice))
    (hQty : base.get 5 = some (.i64 taker.oqty))
    (hBook : base.get 7 = some (.i64 book))
    (hIndex : base.get 25 = some (.i64 (UInt64.ofNat i)))
    (hi : i < os.length)
    (hLength64 : os.length < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hOrders : OrdersAt st book os)
    (updateProg : Wasm.Program) (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» updateProg
      (Project.BranchPost.doubleResultIffPost «module» env rest Q) st
      (fullBookPrepareFrame base book taker os i) env) :
    wp «module» (fullBookBranchProg updateProg ++ rest) Q st base env := by
  simp only [Locals.get] at hOid hTrader hSide hPrice hQty hBook hIndex
  have hOid' : base.params[1] = .i64 taker.oid := by
    simpa [hParams, hLocals] using hOid
  have hTrader' : base.params[2] = .i64 taker.otrader := by
    simpa [hParams, hLocals] using hTrader
  have hSide' : base.params[3] = .i64 taker.oside := by
    simpa [hParams, hLocals] using hSide
  have hPrice' : base.params[4] = .i64 taker.oprice := by
    simpa [hParams, hLocals] using hPrice
  have hQty' : base.params[5] = .i64 taker.oqty := by
    simpa [hParams, hLocals] using hQty
  have hBook' : base.params[7] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hIndex' : base.locals[14] = .i64 (UInt64.ofNat i) := by
    simpa [hParams, hLocals] using hIndex
  have hLengthRead :
      st.mem.read64 (UInt32.ofNat (book.toNat % 4294967296)) =
        UInt64.ofNat os.length := hOrders.1.1
  have hLengthBound :
      book.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hOrders.1.2
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hLength64]
    exact hi
  have hiU : (UInt64.ofNat i).toNat = i :=
    toNat_ofNat_lt (by omega)
  have hLengthU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt hLength64
  have hErasedU : (UInt64.ofNat (os.length - 1)).toNat = os.length - 1 :=
    toNat_ofNat_lt (by omega)
  have hLengthSub : UInt64.ofNat os.length - 1 =
      UInt64.ofNat (os.length - 1) := by
    apply UInt64.toNat.inj
    rw [toNat_sub_le _ _ (by simp [hLengthU]; omega), hLengthU, hErasedU]
    rfl
  have hPrefixU : (UInt64.ofNat i * 5).toNat = i * 5 := by
    rw [UInt64.toNat_mul, hiU]
    change i * 5 % UInt64.size = i * 5
    exact Nat.mod_eq_of_lt (by omega)
  have hPrefixEq : UInt64.ofNat i * 5 = UInt64.ofNat (i * 5) := by
    apply UInt64.toNat.inj
    rw [hPrefixU, toNat_ofNat_lt (by omega)]
  have hSuffixBase :
      (UInt64.ofNat os.length - 1 - UInt64.ofNat i).toNat =
        os.length - 1 - i := by
    rw [hLengthSub, toNat_sub_le _ _ (by rw [hErasedU, hiU]; omega),
      hErasedU, hiU]
  have hSuffixU :
      ((UInt64.ofNat os.length - 1 - UInt64.ofNat i) * 5).toNat =
        (os.length - 1 - i) * 5 := by
    rw [UInt64.toNat_mul, hSuffixBase]
    change (os.length - 1 - i) * 5 % UInt64.size =
      (os.length - 1 - i) * 5
    exact Nat.mod_eq_of_lt (by omega)
  have hSuffixEq :
      (UInt64.ofNat os.length - 1 - UInt64.ofNat i) * 5 =
        UInt64.ofNat ((os.length - 1 - i) * 5) := by
    apply UInt64.toNat.inj
    rw [hSuffixU, toNat_ofNat_lt (by omega)]
  have hSuffixErasedEq :
      (UInt64.ofNat (os.length - 1) - UInt64.ofNat i) * 5 =
        UInt64.ofNat ((os.length - 1 - i) * 5) := by
    rw [← hLengthSub]
    exact hSuffixEq
  simp only [fullBookBranchProg, fullBookSuccessProg, List.cons_append,
    List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hOid', hTrader', hSide', hPrice', hQty', hBook', hIndex']
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals]
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals]
  rw [hLengthSub, hPrefixEq, hSuffixErasedEq]
  refine wp.imp hDone ?_
  intro c hc
  unfold Project.BranchPost.doubleResultIffPost at hc
  unfold Project.BranchPost.oneResultIffPost at hc
  cases c <;> try exact hc
  case Break k _ _ =>
    cases k with
    | zero => exact hc
    | succ k => cases k <;> exact hc

end Project.ClobLimit.InternalFullBookPrepare
