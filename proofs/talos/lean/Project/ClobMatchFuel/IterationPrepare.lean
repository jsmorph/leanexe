import Project.ClobMatchFuel.FullStep
import Project.ClobMatchFuel.BranchPost
import Project.ClobMatchFuel.FindBestWrapper
import Project.ClobMatchFuel.LoopControl
import Project.ClobMatchFuel.PartialBranch

/-!
# Match-loop iteration control

The generated loop records a completed result on an early exit.  A selected
full fill prepares array lengths and copy ranges before entering the allocator.
These small instruction slices provide exact frames for the branch dispatcher.
-/

namespace Project.ClobMatchFuel.Iteration

open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def completeProg : Wasm.Program :=
  [
  .localGet 15,
  .localSet 21,
  .localGet 17,
  .localSet 22,
  .localGet 18,
  .localSet 23,
  .constI64 1,
  .localSet 24
  ]

def completeLocals (base : Locals) (book trades remaining : UInt64) :
    List Value :=
  let locals := base.locals.set 12 (.i64 book)
  let locals := locals.set 13 (.i64 trades)
  let locals := locals.set 14 (.i64 remaining)
  locals.set 15 (.i64 1)

def completeFrame (base : Locals) (book trades remaining : UInt64) : Locals :=
  { base with
    locals := completeLocals base book trades remaining
    values := [] }

set_option Elab.async false in
theorem completeProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades remaining : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hBook : base.get 15 = some (.i64 book))
    (hTrades : base.get 17 = some (.i64 trades))
    (hRemaining : base.get 18 = some (.i64 remaining))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (completeFrame base book trades remaining) env) :
    wp «module» (completeProg ++ rest) Q st base env := by
  simp only [Locals.get] at hBook hTrades hRemaining
  have hBook' : base.locals[6] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hTrades' : base.locals[8] = .i64 trades := by
    simpa [hParams, hLocals] using hTrades
  have hRemaining' : base.locals[9] = .i64 remaining := by
    simpa [hParams, hLocals] using hRemaining
  simp only [completeProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hBook', hTrades', hRemaining']
  simpa [completeFrame, completeLocals] using hDone

def fullBranchProg : Wasm.Program :=
  [
  .localGet 15,
  .localSet 39,
  .localGet 33,
  .localSet 40,
  .localGet 40,
  .localGet 39,
  .localSet 76,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 39,
    .localSet 76,
    .localGet 40,
    .localSet 77,
    .localGet 76,
    .wrapI64,
    .load64 0,
    .localSet 78,
    .localGet 77,
    .localGet 78,
    .ltUI64,
    .iff 0 1 ([
      .localGet 78,
      .constI64 1,
      .subI64,
      .localSet 81,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .localSet 79,
      .localGet 81,
      .localGet 77,
      .subI64,
      .constI64 5,
      .mulI64,
      .localSet 80
    ] ++ FullBookUpdate.fullBookUpdateProg) [
      .localGet 76
    ] [] [.i64]
  ] [
    .unreachable
  ] [] [.i64]
  ] ++ FullTradeUpdate.fullTradeUpdateProg ++
    FullReleaseTransition.fullReleaseTransitionProg

def fullPrepareLocals (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 30 (.i64 book)
  let locals := locals.set 31 (.i64 (UInt64.ofNat i))
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 69 (.i64 (UInt64.ofNat os.length))
  let locals := locals.set 72 (.i64 (UInt64.ofNat (os.length - 1)))
  let locals := locals.set 70 (.i64 (UInt64.ofNat (i * 5)))
  locals.set 71 (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5)))

def fullPrepareFrame (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with locals := fullPrepareLocals base book taker os i, values := [] }

set_option Elab.async false in
theorem fullBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book : UInt64) (taker : OrderL) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hOid : base.get 9 = some (.i64 taker.oid))
    (hTrader : base.get 10 = some (.i64 taker.otrader))
    (hSide : base.get 11 = some (.i64 taker.oside))
    (hPrice : base.get 12 = some (.i64 taker.oprice))
    (hQty : base.get 13 = some (.i64 taker.oqty))
    (hBook : base.get 15 = some (.i64 book))
    (hIndex : base.get 33 = some (.i64 (UInt64.ofNat i)))
    (hi : i < os.length)
    (hLength64 : os.length < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» FullBookUpdate.fullBookUpdateProg
      (BranchPost.doubleResultIffPost env
        (FullTradeUpdate.fullTradeUpdateProg ++
          FullReleaseTransition.fullReleaseTransitionProg ++ rest) Q)
      st (fullPrepareFrame base book taker os i) env) :
    wp «module» (fullBranchProg ++ rest) Q st base env := by
  simp only [Locals.get] at hOid hTrader hSide hPrice hQty hBook hIndex
  have hOid' : base.locals[0] = .i64 taker.oid := by
    simpa [hParams, hLocals] using hOid
  have hTrader' : base.locals[1] = .i64 taker.otrader := by
    simpa [hParams, hLocals] using hTrader
  have hSide' : base.locals[2] = .i64 taker.oside := by
    simpa [hParams, hLocals] using hSide
  have hPrice' : base.locals[3] = .i64 taker.oprice := by
    simpa [hParams, hLocals] using hPrice
  have hQty' : base.locals[4] = .i64 taker.oqty := by
    simpa [hParams, hLocals] using hQty
  have hBook' : base.locals[6] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hIndex' : base.locals[24] = .i64 (UInt64.ofNat i) := by
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
  simp only [fullBranchProg, List.cons_append, List.nil_append]
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
  unfold BranchPost.doubleResultIffPost at hc
  unfold Project.BranchPost.doubleResultIffPost
    Project.BranchPost.oneResultIffPost at hc
  cases c <;> try exact hc
  case Break k _ _ =>
    cases k with
    | zero => exact hc
    | succ k => cases k <;> exact hc

end Project.ClobMatchFuel.Iteration
