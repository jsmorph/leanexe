import Project.ClobLimit.HeapSelect
import Project.ClobLimit.FindBestWrapper

namespace Project.ClobLimit.HeapDispatch
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
open Project.ClobLimit Project.ClobLimit.HeapProgram Project.ClobLimit.HeapFrames
open Project.ClobLimit.FindBestWrapper
set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def zeroIffPost (env : HostEnv Unit) (rest : Program) (Q : Assertion Unit) : Assertion Unit
  | .Fallthrough st s => wp «module» rest Q st { s with values := [] } env
  | .Break 0 st s => wp «module» rest Q st { s with values := [] } env
  | .Break (k + 1) st s => Q (.Break k st s)
  | other => Q other

def selectedPost (env : HostEnv Unit) (rest : Program) (Q : Assertion Unit) :=
  zeroIffPost env [] (zeroIffPost env rest Q)

set_option Elab.async false in
theorem dispatch_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (bookOwner book trades remaining : UInt64) (tradesOwner : Value)
    (taker : OrderL) (os : List OrderL)
    (hParams : base.params.length = 11) (hLocals : base.locals.length = 78)
    (hValues : base.values = [])
    (hOid : base.get 1 = some (.i64 taker.oid))
    (hTrader : base.get 2 = some (.i64 taker.otrader))
    (hSide : base.get 3 = some (.i64 taker.oside))
    (hPrice : base.get 4 = some (.i64 taker.oprice))
    (hQty : base.get 5 = some (.i64 taker.oqty))
    (hBookOwner : base.get 6 = some (.i64 bookOwner))
    (hBook : base.get 7 = some (.i64 book))
    (hTradesOwner : base.get 8 = some tradesOwner)
    (hTrades : base.get 9 = some (.i64 trades))
    (hRemaining : base.get 10 = some (.i64 remaining))
    (hLength32 : os.length < 4294967296) (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Program)
    (hEarly : remaining = 0 → wp «module» rest Q st
      (completeTarget base (.i64 bookOwner) tradesOwner book trades remaining) env)
    (hNone : findBestL os taker = none → wp «module» rest Q st
      (completeTarget (searchFrame base bookOwner book taker none)
        (.i64 bookOwner) tradesOwner book trades remaining) env)
    (hSelected : ∀ i, remaining ≠ 0 → findBestL os taker = some i →
      wp «module» HeapSelect.program (selectedPost env rest Q) st
        (searchFrame base bookOwner book taker (some i)) env) :
    wp «module» (HeapProgram.dispatchProg ++ rest) Q st base env := by
  have hOid' : base.params[1] = .i64 taker.oid := by
    simpa [Locals.get, hParams, hLocals] using hOid
  have hTrader' : base.params[2] = .i64 taker.otrader := by
    simpa [Locals.get, hParams, hLocals] using hTrader
  have hSide' : base.params[3] = .i64 taker.oside := by
    simpa [Locals.get, hParams, hLocals] using hSide
  have hPrice' : base.params[4] = .i64 taker.oprice := by
    simpa [Locals.get, hParams, hLocals] using hPrice
  have hQty' : base.params[5] = .i64 taker.oqty := by
    simpa [Locals.get, hParams, hLocals] using hQty
  have hBookOwner' : base.params[6] = .i64 bookOwner := by
    simpa [Locals.get, hParams, hLocals] using hBookOwner
  have hBook' : base.params[7] = .i64 book := by
    simpa [Locals.get, hParams, hLocals] using hBook
  have hTradesOwner' : base.params[8] = tradesOwner := by
    simpa [Locals.get, hParams, hLocals] using hTradesOwner
  have hTrades' : base.params[9] = .i64 trades := by
    simpa [Locals.get, hParams, hLocals] using hTrades
  have hRemaining' : base.params[10] = .i64 remaining := by
    simpa [Locals.get, hParams, hLocals] using hRemaining
  simp only [Locals.get] at hRemaining
  simp only [HeapProgram.dispatchProg, HeapProgram.searchProg, List.cons_append, List.nil_append]
  wp_run
  rw [hRemaining]
  wp_run
  refine wp_iff_cons rfl ?_
  by_cases hRemainingZero : remaining = 0
  · subst remaining
    rw [if_pos (by simp)]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    norm_num
    simp (config := { maxSteps := 10000000 }) [stopProg, wp_simp,
      hParams, hLocals, hValues, hBookOwner', hBook', hTradesOwner', hTrades',
      hRemaining']
    simpa [completeTarget] using hEarly rfl
  · rw [if_neg (by simp [hRemainingZero])]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    norm_num
    simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
      hValues, hOid', hTrader', hSide', hPrice', hQty', hBookOwner', hBook']
    refine wp_call_tw
      (func14_spec_owner env st bookOwner book os taker hLength32 hOrders) ?_
    intro st1 values hResult
    rcases hResult with ⟨hResultValues, hState⟩
    subst st1
    cases hFind : findBestL os taker with
    | none =>
        simp [optionVals, hFind, optionTag, optionPayload] at hResultValues
        subst values
        wp_run
        simp [hParams, hLocals]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        norm_num
        simp (config := { maxSteps := 10000000 }) [stopProg, wp_simp,
          hParams, hLocals, hBookOwner', hBook', hTradesOwner', hTrades',
          hRemaining']
        simpa [completeTarget, searchFrame, searchLocals, optionPayload, optionTag] using hNone hFind
    | some i =>
        simp [optionVals, hFind, optionTag, optionPayload] at hResultValues
        subst values
        wp_run
        simp [hParams, hLocals]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        change wp «module» HeapSelect.program _ st
          (searchFrame base bookOwner book taker (some i)) env
        refine wp.imp (hSelected i hRemainingZero hFind) ?_
        intro cont hCont
        unfold selectedPost zeroIffPost at hCont
        cases cont <;> simp_all [wp_simp]
        case Break k _ _ =>
          cases k <;> simp_all [wp_simp]
          case succ k => cases k <;> simp_all [wp_simp]

#print axioms dispatch_spec
end Project.ClobLimit.HeapDispatch
