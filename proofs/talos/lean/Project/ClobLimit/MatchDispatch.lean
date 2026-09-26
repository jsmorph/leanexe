import Project.ClobMatchFuel.IterationQuantity

namespace Project.ClobLimit.MatchDispatch

open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobMatchFuel Project.ClobMatchFuel.Iteration

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def completeProg : Wasm.Program :=
  [.localGet 14, .localSet 73, .localGet 15, .localSet 21,
    .localGet 16, .localSet 75, .localGet 17, .localSet 22,
    .localGet 18, .localSet 23, .constI64 1, .localSet 24]

def completeFrame (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Locals :=
  { base with
    locals := (((((base.locals.set 64 (.i64 bookOwner)).set 12 (.i64 book)).set 66
      (.i64 tradesOwner)).set 13 (.i64 trades)).set 14 (.i64 remaining)).set 15 (.i64 1)
    values := [] }

def CompletedAt (frame : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Prop :=
  frame.get 73 = some (.i64 bookOwner) ∧ frame.get 21 = some (.i64 book) ∧
  frame.get 75 = some (.i64 tradesOwner) ∧ frame.get 22 = some (.i64 trades) ∧
  frame.get 23 = some (.i64 remaining) ∧ frame.get 24 = some (.i64 1) ∧
  frame.params.length = 9 ∧ frame.locals.length = 86 ∧ frame.values = []

def dispatchProg : Wasm.Program :=
  [
  .localGet 18,
  .constI64 0,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ] [] [.i64],
  .constI64 1,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ] [] [.i64],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 completeProg [
    .localGet 14,
    .localSet 25,
    .localGet 15,
    .localSet 26,
    .localGet 9,
    .localSet 27,
    .localGet 10,
    .localSet 28,
    .localGet 11,
    .localSet 29,
    .localGet 12,
    .localSet 30,
    .localGet 13,
    .localSet 31,
    .localGet 25,
    .localGet 26,
    .localGet 27,
    .localGet 28,
    .localGet 29,
    .localGet 30,
    .localGet 31,
    .call 9,
    .localSet 33,
    .localSet 32,
    .localGet 32,
    .constI64 0,
    .eqI64,
    .iff 0 0 completeProg (SelectedOrder.loadProg ++ quantityProg)
  ]
  ]

set_option Elab.async false in
theorem dispatchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel bookOwner book tradesOwner trades remaining : UInt64) (taker : OrderL)
    (os : List OrderL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 9 = some (.i64 taker.oid))
    (hTrader : base.get 10 = some (.i64 taker.otrader))
    (hSide : base.get 11 = some (.i64 taker.oside))
    (hPrice : base.get 12 = some (.i64 taker.oprice))
    (hQty : base.get 13 = some (.i64 taker.oqty))
    (hBookOwner : base.get 14 = some (.i64 bookOwner))
    (hBook : base.get 15 = some (.i64 book))
    (hTradesOwner : base.get 16 = some (.i64 tradesOwner))
    (hTrades : base.get 17 = some (.i64 trades))
    (hRemaining : base.get 18 = some (.i64 remaining))
    (hLength32 : os.length < 4294967296)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hStop : ∀ s,
      (remaining = 0 ∨ findBestL os taker = none) →
      CompletedAt s bookOwner book tradesOwner trades remaining →
      s.get 0 = some (.i64 fuel) →
      wp Project.ClobMatchFuel.«module» rest Q st s env)
    (hFull : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      os[i]!.oqty ≤ remaining →
      wp Project.ClobMatchFuel.«module» fullBranchProg
        (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker os i) env)
    (hPartial : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      ¬os[i]!.oqty ≤ remaining →
      wp Project.ClobMatchFuel.«module» PartialBranch.partialBranchProg
        (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker os i) env) :
    wp Project.ClobMatchFuel.«module» (dispatchProg ++ rest) Q st base env := by
  simp only [Locals.get] at hOid hTrader hSide hPrice hQty hBookOwner hBook hTradesOwner hTrades hRemaining
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
  have hBookOwner' : base.locals[5] = .i64 bookOwner := by
    simpa [hParams, hLocals] using hBookOwner
  have hBook' : base.locals[6] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hTradesOwner' : base.locals[7] = .i64 tradesOwner := by
    simpa [hParams, hLocals] using hTradesOwner
  have hTrades' : base.locals[8] = .i64 trades := by
    simpa [hParams, hLocals] using hTrades
  have hRemaining' : base.locals[9] = .i64 remaining := by
    simpa [hParams, hLocals] using hRemaining
  simp only [dispatchProg, List.cons_append, List.nil_append]
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
    simp (config := { maxSteps := 10000000 }) [completeProg, wp_simp,
      hParams, hLocals, hValues, hBookOwner', hBook', hTradesOwner', hTrades', hRemaining']
    apply hStop
    · exact Or.inl rfl
    · simp [CompletedAt, Locals.get, hParams, hLocals]
    · simpa [completeFrame] using hFuel
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
      (FindBestWrapper.func9_spec_owner env st bookOwner book os taker
        hLength32 hOrders) ?_
    intro st1 vs hResult
    rcases hResult with ⟨hvs, hst⟩
    subst st1
    cases hFind : findBestL os taker with
    | none =>
        simp [optionVals, hFind, optionTag, optionPayload] at hvs
        subst vs
        wp_run
        simp [hParams, hLocals]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        norm_num
        simp (config := { maxSteps := 10000000 }) [completeProg, wp_simp,
          hParams, hLocals, hBookOwner', hBook', hTradesOwner', hTrades', hRemaining']
        apply hStop
        · exact Or.inr hFind
        · simp [CompletedAt, Locals.get, hParams, hLocals]
        · simpa [completeFrame] using hFuel
    | some i =>
        have hi : i < os.length := findBestL_some_lt os taker i hFind
        have hLength64 : os.length < UInt64.size := by
          rw [size_eq]
          omega
        simp [optionVals, hFind, optionTag, optionPayload] at hvs
        subst vs
        wp_run
        simp [hParams, hLocals]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        norm_num
        apply SelectedOrder.loadProg_spec env st _ book os i
        · simpa [searchFrame] using hParams
        · simpa [searchFrame, searchLocals, List.length_set] using hLocals
        · rfl
        · simp [searchFrame, searchLocals, Locals.get, hParams, hLocals, hBook']
        · simp [searchFrame, searchLocals, Locals.get, hParams, hLocals, optionPayload]
        · exact hi
        · exact hLength64
        · exact hOrders
        change wp Project.ClobMatchFuel.«module» (quantityProg ++ []) _ st
          (quantityFrame base bookOwner book taker os i) env
        apply quantityProg_spec env st _ os[i]!.oqty remaining
        · simpa [quantityFrame, SelectedOrder.loadFrame, searchFrame] using hParams
        · simpa [quantityFrame, SelectedOrder.loadFrame, SelectedOrder.loadLocals,
            searchFrame, searchLocals] using hLocals
        · rfl
        · simp [quantityFrame, SelectedOrder.loadFrame, SelectedOrder.loadLocals,
            searchFrame, searchLocals, Locals.get, hParams, hLocals]
        · simp [quantityFrame, SelectedOrder.loadFrame, SelectedOrder.loadLocals,
            searchFrame, searchLocals, Locals.get, hParams, hLocals, hRemaining']
        · intro hMakerQty
          refine wp.imp (hFull i hRemainingZero hFind hMakerQty) ?_
          intro c hc
          unfold dispatchBranchPost zeroIffPost at hc
          unfold zeroIffPost
          cases c <;> try simpa [wp_simp] using hc
          case Break k _ _ =>
            cases k <;> try simpa [wp_simp] using hc
            case succ k =>
              cases k <;> try simpa [wp_simp] using hc
              case succ k => cases k <;> simpa [wp_simp] using hc
        · intro hMakerQty
          refine wp.imp (hPartial i hRemainingZero hFind hMakerQty) ?_
          intro c hc
          unfold dispatchBranchPost zeroIffPost at hc
          unfold zeroIffPost
          cases c <;> try simpa [wp_simp] using hc
          case Break k _ _ =>
            cases k <;> try simpa [wp_simp] using hc
            case succ k =>
              cases k <;> try simpa [wp_simp] using hc
              case succ k => cases k <;> simpa [wp_simp] using hc

end Project.ClobLimit.MatchDispatch
