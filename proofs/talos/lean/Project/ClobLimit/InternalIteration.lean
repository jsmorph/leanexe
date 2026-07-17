import Project.ClobLimit.FindBestWrapper
import Interpreter.Wasm.Wp.Tactic

/-!
# Internal matcher iteration control

The generated internal matcher checks the remaining quantity, invokes its
owner-aware search, reads the selected maker quantity, and chooses a full or
partial update.  This module stops before either allocation-bearing branch.
Its frames retain both owner-and-pointer pairs returned by function 17.
-/

namespace Project.ClobLimit.InternalIteration

open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobLimit Project.ClobLimit.FindBestWrapper

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def completeProg : Wasm.Program :=
  [
  .localGet 6,
  .localSet 11,
  .localGet 7,
  .localSet 12,
  .localGet 8,
  .localSet 13,
  .localGet 9,
  .localSet 14,
  .localGet 10,
  .localSet 15,
  .constI64 1,
  .localSet 16
  ]

def completeLocals (base : Locals) (bookOwner book tradesOwner trades
    remaining : UInt64) : List Value :=
  let locals := base.locals.set 0 (.i64 bookOwner)
  let locals := locals.set 1 (.i64 book)
  let locals := locals.set 2 (.i64 tradesOwner)
  let locals := locals.set 3 (.i64 trades)
  let locals := locals.set 4 (.i64 remaining)
  locals.set 5 (.i64 1)

def completeFrame (base : Locals) (bookOwner book tradesOwner trades
    remaining : UInt64) : Locals :=
  { base with
    locals := completeLocals base bookOwner book tradesOwner trades remaining
    values := [] }

def CompletedResultAt (base : Locals) (bookOwner book tradesOwner trades
    remaining : UInt64) : Prop :=
  base.locals[0]? = some (.i64 bookOwner) ∧
  base.locals[1]? = some (.i64 book) ∧
  base.locals[2]? = some (.i64 tradesOwner) ∧
  base.locals[3]? = some (.i64 trades) ∧
  base.locals[4]? = some (.i64 remaining) ∧
  base.locals[5]? = some (.i64 1) ∧
  base.params.length = 11 ∧ base.locals.length = 64 ∧ base.values = []

def AllocScratchAt (s : Locals) : Prop :=
  ∃ bookCapacity bookNext tradeNext partialNext : UInt64,
    s.locals[58]? = some (.i64 bookCapacity) ∧
    s.locals[59]? = some (.i64 bookNext) ∧
    s.locals[61]? = some (.i64 tradeNext) ∧
    s.locals[62]? = some (.i64 partialNext)

def searchLocals (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (result : Option Nat) : List Value :=
  let locals := base.locals.set 6 (.i64 bookOwner)
  let locals := locals.set 7 (.i64 book)
  let locals := locals.set 8 (.i64 taker.oid)
  let locals := locals.set 9 (.i64 taker.otrader)
  let locals := locals.set 10 (.i64 taker.oside)
  let locals := locals.set 11 (.i64 taker.oprice)
  let locals := locals.set 12 (.i64 taker.oqty)
  let locals := locals.set 14 (.i64 (optionPayload result))
  locals.set 13 (.i64 (optionTag result))

def searchFrame (base : Locals) (bookOwner book : UInt64) (taker : OrderL)
    (result : Option Nat) : Locals :=
  { base with
    locals := searchLocals base bookOwner book taker result
    values := [] }

def quantityFrame (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (i : Nat) : Locals :=
  { base with
    locals := ((searchLocals base bookOwner book taker (some i)).set 45
      (.i64 book)).set 46 (.i64 (UInt64.ofNat i))
    values := [] }

def zeroIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp «module» rest Q st' { s' with values := [] } env
    | .Break 0 st' s' =>
        wp «module» rest Q st' { s' with values := [] } env
    | .Break (k + 1) st' s' => Q (.Break k st' s')
    | other => Q other

def dispatchBranchPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  zeroIffPost env [] (zeroIffPost env [] (zeroIffPost env rest Q))

def dispatchProg (fullBranch partialBranch : Wasm.Program) : Wasm.Program :=
  [
  .localGet 10,
  .constI64 0,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 1,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 completeProg [
    .localGet 6,
    .localSet 17,
    .localGet 7,
    .localSet 18,
    .localGet 1,
    .localSet 19,
    .localGet 2,
    .localSet 20,
    .localGet 3,
    .localSet 21,
    .localGet 4,
    .localSet 22,
    .localGet 5,
    .localSet 23,
    .localGet 17,
    .localGet 18,
    .localGet 19,
    .localGet 20,
    .localGet 21,
    .localGet 22,
    .localGet 23,
    .call 14,
    .localSet 25,
    .localSet 24,
    .localGet 24,
    .constI64 0,
    .eqI64,
    .iff 0 0 completeProg [
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
      .localGet 10,
      .leUI64,
      .iff 0 0 fullBranch partialBranch
    ]
  ]
  ]

set_option Elab.async false in
theorem dispatchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel bookOwner book tradesOwner trades remaining : UInt64)
    (taker : OrderL) (os : List OrderL)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 1 = some (.i64 taker.oid))
    (hTrader : base.get 2 = some (.i64 taker.otrader))
    (hSide : base.get 3 = some (.i64 taker.oside))
    (hPrice : base.get 4 = some (.i64 taker.oprice))
    (hQty : base.get 5 = some (.i64 taker.oqty))
    (hBookOwner : base.get 6 = some (.i64 bookOwner))
    (hBook : base.get 7 = some (.i64 book))
    (hTradesOwner : base.get 8 = some (.i64 tradesOwner))
    (hTrades : base.get 9 = some (.i64 trades))
    (hRemaining : base.get 10 = some (.i64 remaining))
    (hLength32 : os.length < 4294967296)
    (hOrders : OrdersAt st book os)
    (fullBranch partialBranch : Wasm.Program)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hStop : ∀ s,
      (remaining = 0 ∨ findBestL os taker = none) →
      CompletedResultAt s bookOwner book tradesOwner trades remaining →
      s.get 0 = some (.i64 fuel) →
      wp «module» rest Q st s env)
    (hFull : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      os[i]!.oqty ≤ remaining →
      wp «module» fullBranch (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker i) env)
    (hPartial : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      ¬os[i]!.oqty ≤ remaining →
      wp «module» partialBranch (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker i) env) :
    wp «module» (dispatchProg fullBranch partialBranch ++ rest) Q st base env := by
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
  have hTradesOwner' : base.params[8] = .i64 tradesOwner := by
    simpa [Locals.get, hParams, hLocals] using hTradesOwner
  have hTrades' : base.params[9] = .i64 trades := by
    simpa [Locals.get, hParams, hLocals] using hTrades
  have hRemaining' : base.params[10] = .i64 remaining := by
    simpa [Locals.get, hParams, hLocals] using hRemaining
  simp only [Locals.get] at hRemaining
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
      hParams, hLocals, hValues, hBookOwner', hBook', hTradesOwner', hTrades',
      hRemaining']
    apply hStop
    · exact Or.inl rfl
    · simp [CompletedResultAt, hParams, hLocals]
    · simpa [completeFrame, completeLocals, Locals.get, hParams, hLocals]
        using hFuel
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
        simp (config := { maxSteps := 10000000 }) [completeProg, wp_simp,
          hParams, hLocals, hBookOwner', hBook', hTradesOwner', hTrades',
          hRemaining']
        apply hStop
        · exact Or.inr hFind
        · simp [CompletedResultAt, hParams, hLocals]
        · simpa [completeFrame, completeLocals, searchFrame, searchLocals,
            Locals.get, hParams, hLocals] using hFuel
    | some i =>
        have hi : i < os.length := findBestL_some_lt os taker i hFind
        have hLength64 : os.length < UInt64.size := by
          rw [size_eq]
          omega
        have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
          rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
            toNat_ofNat_lt hLength64]
          exact hi
        have hMakerBound :
            (book.toNat + (i * 5 + 4 + 1) * 8) % 4294967296 + 8 ≤
              st.mem.pages * 65536 :=
          hOrders.orderWord_bound i 4 hi (by omega)
        have hMakerRead : st.mem.read64 (UInt32.ofNat
            ((book.toNat + (i * 5 + 4 + 1) * 8) % 4294967296)) =
            os[i]!.oqty := by
          simpa [orderWord, OrderL.word] using
            hOrders.orderWord_eq i 4 hi (by omega)
        simp [optionVals, hFind, optionTag, optionPayload] at hResultValues
        subst values
        wp_run
        simp [hParams, hLocals]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        norm_num
        simp (config := { maxSteps := 10000000 }) [wp_simp, hParams,
          hLocals, hBook']
        rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1,
          if_pos hIndexLt]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        simp (config := { maxSteps := 10000000 }) [wp_simp, hParams,
          hLocals]
        rw [if_neg (Nat.not_lt.mpr hMakerBound), hMakerRead]
        rw [hRemaining']
        wp_run
        refine wp_iff_cons rfl ?_
        by_cases hMakerQty : os[i]!.oqty ≤ remaining
        · rw [if_pos hMakerQty]
          refine wp.imp (hFull i hRemainingZero hFind hMakerQty) ?_
          intro cont hCont
          unfold dispatchBranchPost zeroIffPost at hCont
          cases cont <;> simp_all [wp_simp]
          case Break k _ _ =>
            cases k <;> simp_all [wp_simp]
            case succ k =>
              cases k <;> simp_all [wp_simp]
              case succ k => cases k <;> simp_all [wp_simp]
        · rw [if_neg hMakerQty]
          refine wp.imp (hPartial i hRemainingZero hFind hMakerQty) ?_
          intro cont hCont
          unfold dispatchBranchPost zeroIffPost at hCont
          cases cont <;> simp_all [wp_simp]
          case Break k _ _ =>
            cases k <;> simp_all [wp_simp]
            case succ k =>
              cases k <;> simp_all [wp_simp]
              case succ k => cases k <;> simp_all [wp_simp]

end Project.ClobLimit.InternalIteration
