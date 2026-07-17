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
    (hLocals : base.locals.length = 76)
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
  .localGet 9,
  .localSet 34,
  .localGet 10,
  .localSet 35,
  .localGet 11,
  .localSet 36,
  .localGet 12,
  .localSet 37,
  .localGet 13,
  .localSet 38,
  .localGet 15,
  .localSet 39,
  .localGet 33,
  .localSet 40,
  .localGet 40,
  .localGet 39,
  .localSet 66,
  .localGet 66,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 39,
    .localSet 66,
    .localGet 40,
    .localSet 67,
    .localGet 66,
    .wrapI64,
    .load64 0,
    .localSet 68,
    .localGet 67,
    .localGet 68,
    .ltUI64,
    .iff 0 1 ([
      .localGet 68,
      .constI64 1,
      .subI64,
      .localSet 71,
      .localGet 67,
      .constI64 5,
      .mulI64,
      .localSet 69,
      .localGet 71,
      .localGet 67,
      .subI64,
      .constI64 5,
      .mulI64,
      .localSet 70
    ] ++ FullBookUpdate.fullBookUpdateProg) [
      .localGet 66
    ]
  ] [
    .unreachable
  ]
  ] ++ FullTradeUpdate.fullTradeUpdateProg ++
    FullReleaseTransition.fullReleaseTransitionProg

def fullPrepareLocals (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 25 (.i64 taker.oid)
  let locals := locals.set 26 (.i64 taker.otrader)
  let locals := locals.set 27 (.i64 taker.oside)
  let locals := locals.set 28 (.i64 taker.oprice)
  let locals := locals.set 29 (.i64 taker.oqty)
  let locals := locals.set 30 (.i64 book)
  let locals := locals.set 31 (.i64 (UInt64.ofNat i))
  let locals := locals.set 57 (.i64 book)
  let locals := locals.set 58 (.i64 (UInt64.ofNat i))
  let locals := locals.set 59 (.i64 (UInt64.ofNat os.length))
  let locals := locals.set 62 (.i64 (UInt64.ofNat (os.length - 1)))
  let locals := locals.set 60 (.i64 (UInt64.ofNat (i * 5)))
  locals.set 61 (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5)))

def fullPrepareFrame (base : Locals) (book : UInt64) (taker : OrderL)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with locals := fullPrepareLocals base book taker os i, values := [] }

set_option Elab.async false in
theorem fullBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book : UInt64) (taker : OrderL) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
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

def searchLocals (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (result : Option Nat) : List Value :=
  let locals := base.locals.set 16 (.i64 bookOwner)
  let locals := locals.set 17 (.i64 book)
  let locals := locals.set 18 (.i64 taker.oid)
  let locals := locals.set 19 (.i64 taker.otrader)
  let locals := locals.set 20 (.i64 taker.oside)
  let locals := locals.set 21 (.i64 taker.oprice)
  let locals := locals.set 22 (.i64 taker.oqty)
  let locals := locals.set 24 (.i64 (optionPayload result))
  locals.set 23 (.i64 (optionTag result))

def searchFrame (base : Locals) (bookOwner book : UInt64) (taker : OrderL)
    (result : Option Nat) : Locals :=
  { base with
    locals := searchLocals base bookOwner book taker result
    values := [] }

def quantityFrame (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (i : Nat) : Locals :=
  { base with
    locals := ((searchLocals base bookOwner book taker (some i)).set 57
      (.i64 book)).set 58 (.i64 (UInt64.ofNat i))
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

def dispatchProg : Wasm.Program :=
  [
  .localGet 18,
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
    .iff 0 0 completeProg [
      .localGet 15,
      .localSet 66,
      .localGet 33,
      .localSet 67,
      .localGet 67,
      .localGet 66,
      .wrapI64,
      .load64 0,
      .ltUI64,
      .iff 0 1 [
        .localGet 66,
        .localGet 67,
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
      .localGet 18,
      .leUI64,
      .iff 0 0 fullBranchProg
        PartialBranch.partialBranchProg
    ]
  ]
  ]

set_option Elab.async false in
theorem dispatchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel bookOwner book trades remaining : UInt64) (taker : OrderL)
    (os : List OrderL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 9 = some (.i64 taker.oid))
    (hTrader : base.get 10 = some (.i64 taker.otrader))
    (hSide : base.get 11 = some (.i64 taker.oside))
    (hPrice : base.get 12 = some (.i64 taker.oprice))
    (hQty : base.get 13 = some (.i64 taker.oqty))
    (hBookOwner : base.get 14 = some (.i64 bookOwner))
    (hBook : base.get 15 = some (.i64 book))
    (hTrades : base.get 17 = some (.i64 trades))
    (hRemaining : base.get 18 = some (.i64 remaining))
    (hLength32 : os.length < 4294967296)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hStop : ∀ s,
      (remaining = 0 ∨ findBestL os taker = none) →
      LoopControl.CompletedResultAt s book trades remaining →
      s.get 0 = some (.i64 fuel) →
      wp «module» rest Q st s env)
    (hFull : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      os[i]!.oqty ≤ remaining →
      wp «module» fullBranchProg
        (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker i) env)
    (hPartial : ∀ i,
      remaining ≠ 0 → findBestL os taker = some i →
      ¬os[i]!.oqty ≤ remaining →
      wp «module» PartialBranch.partialBranchProg
        (dispatchBranchPost env rest Q) st
        (quantityFrame base bookOwner book taker i) env) :
    wp «module» (dispatchProg ++ rest) Q st base env := by
  simp only [Locals.get] at hOid hTrader hSide hPrice hQty hBookOwner hBook hTrades hRemaining
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
      hParams, hLocals, hValues, hBook', hTrades', hRemaining']
    apply hStop
    · exact Or.inl rfl
    · simp [LoopControl.CompletedResultAt, hParams, hLocals]
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
          hParams, hLocals, hBook', hTrades', hRemaining']
        apply hStop
        · exact Or.inr hFind
        · simp [LoopControl.CompletedResultAt, hParams, hLocals]
        · simpa [completeFrame] using hFuel
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
        simp [optionVals, hFind, optionTag, optionPayload] at hvs
        subst vs
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
          intro c hc
          unfold dispatchBranchPost zeroIffPost at hc
          cases c <;> simp_all [wp_simp]
          case Break k _ _ =>
            cases k <;> simp_all [wp_simp]
            case succ k =>
              cases k <;> simp_all [wp_simp]
              case succ k => cases k <;> simp_all [wp_simp]
        · rw [if_neg hMakerQty]
          refine wp.imp (hPartial i hRemainingZero hFind hMakerQty) ?_
          intro c hc
          unfold dispatchBranchPost zeroIffPost at hc
          cases c <;> simp_all [wp_simp]
          case Break k _ _ =>
            cases k <;> simp_all [wp_simp]
            case succ k =>
              cases k <;> simp_all [wp_simp]
              case succ k => cases k <;> simp_all [wp_simp]

end Project.ClobMatchFuel.Iteration
