import Project.ClobLimit.RunMatchAllocations
import Project.ClobLimit.InternalCorrect

/-!
# `runMatch` internal call

The generated call site reads eleven values from the prepared function 18
frame and invokes function 17.  This module states those local facts once and
uses the complete internal matcher theorem without unfolding its body.
-/

namespace Project.ClobLimit.RunMatchCall

open Wasm Project.Clob Project.ClobLimit

set_option maxRecDepth 1048576

structure CallLocalsAt (base : Locals)
    (fuel : UInt64) (taker : OrderL)
    (bookOwner book tradesOwner trades remaining : UInt64) : Prop where
  params : base.params.length = 7
  locals : base.locals.length = 35
  values : base.values = []
  fuel : base.get 7 = some (.i64 fuel)
  oid : base.get 8 = some (.i64 taker.oid)
  trader : base.get 9 = some (.i64 taker.otrader)
  side : base.get 10 = some (.i64 taker.oside)
  price : base.get 11 = some (.i64 taker.oprice)
  qty : base.get 12 = some (.i64 taker.oqty)
  bookOwner : base.get 14 = some (.i64 bookOwner)
  book : base.get 15 = some (.i64 book)
  tradesOwner : base.get 16 = some (.i64 tradesOwner)
  trades : base.get 17 = some (.i64 trades)
  remaining : base.get 18 = some (.i64 remaining)

set_option Elab.async false in
theorem finalFrame_callLocals
    (bookOwner book g0 : UInt64) (taker : OrderL) (os : List OrderL) :
    CallLocalsAt
      (RunMatchAllocations.finalFrame bookOwner book taker os g0)
      (UInt64.ofNat (os.length + 1)) taker bookOwner book
      (g0 + 48) (g0 + 104) taker.oqty := by
  have hRoot2 : g0 + 56 + 48 = g0 + 104 := by
    rw [UInt64.add_assoc]
    rw [show (56 : UInt64) + 48 = 104 by decide]
  unfold RunMatchAllocations.finalFrame
    RunMatchAllocations.secondResultFrame RunMatchAllocations.firstFrame
    RunMatchAllocations.firstResultFrame RunMatchEmptyAlloc.allocFrame
    RunMatchPrepare.prepareFrame RunMatchPrepare.prepareLocals
    RunMatchPrepare.entryFrame
  dsimp
  constructor <;> try rfl
  change some (Value.i64 (g0 + 56 + 48)) =
    some (Value.i64 (g0 + 104))
  rw [hRoot2]

set_option Elab.async false in
theorem callProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel : UInt64) (taker : OrderL)
    (bookOwner book tradesOwner trades remaining : UInt64)
    (hLocals : CallLocalsAt base fuel taker bookOwner book
      tradesOwner trades remaining)
    (P : Store Unit → List Value → Prop)
    (hCall : TerminatesWith (m := «module») (id := 17)
      (initial := st) (env := env)
      (InternalEarlyExit.internalArgs fuel taker bookOwner book
        tradesOwner trades remaining) P)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (st' : Store Unit) (values : List Value), P st' values →
      wp «module» rest Q st' { base with values := values } env) :
    wp «module» (RunMatchEntry.callProg ++ rest) Q st base env := by
  rcases hLocals with ⟨hParams, hLocalLength, hValues, hFuel, hOid,
    hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTradesOwner, hTrades,
    hRemaining⟩
  simp only [Locals.get] at hFuel hOid hTrader hSide hPrice hQty hBookOwner hBook hTradesOwner hTrades hRemaining
  have hFuel' : base.locals[0] = .i64 fuel := by
    simpa [hParams, hLocalLength] using hFuel
  have hOid' : base.locals[1] = .i64 taker.oid := by
    simpa [hParams, hLocalLength] using hOid
  have hTrader' : base.locals[2] = .i64 taker.otrader := by
    simpa [hParams, hLocalLength] using hTrader
  have hSide' : base.locals[3] = .i64 taker.oside := by
    simpa [hParams, hLocalLength] using hSide
  have hPrice' : base.locals[4] = .i64 taker.oprice := by
    simpa [hParams, hLocalLength] using hPrice
  have hQty' : base.locals[5] = .i64 taker.oqty := by
    simpa [hParams, hLocalLength] using hQty
  have hBookOwner' : base.locals[7] = .i64 bookOwner := by
    simpa [hParams, hLocalLength] using hBookOwner
  have hBook' : base.locals[8] = .i64 book := by
    simpa [hParams, hLocalLength] using hBook
  have hTradesOwner' : base.locals[9] = .i64 tradesOwner := by
    simpa [hParams, hLocalLength] using hTradesOwner
  have hTrades' : base.locals[10] = .i64 trades := by
    simpa [hParams, hLocalLength] using hTrades
  have hRemaining' : base.locals[11] = .i64 remaining := by
    simpa [hParams, hLocalLength] using hRemaining
  simp only [RunMatchEntry.callProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocalLength,
    hValues, hFuel', hOid', hTrader', hSide', hPrice', hQty', hBookOwner',
    hBook', hTradesOwner', hTrades', hRemaining']
  refine wp_call_tw hCall ?_
  intro st' values hPost
  exact hNext st' values hPost

end Project.ClobLimit.RunMatchCall
