import Project.ClobLimit.InternalLoopBounds

/-!
# Internal match-loop source progress

The loop invariant records a residual source computation.  These lemmas advance
that computation for stopped, partial-fill, and full-fill dispatcher outcomes.
They also normalize the allocation counter from appended-trade progress.
-/

namespace Project.ClobLimit.InternalLoopProgress

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant

def fullState (data : RunningData) (taker : OrderL) (i : Nat) :
    Project.ClobMatchFuel.Model.MatchStateL :=
  { book := data.orders.eraseIdx i
    trades := data.tradeValues ++
      [Project.ClobMatchFuel.Model.fillTradeL taker data.orders[i]!
        data.orders[i]!.oqty]
    remaining := data.remaining - data.orders[i]!.oqty }

def partialState (data : RunningData) (taker : OrderL) (i : Nat) :
    Project.ClobMatchFuel.Model.MatchStateL :=
  { book := Project.ClobMatchFuel.Model.setQtyL data.orders i
      (data.orders[i]!.oqty - data.remaining)
    trades := data.tradeValues ++
      [Project.ClobMatchFuel.Model.fillTradeL taker data.orders[i]!
        data.remaining]
    remaining := 0 }

theorem stopped_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0)
    (hStop : data.remaining = 0 ∨ findBestL data.orders ctx.taker = none) :
    ctx.result = data.sourceState := by
  have hFuelPositive : 0 < data.fuel.toNat := by
    by_contra h
    have hZero : data.fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  obtain ⟨fuel, hFuelNat⟩ : ∃ fuel, data.fuel.toNat = fuel + 1 :=
    ⟨data.fuel.toNat - 1, by omega⟩
  have hSource := facts.source
  rcases hStop with hRemaining | hFind
  · rw [hFuelNat] at hSource
    rw [Project.ClobMatchFuel.Model.matchFuelL_succ_zero fuel ctx.taker
      data.sourceState hRemaining] at hSource
    exact hSource
  · by_cases hRemaining : data.remaining = 0
    · rw [hFuelNat] at hSource
      rw [Project.ClobMatchFuel.Model.matchFuelL_succ_zero fuel ctx.taker
        data.sourceState hRemaining] at hSource
      exact hSource
    · rw [hFuelNat] at hSource
      rw [Project.ClobMatchFuel.Model.matchFuelL_succ_none fuel ctx.taker
        data.sourceState hRemaining hFind] at hSource
      exact hSource

theorem partial_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining) :
    ctx.result = partialState data ctx.taker i := by
  have hFuelPositive : 0 < data.fuel.toNat := by
    by_contra h
    have hZero : data.fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  obtain ⟨fuel, hFuelNat⟩ : ∃ fuel, data.fuel.toNat = fuel + 1 :=
    ⟨data.fuel.toNat - 1, by omega⟩
  have hSource := facts.source
  rw [hFuelNat] at hSource
  rw [Project.ClobMatchFuel.Model.matchFuelL_succ_partial fuel ctx.taker
    data.sourceState i hRemaining hFind hQty] at hSource
  simpa [partialState, RunningData.sourceState] using hSource

theorem full_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining) :
    ctx.result = Project.ClobMatchFuel.Model.matchFuelL
      (data.fuel - 1).toNat ctx.taker (fullState data ctx.taker i) := by
  have hFuelNat : data.fuel.toNat = (data.fuel - 1).toNat + 1 := by
    rw [Project.ClobMatchFuel.Budget.fuel_sub_one_toNat data.fuel hFuel]
    have hFuelPositive : 0 < data.fuel.toNat := by
      by_contra h
      have hZero : data.fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega
  have hSource := facts.source
  rw [hFuelNat] at hSource
  rw [Project.ClobMatchFuel.Model.matchFuelL_succ_full
    (data.fuel - 1).toNat ctx.taker data.sourceState i hRemaining hFind hQty]
    at hSource
  simpa [fullState, RunningData.sourceState] using hSource

theorem allocationCounter_next (initial : UInt64) (steps : Nat) :
    initial + UInt64.ofNat (2 * steps) + 2 =
      initial + UInt64.ofNat (2 * (steps + 1)) := by
  simp [Nat.mul_add]
  ac_rfl

theorem expectedG2_current (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hTrades : ctx.result.trades.length = data.tradeValues.length) :
    data.g2 = ctx.expectedG2 := by
  rw [facts.allocationCounter]
  unfold Context.expectedG2
  rw [hTrades, facts.tradeLength]
  congr 2
  omega

theorem expectedG2_after_append
    (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hTrades : ctx.result.trades.length = data.tradeValues.length + 1) :
    data.g2 + 2 = ctx.expectedG2 := by
  rw [facts.allocationCounter]
  unfold Context.expectedG2
  rw [hTrades, facts.tradeLength]
  have hLength :
      ctx.initialState.trades.length + data.steps + 1 -
          ctx.initialState.trades.length = data.steps + 1 := by
    omega
  rw [hLength]
  exact allocationCounter_next ctx.initialG2 data.steps

end Project.ClobLimit.InternalLoopProgress
