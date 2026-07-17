import Project.ClobMatchFuel.LoopBounds

/-!
# Match-loop source progress

The loop invariant records a residual source computation and the number of
completed full fills.  These lemmas advance that source state for each
dispatcher branch and normalize the corresponding modular counters.
-/

namespace Project.ClobMatchFuel.LoopProgress

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobMatchFuel
  Project.ClobMatchFuel.LoopInvariant

def fullState (data : RunningData) (taker : OrderL) (i : Nat) :
    Model.MatchStateL :=
  { book := data.orders.eraseIdx i
    trades := data.tradeValues ++
      [Model.fillTradeL taker data.orders[i]! data.orders[i]!.oqty]
    remaining := data.remaining - data.orders[i]!.oqty }

def partialState (data : RunningData) (taker : OrderL) (i : Nat) :
    Model.MatchStateL :=
  { book := Model.setQtyL data.orders i
      (data.orders[i]!.oqty - data.remaining)
    trades := data.tradeValues ++
      [Model.fillTradeL taker data.orders[i]! data.remaining]
    remaining := 0 }

theorem stopped_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0)
    (hStop : data.remaining = 0 ∨ findBestL data.orders ctx.taker = none) :
    ctx.result = data.sourceState ∧ ctx.fullFills = data.steps := by
  have hFuelPositive : 0 < data.fuel.toNat := by
    by_contra h
    have hZero : data.fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  obtain ⟨fuel, hFuelNat⟩ : ∃ fuel, data.fuel.toNat = fuel + 1 :=
    ⟨data.fuel.toNat - 1, by omega⟩
  have hSource := facts.source
  have hFills := facts.fullFills
  rcases hStop with hRemaining | hFind
  · rw [hFuelNat] at hSource hFills
    rw [Model.matchFuelL_succ_zero fuel ctx.taker data.sourceState hRemaining]
      at hSource
    rw [Model.fullFillCountL_succ_zero fuel ctx.taker data.sourceState
      hRemaining] at hFills
    simpa using And.intro hSource hFills
  · by_cases hRemaining : data.remaining = 0
    · rw [hFuelNat] at hSource hFills
      rw [Model.matchFuelL_succ_zero fuel ctx.taker data.sourceState hRemaining]
        at hSource
      rw [Model.fullFillCountL_succ_zero fuel ctx.taker data.sourceState
        hRemaining] at hFills
      simpa using And.intro hSource hFills
    · rw [hFuelNat] at hSource hFills
      rw [Model.matchFuelL_succ_none fuel ctx.taker data.sourceState hRemaining
        hFind] at hSource
      rw [Model.fullFillCountL_succ_none fuel ctx.taker data.sourceState
        hRemaining hFind] at hFills
      simpa using And.intro hSource hFills

theorem partial_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining) :
    ctx.result = partialState data ctx.taker i ∧
      ctx.fullFills = data.steps := by
  have hFuelPositive : 0 < data.fuel.toNat := by
    by_contra h
    have hZero : data.fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  obtain ⟨fuel, hFuelNat⟩ : ∃ fuel, data.fuel.toNat = fuel + 1 :=
    ⟨data.fuel.toNat - 1, by omega⟩
  have hSource := facts.source
  have hFills := facts.fullFills
  rw [hFuelNat] at hSource hFills
  rw [Model.matchFuelL_succ_partial fuel ctx.taker data.sourceState i hRemaining
    hFind hQty] at hSource
  rw [Model.fullFillCountL_succ_partial fuel ctx.taker data.sourceState i
    hRemaining hFind hQty] at hFills
  constructor
  · simpa [partialState, RunningData.sourceState] using hSource
  · simpa using hFills

theorem full_source (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining) :
    ctx.result = Model.matchFuelL (data.fuel - 1).toNat ctx.taker
        (fullState data ctx.taker i) ∧
      ctx.fullFills = data.steps + 1 +
        Model.fullFillCountL (data.fuel - 1).toNat ctx.taker
          (fullState data ctx.taker i) := by
  have hFuelNat : data.fuel.toNat = (data.fuel - 1).toNat + 1 := by
    rw [Budget.fuel_sub_one_toNat data.fuel hFuel]
    have hFuelPositive : 0 < data.fuel.toNat := by
      by_contra h
      have hZero : data.fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega
  have hSource := facts.source
  have hFills := facts.fullFills
  rw [hFuelNat] at hSource hFills
  rw [Model.matchFuelL_succ_full (data.fuel - 1).toNat ctx.taker
    data.sourceState i hRemaining hFind hQty] at hSource
  rw [Model.fullFillCountL_succ_full (data.fuel - 1).toNat ctx.taker
    data.sourceState i hRemaining hFind hQty] at hFills
  constructor
  · simpa [fullState, RunningData.sourceState] using hSource
  · simpa [fullState, RunningData.sourceState, Nat.add_assoc] using hFills

theorem allocationCounter_next (initial : UInt64) (steps : Nat) :
    initial + UInt64.ofNat (2 * steps) + 2 =
      initial + UInt64.ofNat (2 * (steps + 1)) := by
  simp [Nat.mul_add]
  ac_rfl

theorem releaseCounter_next (initial : UInt64) (steps : Nat) :
    initial + UInt64.ofNat (steps - 1) +
        (if steps = 0 then 0 else 1) =
      initial + UInt64.ofNat ((steps + 1) - 1) := by
  cases steps with
  | zero => simp
  | succ steps =>
      simp
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

theorem expectedG2_after_append (ctx : Context) (st : Store Unit) (s : Locals)
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

theorem expectedG4_current (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFills : ctx.fullFills = data.steps) : data.g4 = ctx.expectedG4 := by
  rw [facts.releaseCounter4]
  unfold Context.expectedG4
  rw [hFills]

theorem expectedG5_current (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFills : ctx.fullFills = data.steps) : data.g5 = ctx.expectedG5 := by
  rw [facts.releaseCounter5]
  unfold Context.expectedG5
  rw [hFills]

end Project.ClobMatchFuel.LoopProgress
