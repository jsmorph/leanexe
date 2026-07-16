import Project.ClobMatchFuel.LoopInitial

/-!
# Match-loop public result

The loop exits through either a completed result frame or a zero-fuel running
frame.  Both cases represent the same source result and public allocator
counters.  This module converts them to one store predicate and proves the
generated result epilogue.
-/

namespace Project.ClobMatchFuel.LoopResult

open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.LoopInvariant

structure OutputData where
  book : UInt64
  bookCapacity : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  g0 : UInt64
  nodes : List FreeNode

structure OutputAt (ctx : Context) (st : Store Unit) (data : OutputData) : Prop where
  bookOwned : OwnedOrderArrayAt st data.book data.bookCapacity ctx.result.book
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity ctx.result.trades
  freeList : FreeListAt st.mem data.nodes
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 : st.globals.globals[1]? = some (.i64 (freeHead data.nodes))
  global2 : st.globals.globals[2]? = some (.i64 ctx.expectedG2)
  global4 : st.globals.globals[4]? = some (.i64 ctx.expectedG4)
  global5 : st.globals.globals[5]? = some (.i64 ctx.expectedG5)

def outputValues (ctx : Context) (data : OutputData) : List Value :=
  [.i64 ctx.result.remaining, .i64 data.trades, .i64 data.book]

def Postcondition (ctx : Context) (st : Store Unit) (values : List Value) : Prop :=
  ∃ data, values = outputValues ctx data ∧ OutputAt ctx st data

def completedOutputData (data : CompletedData) : OutputData :=
  { book := data.book
    bookCapacity := data.bookCapacity
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0
    nodes := data.nodes }

def runningOutputData (data : RunningData) : OutputData :=
  { book := data.book
    bookCapacity := data.bookCapacity
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0
    nodes := data.nodes }

theorem of_completed (facts : CompletedFacts ctx st s data) :
    OutputAt ctx st (completedOutputData data) := by
  exact {
    bookOwned := facts.bookOwned
    tradesOwned := facts.tradesOwned
    freeList := facts.freeList
    global0 := facts.global0
    global1 := facts.global1
    global2 := facts.global2
    global4 := facts.global4
    global5 := facts.global5 }

theorem of_zero_running (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel = 0) : OutputAt ctx st (runningOutputData data) := by
  have hSource := facts.source
  have hFills := facts.fullFills
  rw [hFuel] at hSource hFills
  simp only [UInt64.toNat_zero, Model.matchFuelL, Model.fullFillCountL,
    Nat.add_zero] at hSource hFills
  have hTradeLength : ctx.result.trades.length = data.tradeValues.length := by
    simpa [RunningData.sourceState] using
      congrArg (fun state => state.trades.length) hSource
  have hG2 := LoopProgress.expectedG2_current ctx st s data facts hTradeLength
  have hG4 := LoopProgress.expectedG4_current ctx st s data facts hFills
  have hG5 := LoopProgress.expectedG5_current ctx st s data facts hFills
  exact {
    bookOwned := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.bookOwned
    tradesOwned := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.tradesOwned
    freeList := facts.freeList
    global0 := facts.global0
    global1 := facts.global1
    global2 := by
      rw [← hG2]
      exact facts.global2
    global4 := by
      rw [← hG4]
      exact facts.global4
    global5 := by
      rw [← hG5]
      exact facts.global5 }

set_option Elab.async false in
theorem resultEpilogueProg_spec (env : HostEnv Unit) (ctx : Context)
    (st : Store Unit) (base : Locals) (hExit : ExitAt ctx st base)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ (data : OutputData) (final : Locals),
      final.values = outputValues ctx data → OutputAt ctx st data →
      wp «module» rest Q st final env) :
    wp «module» (LoopControl.resultEpilogueProg ++ rest) Q st base env := by
  rcases hExit with hCompleted | ⟨data, facts, hFuel⟩
  · rcases hCompleted with ⟨data, facts⟩
    apply LoopControl.resultEpilogue_completed_spec env st base data.book
      data.trades ctx.result.remaining facts.result
    apply hDone (completedOutputData data)
    · rfl
    · exact of_completed facts
  · rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
      hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTrades, hRemaining,
      hOldBook, hOldTrades, hRunning, hScratch⟩
    have hSource := facts.source
    rw [hFuel] at hSource
    simp only [UInt64.toNat_zero, Model.matchFuelL] at hSource
    apply LoopControl.resultEpilogue_running_spec env st base data.book
      data.trades data.remaining hParams hLocals hValues hBook hTrades hRemaining
      hRunning
    apply hDone (runningOutputData data)
    · simp [LoopControl.runningResultFrame, outputValues, runningOutputData,
        hSource, RunningData.sourceState]
    · exact of_zero_running facts hFuel

end Project.ClobMatchFuel.LoopResult
