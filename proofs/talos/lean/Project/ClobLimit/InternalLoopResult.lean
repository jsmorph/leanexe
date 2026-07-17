import Project.ClobLimit.InternalLoopInitial

/-!
# Internal match-loop result

The loop exits through either a completed result frame or a zero-fuel running
frame.  Both cases represent the same source result and allocator counter.
This module converts them to one store predicate and proves the generated
five-value result epilogue.
-/

namespace Project.ClobLimit.InternalLoopResult

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame

structure OutputData where
  bookOwner : UInt64
  book : UInt64
  bookCapacity : UInt64
  tradesOwner : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  g0 : UInt64

structure OutputAt (ctx : Context) (st : Store Unit) (data : OutputData) :
    Prop where
  book48 : 48 ≤ data.book.toNat
  book32 : data.book.toNat +
    fixedArrayBytes ctx.result.book.length 5 < 4294967296
  bookCapacity :
    fixedArrayBytes ctx.result.book.length 5 ≤ data.bookCapacity.toNat
  bookBelow : data.book.toNat + data.bookCapacity.toNat ≤ data.g0.toNat
  trades48 : 48 ≤ data.trades.toNat
  trades32 : data.trades.toNat +
    fixedArrayBytes ctx.result.trades.length 4 < 4294967296
  tradesCapacity :
    fixedArrayBytes ctx.result.trades.length 4 ≤ data.tradesCapacity.toNat
  tradesBelow :
    data.trades.toNat + data.tradesCapacity.toNat ≤ data.g0.toNat
  bookOwned : OwnedOrderArrayAt st data.book data.bookCapacity ctx.result.book
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity ctx.result.trades
  memoryBelow : BytesEqBelow ctx.initialMem st.mem ctx.initialG0.toNat
  pages : st.mem.pages = ctx.initialPages
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 : st.globals.globals[1]? = some (.i64 0)
  global2 : st.globals.globals[2]? = some (.i64 ctx.expectedG2)
  heapMono : ctx.initialG0.toNat <= data.g0.toNat
  heapLimit : data.g0.toNat ≤ ctx.limit
  pageLimit : st.mem.pages ≤ 65536
  addressLimit : ctx.limit < 4294967296
  memoryLimit : ctx.limit ≤ st.mem.pages * 65536

def outputValues (ctx : Context) (data : OutputData) : List Value :=
  [.i64 ctx.result.remaining, .i64 data.trades, .i64 data.tradesOwner,
    .i64 data.book, .i64 data.bookOwner]

def Postcondition (ctx : Context) (st : Store Unit)
    (values : List Value) : Prop :=
  ∃ data, values = outputValues ctx data ∧ OutputAt ctx st data

def completedOutputData (data : CompletedData) : OutputData :=
  { bookOwner := data.bookOwner
    book := data.book
    bookCapacity := data.bookCapacity
    tradesOwner := data.tradesOwner
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0 }

def runningOutputData (data : RunningData) : OutputData :=
  { bookOwner := data.bookOwner
    book := data.book
    bookCapacity := data.bookCapacity
    tradesOwner := data.tradesOwner
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0 }

theorem of_completed (facts : CompletedFacts ctx st s data) :
    OutputAt ctx st (completedOutputData data) := by
  exact {
    book48 := facts.book48
    book32 := facts.book32
    bookCapacity := facts.bookCapacity
    bookBelow := facts.bookBelow
    trades48 := facts.trades48
    trades32 := facts.trades32
    tradesCapacity := facts.tradesCapacity
    tradesBelow := facts.tradesBelow
    bookOwned := facts.bookOwned
    tradesOwned := facts.tradesOwned
    memoryBelow := facts.memoryBelow
    pages := facts.pages
    global0 := facts.global0
    global1 := facts.global1
    global2 := facts.global2
    heapMono := facts.heapMono
    heapLimit := facts.heapLimit
    pageLimit := facts.pageLimit
    addressLimit := facts.addressLimit
    memoryLimit := facts.memoryLimit }

theorem of_zero_running (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel = 0) : OutputAt ctx st (runningOutputData data) := by
  have hSource := facts.source
  rw [hFuel] at hSource
  simp only [UInt64.toNat_zero, Project.ClobMatchFuel.Model.matchFuelL] at hSource
  have hTradeLength : ctx.result.trades.length = data.tradeValues.length := by
    simpa [RunningData.sourceState] using
      congrArg (fun state => state.trades.length) hSource
  have hExpectedG2 := InternalLoopProgress.expectedG2_current ctx st s data
    facts hTradeLength
  exact {
    book48 := facts.book48
    book32 := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.book32
    bookCapacity := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.bookCapacity
    bookBelow := facts.bookBelow
    trades48 := facts.trades48
    trades32 := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.trades32
    tradesCapacity := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.tradesCapacity
    tradesBelow := facts.tradesBelow
    bookOwned := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.bookOwned
    tradesOwned := by
      simpa [runningOutputData, hSource, RunningData.sourceState] using
        facts.tradesOwned
    memoryBelow := facts.memoryBelow
    pages := facts.pages
    global0 := facts.global0
    global1 := facts.global1
    global2 := by
      rw [← hExpectedG2]
      exact facts.global2
    heapMono := facts.heapMono
    heapLimit := by
      have hBudget := facts.budget
      simp [hFuel] at hBudget
      exact hBudget
    pageLimit := facts.pageLimit
    addressLimit := facts.addressLimit
    memoryLimit := facts.memoryLimit }

set_option Elab.async false in
theorem resultEpilogueProg_spec (env : HostEnv Unit) (ctx : Context)
    (st : Store Unit) (base : Locals) (hExit : ExitAt ctx st base)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ (data : OutputData) (final : Locals),
      final.values = outputValues ctx data → OutputAt ctx st data →
      wp «module» rest Q st final env) :
    wp «module» (InternalLoopControl.resultEpilogueProg ++ rest) Q st base
      env := by
  rcases hExit with hCompleted | ⟨data, facts, hFuel⟩
  · rcases hCompleted with ⟨data, facts⟩
    apply InternalLoopControl.resultEpilogue_completed_spec env st base
      data.bookOwner data.book data.tradesOwner data.trades ctx.result.remaining
      facts.result
    apply hDone (completedOutputData data)
    · rfl
    · exact of_completed facts
  · rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
      hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTradesOwner, hTrades,
      hRemaining, hRunning, hScratch⟩
    have hSource := facts.source
    rw [hFuel] at hSource
    simp only [UInt64.toNat_zero, Project.ClobMatchFuel.Model.matchFuelL] at hSource
    apply InternalLoopControl.resultEpilogue_running_spec env st base
      data.bookOwner data.book data.tradesOwner data.trades data.remaining
      hParams hLocals hValues hBookOwner hBook hTradesOwner hTrades hRemaining
      hRunning
    apply hDone (runningOutputData data)
    · simp [InternalLoopControl.runningResultFrame, outputValues,
        runningOutputData, hSource, RunningData.sourceState]
    · exact of_zero_running facts hFuel

end Project.ClobLimit.InternalLoopResult
