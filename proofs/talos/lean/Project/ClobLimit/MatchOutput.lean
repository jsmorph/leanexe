import Project.ClobLimit.MatchInvariant
import Project.ClobMatchFuel.LoopResult

namespace Project.ClobLimit.MatchOutput

open Wasm Project.Clob Project.Runtime Project.ClobLimit
  Project.ClobLimit.MatchInvariant
  Project.ClobMatchFuel.AllocatorFrame

structure OutputData where
  bookOwner : UInt64
  book : UInt64
  bookCapacity : UInt64
  tradesOwner : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  g0 : UInt64
  nodes : List FreeNode

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
  bookFree : FreeListSeparatedFromFixedArray data.nodes data.book data.bookCapacity
  tradesFree : FreeListSeparatedFromFixedArray data.nodes data.trades data.tradesCapacity
  nodesBelow : ∀ node ∈ data.nodes, node.root.toNat + node.capacity.toNat ≤ data.g0.toNat
  nodesAbove : ∀ node ∈ data.nodes, ctx.initialG0.toNat + 48 ≤ node.root.toNat
  freeList : FreeListAt st.mem data.nodes
  memoryBelow : Project.ClobMatchFuel.MemoryBelow.BytesEqBelow ctx.initialMem st.mem ctx.initialG0.toNat
  pages : st.mem.pages = ctx.initialPages
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 : st.globals.globals[1]? = some (.i64 (freeHead data.nodes))
  global2 : st.globals.globals[2]? = some (.i64 ctx.expectedG2)
  global4 : st.globals.globals[4]? = some (.i64 ctx.expectedG4)
  global5 : st.globals.globals[5]? = some (.i64 ctx.expectedG5)
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

def completedOutputData (data : CompletedData) (bookOwner tradesOwner : UInt64) : OutputData :=
  { bookOwner := bookOwner
    book := data.book
    bookCapacity := data.bookCapacity
    tradesOwner := tradesOwner
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0
    nodes := data.nodes }

def runningOutputData (data : RunningData) (tradesOwner : UInt64) : OutputData :=
  { bookOwner := data.bookOwner
    book := data.book
    bookCapacity := data.bookCapacity
    tradesOwner := tradesOwner
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    g0 := data.g0
    nodes := data.nodes }

theorem of_completed (facts : CompletedFacts ctx st s data bookOwner tradesOwner) :
    OutputAt ctx st (completedOutputData data bookOwner tradesOwner) := by
  exact {
    book48 := facts.base.book48
    book32 := facts.base.book32
    bookCapacity := facts.base.bookCapacity
    bookBelow := facts.base.bookBelow
    trades48 := facts.base.trades48
    trades32 := facts.base.trades32
    tradesCapacity := facts.base.tradesCapacity
    tradesBelow := facts.base.tradesBelow
    bookOwned := facts.base.bookOwned
    tradesOwned := facts.base.tradesOwned
    bookFree := facts.base.bookFree
    tradesFree := facts.base.tradesFree
    nodesBelow := facts.base.nodesBelow
    nodesAbove := facts.nodesAbove
    freeList := facts.base.freeList
    memoryBelow := facts.memoryBelow
    pages := facts.base.pages
    global0 := facts.base.global0
    global1 := facts.base.global1
    global2 := facts.base.global2
    global4 := facts.base.global4
    global5 := facts.base.global5
    heapMono := facts.heapMono
    heapLimit := facts.base.heapLimit
    pageLimit := facts.base.pageLimit
    addressLimit := facts.base.addressLimit
    memoryLimit := facts.base.memoryLimit }

theorem of_zero_running (facts : RunningFacts ctx st s data tradesOwner)
    (hFuel : data.fuel = 0) : OutputAt ctx st (runningOutputData data tradesOwner) := by
  have hSource := facts.base.source
  rw [hFuel] at hSource
  simp only [UInt64.toNat_zero, Project.ClobMatchFuel.Model.matchFuelL] at hSource
  have hTradeLength : ctx.result.trades.length = data.tradeValues.length := by
    simpa [Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
      congrArg (fun state => state.trades.length) hSource
  have hCommon := Project.ClobMatchFuel.LoopResult.of_zero_running facts.base hFuel
  exact {
    book48 := facts.base.book48
    book32 := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.book32
    bookCapacity := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.bookCapacity
    bookBelow := facts.base.bookBelow
    trades48 := facts.base.trades48
    trades32 := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.trades32
    tradesCapacity := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.tradesCapacity
    tradesBelow := facts.base.tradesBelow
    bookOwned := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.bookOwned
    tradesOwned := by
      simpa [runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState] using
        facts.base.tradesOwned
    bookFree := facts.base.bookFree
    tradesFree := facts.base.tradesFree
    nodesBelow := facts.base.nodesBelow
    nodesAbove := facts.nodesAbove
    freeList := facts.base.freeList
    memoryBelow := facts.memoryBelow
    pages := facts.base.pages
    global0 := facts.base.global0
    global1 := facts.base.global1
    global2 := hCommon.global2
    global4 := hCommon.global4
    global5 := hCommon.global5
    heapMono := facts.heapMono
    heapLimit := by
      have hBudget := facts.base.budget
      simp [hFuel] at hBudget
      exact hBudget
    pageLimit := facts.base.pageLimit
    addressLimit := facts.base.addressLimit
    memoryLimit := facts.base.memoryLimit }

end Project.ClobLimit.MatchOutput
