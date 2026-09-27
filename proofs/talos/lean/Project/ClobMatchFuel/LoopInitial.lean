import Project.ClobMatchFuel.Loop

/-!
# Initial match-loop invariant

The exported parameters determine one running state before the first guard.
This module separates that logical construction from the generated
initialization instructions.  Its premises state every memory and allocator
fact required by later iterations.
-/

namespace Project.ClobMatchFuel.LoopInitial

open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.LoopInvariant

def initialData (ctx : Context) (book bookCapacity trades tradesCapacity g0 : UInt64)
    (nodes : List FreeNode) : RunningData :=
  { steps := 0
    fuel := ctx.initialFuel
    bookOwner := 0
    book := book
    bookCapacity := bookCapacity
    trades := trades
    tradesCapacity := tradesCapacity
    remaining := ctx.initialState.remaining
    oldTradesTracker := 0
    g0 := g0
    g2 := ctx.initialG2
    g4 := ctx.initialG4
    g5 := ctx.initialG5
    orders := ctx.initialState.book
    tradeValues := ctx.initialState.trades
    nodes := nodes }

theorem of_initial (ctx : Context) (st : Store Unit) (s : Locals)
    (book bookCapacity trades tradesCapacity g0 : UInt64)
    (nodes : List FreeNode)
    (hLocals : LoopLocalsAt ctx
      (initialData ctx book bookCapacity trades tradesCapacity g0 nodes) s)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat +
      fixedArrayBytes ctx.initialState.book.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes ctx.initialState.book.length 5 ≤
      bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookFree : FreeListSeparatedFromFixedArray nodes book bookCapacity)
    (hTrades48 : 48 ≤ trades.toNat)
    (hTrades32 : trades.toNat +
      fixedArrayBytes ctx.initialState.trades.length 4 < 4294967296)
    (hTradesCapacity : fixedArrayBytes ctx.initialState.trades.length 4 ≤
      tradesCapacity.toNat)
    (hTradesBelow : trades.toNat + tradesCapacity.toNat ≤ g0.toNat)
    (hTradesFree : FreeListSeparatedFromFixedArray nodes trades tradesCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity ctx.initialState.book)
    (hTradesOwned : OwnedTradeArrayAt st trades tradesCapacity
      ctx.initialState.trades)
    (hFreeList : FreeListAt st.mem nodes)
    (hG0 : st.globals.globals[0]? = some (.i64 g0))
    (hG1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hG2 : st.globals.globals[2]? = some (.i64 ctx.initialG2))
    (hG4 : st.globals.globals[4]? = some (.i64 ctx.initialG4))
    (hG5 : st.globals.globals[5]? = some (.i64 ctx.initialG5))
    (hMemoryFrame : MemoryFrame.BytesEqFrom ctx.initialMem st.mem ctx.limit)
    (hPages : st.mem.pages = ctx.initialPages)
    (hPageLimit : st.mem.pages ≤ 65536)
    (hAddressLimit : ctx.limit < 4294967296)
    (hMemoryLimit : ctx.limit ≤ st.mem.pages * 65536)
    (hBudget : g0.toNat + ctx.initialFuel.toNat *
      Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤ ctx.limit) :
    RunningFacts ctx st s
      (initialData ctx book bookCapacity trades tradesCapacity g0 nodes) := by
  refine {
    locals := hLocals
    bookOwner := by simp [initialData]
    oldTradesTracker := by simp [initialData]
    fuelSpent := by simp [initialData]
    source := rfl
    fullFills := by
      simp [initialData, Context.fullFills, RunningData.sourceState]
    bookLength := by simp [initialData, Context.bookLimit]
    tradeLength := by simp [initialData]
    book48 := hBook48
    book32 := hBook32
    bookCapacity := hBookCapacity
    bookBelow := hBookBelow
    bookFree := hBookFree
    trades48 := hTrades48
    trades32 := hTrades32
    tradesCapacity := hTradesCapacity
    tradesBelow := hTradesBelow
    tradesFree := hTradesFree
    nodesBelow := hNodesBelow
    bookOwned := hBookOwned
    tradesOwned := hTradesOwned
    freeList := hFreeList
    global0 := hG0
    global1 := hG1
    global2 := hG2
    global4 := hG4
    global5 := hG5
    allocationCounter := by simp [initialData]
    releaseCounter4 := by simp [initialData]
    releaseCounter5 := by simp [initialData]
    memoryFrame := hMemoryFrame
    pages := hPages
    pageLimit := hPageLimit
    addressLimit := hAddressLimit
    memoryLimit := hMemoryLimit
    budget := hBudget }

end Project.ClobMatchFuel.LoopInitial
