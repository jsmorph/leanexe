import Project.ClobLimit.InternalLoop

/-!
# Initial internal match-loop invariant

The recursive parameters determine one running state before the first guard.
This module separates that logical construction from the generated completion
flag initialization.  Its premises state every memory and allocator fact
required by later iterations.
-/

namespace Project.ClobLimit.InternalLoopInitial

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame

def initialData (ctx : Context)
    (bookOwner book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64) :
    RunningData :=
  { steps := 0
    fuel := ctx.initialFuel
    bookOwner := bookOwner
    book := book
    bookCapacity := bookCapacity
    tradesOwner := tradesOwner
    trades := trades
    tradesCapacity := tradesCapacity
    remaining := ctx.initialState.remaining
    g0 := g0
    g2 := ctx.initialG2
    orders := ctx.initialState.book
    tradeValues := ctx.initialState.trades }

theorem of_initial (ctx : Context) (st : Store Unit) (s : Locals)
    (bookOwner book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64)
    (hLocals : LoopLocalsAt ctx
      (initialData ctx bookOwner book bookCapacity tradesOwner trades
        tradesCapacity g0) s)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat +
      fixedArrayBytes ctx.initialState.book.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes ctx.initialState.book.length 5 ≤
      bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hTrades48 : 48 ≤ trades.toNat)
    (hTrades32 : trades.toNat +
      fixedArrayBytes ctx.initialState.trades.length 4 < 4294967296)
    (hTradesCapacity : fixedArrayBytes ctx.initialState.trades.length 4 ≤
      tradesCapacity.toNat)
    (hTradesBelow : trades.toNat + tradesCapacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity
      ctx.initialState.book)
    (hTradesOwned : OwnedTradeArrayAt st trades tradesCapacity
      ctx.initialState.trades)
    (hG0 : st.globals.globals[0]? = some (.i64 g0))
    (hG1 : st.globals.globals[1]? = some (.i64 0))
    (hG2 : st.globals.globals[2]? = some (.i64 ctx.initialG2))
    (hHeapMono : ctx.initialG0.toNat ≤ g0.toNat)
    (hMemoryBelow : BytesEqBelow ctx.initialMem st.mem ctx.initialG0.toNat)
    (hPages : st.mem.pages = ctx.initialPages)
    (hPageLimit : st.mem.pages ≤ 65536)
    (hAddressLimit : ctx.limit < 4294967296)
    (hMemoryLimit : ctx.limit ≤ st.mem.pages * 65536)
    (hBudget : g0.toNat + ctx.initialFuel.toNat *
      Project.ClobMatchFuel.Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤
        ctx.limit) :
    RunningFacts ctx st s
      (initialData ctx bookOwner book bookCapacity tradesOwner trades
        tradesCapacity g0) := by
  refine {
    locals := hLocals
    fuelSpent := by simp [initialData]
    source := rfl
    bookLength := by simp [initialData, Context.bookLimit]
    tradeLength := by simp [initialData]
    book48 := hBook48
    book32 := hBook32
    bookCapacity := hBookCapacity
    bookBelow := hBookBelow
    trades48 := hTrades48
    trades32 := hTrades32
    tradesCapacity := hTradesCapacity
    tradesBelow := hTradesBelow
    bookOwned := hBookOwned
    tradesOwned := hTradesOwned
    global0 := hG0
    global1 := hG1
    global2 := hG2
    allocationCounter := by simp [initialData]
    heapMono := hHeapMono
    memoryBelow := hMemoryBelow
    pages := hPages
    pageLimit := hPageLimit
    addressLimit := hAddressLimit
    memoryLimit := hMemoryLimit
    budget := hBudget }

end Project.ClobLimit.InternalLoopInitial
