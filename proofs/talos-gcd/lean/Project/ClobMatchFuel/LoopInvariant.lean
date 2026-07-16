import Project.ClobMatchFuel.Budget
import Project.ClobMatchFuel.Initialization

/-!
# Match-loop invariant

The outer loop carries source progress, owned arrays, allocator state, and the
generated recursive locals.  Running states retain the budget required by the
next full or partial update.  Completed states contain the exact source result
and the public allocator counters used by the epilogue theorem.
-/

namespace Project.ClobMatchFuel.LoopInvariant

open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

structure Context where
  initialFuel : UInt64
  taker : OrderL
  initialState : Model.MatchStateL
  initialG2 : UInt64
  initialG4 : UInt64
  initialG5 : UInt64
  initialPages : Nat
  limit : Nat

def Context.bookLimit (ctx : Context) : Nat :=
  ctx.initialState.book.length

def Context.tradeLimit (ctx : Context) : Nat :=
  ctx.initialState.trades.length + ctx.initialFuel.toNat

def Context.result (ctx : Context) : Model.MatchStateL :=
  Model.matchFuelL ctx.initialFuel.toNat ctx.taker ctx.initialState

def Context.fullFills (ctx : Context) : Nat :=
  Model.fullFillCountL ctx.initialFuel.toNat ctx.taker ctx.initialState

def Context.expectedG2 (ctx : Context) : UInt64 :=
  ctx.initialG2 + UInt64.ofNat
    (2 * (ctx.result.trades.length - ctx.initialState.trades.length))

def Context.expectedG4 (ctx : Context) : UInt64 :=
  ctx.initialG4 + UInt64.ofNat (ctx.fullFills - 1)

def Context.expectedG5 (ctx : Context) : UInt64 :=
  ctx.initialG5 + UInt64.ofNat (ctx.fullFills - 1)

structure RunningData where
  steps : Nat
  fuel : UInt64
  bookOwner : UInt64
  book : UInt64
  bookCapacity : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  remaining : UInt64
  oldTradesTracker : UInt64
  g0 : UInt64
  g2 : UInt64
  g4 : UInt64
  g5 : UInt64
  orders : List OrderL
  tradeValues : List TradeL
  nodes : List FreeNode

def RunningData.sourceState (data : RunningData) : Model.MatchStateL :=
  { book := data.orders
    trades := data.tradeValues
    remaining := data.remaining }

def LoopLocalsAt (ctx : Context) (data : RunningData) (s : Locals) : Prop :=
  s.params.length = 9 ∧
  s.locals.length = 76 ∧
  s.values = [] ∧
  s.get 0 = some (.i64 data.fuel) ∧
  s.get 9 = some (.i64 ctx.taker.oid) ∧
  s.get 10 = some (.i64 ctx.taker.otrader) ∧
  s.get 11 = some (.i64 ctx.taker.oside) ∧
  s.get 12 = some (.i64 ctx.taker.oprice) ∧
  s.get 13 = some (.i64 ctx.taker.oqty) ∧
  s.get 14 = some (.i64 data.bookOwner) ∧
  s.get 15 = some (.i64 data.book) ∧
  s.get 17 = some (.i64 data.trades) ∧
  s.get 18 = some (.i64 data.remaining) ∧
  s.get 19 = some (.i64 0) ∧
  s.get 20 = some (.i64 data.oldTradesTracker) ∧
  s.get 24 = some (.i64 0) ∧
  FullTradeUpdate.AllocScratchAt s

structure RunningFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) : Prop where
  locals : LoopLocalsAt ctx data s
  bookOwner : data.bookOwner = if data.steps = 0 then 0 else data.book
  oldTradesTracker :
    data.oldTradesTracker = if data.steps = 0 then 0 else data.trades
  fuelSpent : ctx.initialFuel.toNat = data.steps + data.fuel.toNat
  source : ctx.result =
    Model.matchFuelL data.fuel.toNat ctx.taker data.sourceState
  fullFills : ctx.fullFills = data.steps +
    Model.fullFillCountL data.fuel.toNat ctx.taker data.sourceState
  bookLength : data.orders.length ≤ ctx.bookLimit
  tradeLength :
    data.tradeValues.length = ctx.initialState.trades.length + data.steps
  book48 : 48 ≤ data.book.toNat
  book32 : data.book.toNat + fixedArrayBytes data.orders.length 5 < 4294967296
  bookCapacity :
    fixedArrayBytes data.orders.length 5 ≤ data.bookCapacity.toNat
  bookBelow : data.book.toNat + data.bookCapacity.toNat ≤ data.g0.toNat
  bookFree :
    FreeListSeparatedFromFixedArray data.nodes data.book data.bookCapacity
  trades48 : 48 ≤ data.trades.toNat
  trades32 : data.trades.toNat +
    fixedArrayBytes data.tradeValues.length 4 < 4294967296
  tradesCapacity :
    fixedArrayBytes data.tradeValues.length 4 ≤ data.tradesCapacity.toNat
  tradesBelow :
    data.trades.toNat + data.tradesCapacity.toNat ≤ data.g0.toNat
  tradesFree :
    FreeListSeparatedFromFixedArray data.nodes data.trades data.tradesCapacity
  nodesBelow : ∀ node ∈ data.nodes,
    node.root.toNat + node.capacity.toNat ≤ data.g0.toNat
  bookOwned : OwnedOrderArrayAt st data.book data.bookCapacity data.orders
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity data.tradeValues
  freeList : FreeListAt st.mem data.nodes
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 :
    st.globals.globals[1]? = some (.i64 (freeHead data.nodes))
  global2 : st.globals.globals[2]? = some (.i64 data.g2)
  global4 : st.globals.globals[4]? = some (.i64 data.g4)
  global5 : st.globals.globals[5]? = some (.i64 data.g5)
  allocationCounter :
    data.g2 = ctx.initialG2 + UInt64.ofNat (2 * data.steps)
  releaseCounter4 :
    data.g4 = ctx.initialG4 + UInt64.ofNat (data.steps - 1)
  releaseCounter5 :
    data.g5 = ctx.initialG5 + UInt64.ofNat (data.steps - 1)
  pages : st.mem.pages = ctx.initialPages
  pageLimit : st.mem.pages ≤ 65536
  addressLimit : ctx.limit < 4294967296
  memoryLimit : ctx.limit ≤ st.mem.pages * 65536
  budget : data.g0.toNat + data.fuel.toNat *
    Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤ ctx.limit

def RunningAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data, RunningFacts ctx st s data

theorem RunningAt.values (h : RunningAt ctx st s) : s.values = [] := by
  rcases h with ⟨data, facts⟩
  exact facts.locals.2.2.1

structure CompletedData where
  book : UInt64
  bookCapacity : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  g0 : UInt64
  nodes : List FreeNode

structure CompletedFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : CompletedData) : Prop where
  result : LoopControl.CompletedResultAt s data.book data.trades
    ctx.result.remaining
  bookOwned :
    OwnedOrderArrayAt st data.book data.bookCapacity ctx.result.book
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity ctx.result.trades
  freeList : FreeListAt st.mem data.nodes
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 :
    st.globals.globals[1]? = some (.i64 (freeHead data.nodes))
  global2 : st.globals.globals[2]? = some (.i64 ctx.expectedG2)
  global4 : st.globals.globals[4]? = some (.i64 ctx.expectedG4)
  global5 : st.globals.globals[5]? = some (.i64 ctx.expectedG5)

def CompletedAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data, CompletedFacts ctx st s data

theorem CompletedAt.values (h : CompletedAt ctx st s) : s.values = [] := by
  rcases h with ⟨data, facts⟩
  exact facts.result.2.2.2.2.2.2

def Invariant (ctx : Context) : AssertionF Unit :=
  fun st s => RunningAt ctx st s ∨ CompletedAt ctx st s

theorem Invariant.values (h : Invariant ctx st s) : s.values = [] := by
  rcases h with hRunning | hCompleted
  · exact hRunning.values
  · exact hCompleted.values

def measure (_ : Store Unit) (s : Locals) : Nat :=
  match s.get 24 with
  | some (.i64 done) =>
      if done = 0 then
        match s.get 0 with
        | some (.i64 fuel) => 2 * fuel.toNat + 1
        | _ => 0
      else 0
  | _ => 0

theorem measure_running (facts : RunningFacts ctx st s data) :
    measure st s = 2 * data.fuel.toNat + 1 := by
  rcases facts.locals with ⟨_, _, _, hFuel, _, _, _, _, _, _, _, _, _, _, _,
    hRunning, _⟩
  unfold measure
  rw [hRunning]
  rw [hFuel]
  rfl

theorem measure_completed (h : CompletedAt ctx st s) : measure st s = 0 := by
  rcases h with ⟨data, facts⟩
  rcases facts.result with
    ⟨_, _, _, hDone, hParams, hLocals, hValues⟩
  have hDoneGet : s.get 24 = some (.i64 1) := by
    simpa [Locals.get, hParams, hLocals] using hDone
  unfold measure
  rw [hDoneGet]
  simp

end Project.ClobMatchFuel.LoopInvariant
