import Project.ClobLimit.InternalLoopControl
import Project.ClobMatchFuel.Budget

/-!
# Internal match-loop invariant

The loop carries source progress, represented arrays, allocator state, and a
fixed allocation budget.  Running states retain the exact recursive parameters.
Completed states retain the semantic result returned by the epilogue.
-/

namespace Project.ClobLimit.InternalLoopInvariant

open Wasm Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.AllocatorFrame

structure Context where
  initialFuel : UInt64
  taker : OrderL
  initialState : Project.ClobMatchFuel.Model.MatchStateL
  initialG0 : UInt64
  initialG2 : UInt64
  initialMem : Mem
  initialPages : Nat
  limit : Nat

def Context.bookLimit (ctx : Context) : Nat :=
  ctx.initialState.book.length

def Context.tradeLimit (ctx : Context) : Nat :=
  ctx.initialState.trades.length + ctx.initialFuel.toNat

def Context.result (ctx : Context) : Project.ClobMatchFuel.Model.MatchStateL :=
  Project.ClobMatchFuel.Model.matchFuelL ctx.initialFuel.toNat ctx.taker
    ctx.initialState

def Context.expectedG2 (ctx : Context) : UInt64 :=
  ctx.initialG2 + UInt64.ofNat
    (2 * (ctx.result.trades.length - ctx.initialState.trades.length))

def BytesEqBelow (before after : Mem) (limit : Nat) : Prop :=
  ∀ a : Nat, a < limit → after.bytes a = before.bytes a

theorem BytesEqBelow.trans {before middle after : Mem} {limit : Nat}
    (hBefore : BytesEqBelow before middle limit)
    (hAfter : BytesEqBelow middle after limit) :
    BytesEqBelow before after limit := by
  intro a ha
  exact (hAfter a ha).trans (hBefore a ha)

structure RunningData where
  steps : Nat
  fuel : UInt64
  bookOwner : UInt64
  book : UInt64
  bookCapacity : UInt64
  tradesOwner : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  remaining : UInt64
  g0 : UInt64
  g2 : UInt64
  orders : List OrderL
  tradeValues : List TradeL

def RunningData.sourceState (data : RunningData) :
    Project.ClobMatchFuel.Model.MatchStateL :=
  { book := data.orders
    trades := data.tradeValues
    remaining := data.remaining }

def LoopLocalsAt (ctx : Context) (data : RunningData) (s : Locals) : Prop :=
  s.params.length = 11 ∧
  s.locals.length = 64 ∧
  s.values = [] ∧
  s.get 0 = some (.i64 data.fuel) ∧
  s.get 1 = some (.i64 ctx.taker.oid) ∧
  s.get 2 = some (.i64 ctx.taker.otrader) ∧
  s.get 3 = some (.i64 ctx.taker.oside) ∧
  s.get 4 = some (.i64 ctx.taker.oprice) ∧
  s.get 5 = some (.i64 ctx.taker.oqty) ∧
  s.get 6 = some (.i64 data.bookOwner) ∧
  s.get 7 = some (.i64 data.book) ∧
  s.get 8 = some (.i64 data.tradesOwner) ∧
  s.get 9 = some (.i64 data.trades) ∧
  s.get 10 = some (.i64 data.remaining) ∧
  s.get 16 = some (.i64 0) ∧
  InternalIteration.AllocScratchAt s

structure RunningFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) : Prop where
  locals : LoopLocalsAt ctx data s
  fuelSpent : ctx.initialFuel.toNat = data.steps + data.fuel.toNat
  source : ctx.result =
    Project.ClobMatchFuel.Model.matchFuelL data.fuel.toNat ctx.taker
      data.sourceState
  bookLength : data.orders.length ≤ ctx.bookLimit
  tradeLength :
    data.tradeValues.length = ctx.initialState.trades.length + data.steps
  book48 : 48 ≤ data.book.toNat
  book32 :
    data.book.toNat + fixedArrayBytes data.orders.length 5 < 4294967296
  bookCapacity :
    fixedArrayBytes data.orders.length 5 ≤ data.bookCapacity.toNat
  bookBelow :
    data.book.toNat + data.bookCapacity.toNat ≤ data.g0.toNat
  trades48 : 48 ≤ data.trades.toNat
  trades32 : data.trades.toNat +
    fixedArrayBytes data.tradeValues.length 4 < 4294967296
  tradesCapacity :
    fixedArrayBytes data.tradeValues.length 4 ≤ data.tradesCapacity.toNat
  tradesBelow :
    data.trades.toNat + data.tradesCapacity.toNat ≤ data.g0.toNat
  bookOwned :
    OwnedOrderArrayAt st data.book data.bookCapacity data.orders
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity data.tradeValues
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 : st.globals.globals[1]? = some (.i64 0)
  global2 : st.globals.globals[2]? = some (.i64 data.g2)
  allocationCounter :
    data.g2 = ctx.initialG2 + UInt64.ofNat (2 * data.steps)
  heapMono : ctx.initialG0.toNat ≤ data.g0.toNat
  memoryBelow : BytesEqBelow ctx.initialMem st.mem ctx.initialG0.toNat
  pages : st.mem.pages = ctx.initialPages
  pageLimit : st.mem.pages ≤ 65536
  addressLimit : ctx.limit < 4294967296
  memoryLimit : ctx.limit ≤ st.mem.pages * 65536
  budget : data.g0.toNat + data.fuel.toNat *
    Project.ClobMatchFuel.Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤
      ctx.limit

def RunningAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data, RunningFacts ctx st s data

theorem RunningAt.values (h : RunningAt ctx st s) : s.values = [] := by
  rcases h with ⟨data, facts⟩
  exact facts.locals.2.2.1

structure CompletedData where
  bookOwner : UInt64
  book : UInt64
  bookCapacity : UInt64
  tradesOwner : UInt64
  trades : UInt64
  tradesCapacity : UInt64
  fuel : UInt64
  g0 : UInt64

structure CompletedFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : CompletedData) : Prop where
  result : InternalIteration.CompletedResultAt s data.bookOwner data.book
    data.tradesOwner data.trades ctx.result.remaining
  fuelLocal : s.get 0 = some (.i64 data.fuel)
  bookOwned :
    OwnedOrderArrayAt st data.book data.bookCapacity ctx.result.book
  tradesOwned :
    OwnedTradeArrayAt st data.trades data.tradesCapacity ctx.result.trades
  memoryBelow : BytesEqBelow ctx.initialMem st.mem ctx.initialG0.toNat
  pages : st.mem.pages = ctx.initialPages
  global0 : st.globals.globals[0]? = some (.i64 data.g0)
  global1 : st.globals.globals[1]? = some (.i64 0)
  global2 : st.globals.globals[2]? = some (.i64 ctx.expectedG2)

def CompletedAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data, CompletedFacts ctx st s data

theorem CompletedAt.values (h : CompletedAt ctx st s) : s.values = [] := by
  rcases h with ⟨data, facts⟩
  exact facts.result.2.2.2.2.2.2.2.2

def Invariant (ctx : Context) : AssertionF Unit :=
  fun st s => RunningAt ctx st s ∨ CompletedAt ctx st s

theorem Invariant.values (h : Invariant ctx st s) : s.values = [] := by
  rcases h with hRunning | hCompleted
  · exact hRunning.values
  · exact hCompleted.values

def ExitAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  CompletedAt ctx st s ∨
    ∃ data, RunningFacts ctx st s data ∧ data.fuel = 0

theorem ExitAt.values (h : ExitAt ctx st s) : s.values = [] := by
  rcases h with hCompleted | ⟨data, facts, hFuel⟩
  · exact hCompleted.values
  · exact facts.locals.2.2.1

def measure (_ : Store Unit) (s : Locals) : Nat :=
  match s.get 16 with
  | some (.i64 done) =>
      if done = 0 then
        match s.get 0 with
        | some (.i64 fuel) => 2 * fuel.toNat + 1
        | _ => 0
      else 0
  | _ => 0

theorem measure_running (facts : RunningFacts ctx st s data) :
    measure st s = 2 * data.fuel.toNat + 1 := by
  rcases facts.locals with ⟨_, _, _, hFuel, _, _, _, _, _, _, _, _, _, _,
    hRunning, _⟩
  unfold measure
  rw [hRunning, hFuel]
  rfl

theorem measure_completed (h : CompletedAt ctx st s) : measure st s = 0 := by
  rcases h with ⟨data, facts⟩
  rcases facts.result with
    ⟨_, _, _, _, _, hDone, hParams, hLocals, hValues⟩
  have hDoneGet : s.get 16 = some (.i64 1) := by
    simpa [Locals.get, hParams, hLocals] using hDone
  unfold measure
  rw [hDoneGet]
  simp

end Project.ClobLimit.InternalLoopInvariant
