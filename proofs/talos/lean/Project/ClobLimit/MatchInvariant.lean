import Project.ClobMatchFuel.LoopBranches
import Project.ClobLimit.MatchDispatch

namespace Project.ClobLimit.MatchInvariant
open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel

abbrev BaseContext := LoopInvariant.Context
abbrev RunningData := LoopInvariant.RunningData
abbrev CompletedData := LoopInvariant.CompletedData

structure Context where
  initialFuel : UInt64
  taker : OrderL
  initialState : Model.MatchStateL
  initialG0 : UInt64
  initialG2 : UInt64
  initialG4 : UInt64
  initialG5 : UInt64
  initialMem : Mem
  initialPages : Nat
  limit : Nat

def Context.base (ctx : Context) : BaseContext :=
  { initialFuel := ctx.initialFuel, taker := ctx.taker,
    initialState := ctx.initialState, initialG2 := ctx.initialG2,
    initialG4 := ctx.initialG4, initialG5 := ctx.initialG5,
    initialMem := ctx.initialMem, initialPages := ctx.initialPages, limit := ctx.limit }

abbrev Context.floor (ctx : Context) := ctx.initialG0
abbrev Context.bookLimit (ctx : Context) := ctx.base.bookLimit
abbrev Context.tradeLimit (ctx : Context) := ctx.base.tradeLimit
abbrev Context.result (ctx : Context) := ctx.base.result
abbrev Context.fullFills (ctx : Context) := ctx.base.fullFills
abbrev Context.expectedG2 (ctx : Context) := ctx.base.expectedG2
abbrev Context.expectedG4 (ctx : Context) := ctx.base.expectedG4
abbrev Context.expectedG5 (ctx : Context) := ctx.base.expectedG5

structure RunningFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (tradesOwner : UInt64) : Prop where
  base : LoopInvariant.RunningFacts ctx.base st s data
  owner : s.get 16 = some (.i64 tradesOwner)
  floor48 : 48 ≤ ctx.floor.toNat
  heapMono : ctx.floor.toNat ≤ data.g0.toNat
  memoryBelow : MemoryBelow.BytesEqBelow ctx.base.initialMem st.mem ctx.floor.toNat
  nodesAbove : ∀ node ∈ data.nodes, ctx.floor.toNat + 48 ≤ node.root.toNat
  trackedAbove : data.oldTradesTracker ≠ 0 → ctx.floor.toNat + 48 ≤ data.trades.toNat

def RunningAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data owner, RunningFacts ctx st s data owner

structure CompletedFacts (ctx : Context) (st : Store Unit) (s : Locals)
    (data : CompletedData) (bookOwner tradesOwner : UInt64) : Prop where
  base : LoopInvariant.CompletedFacts ctx.base st s data
  bookOwner : s.get 73 = some (.i64 bookOwner)
  tradesOwner : s.get 75 = some (.i64 tradesOwner)
  heapMono : ctx.floor.toNat ≤ data.g0.toNat
  memoryBelow : MemoryBelow.BytesEqBelow ctx.base.initialMem st.mem ctx.floor.toNat
  nodesAbove : ∀ node ∈ data.nodes, ctx.floor.toNat + 48 ≤ node.root.toNat

def CompletedAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  ∃ data bookOwner tradesOwner, CompletedFacts ctx st s data bookOwner tradesOwner

def Invariant (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  RunningAt ctx st s ∨ CompletedAt ctx st s

def ExitAt (ctx : Context) (st : Store Unit) (s : Locals) : Prop :=
  CompletedAt ctx st s ∨ ∃ data owner, RunningFacts ctx st s data owner ∧ data.fuel = 0

theorem RunningAt.values (h : RunningAt ctx st s) : s.values = [] := by
  obtain ⟨data, owner, facts⟩ := h
  exact facts.base.locals.2.2.1

theorem CompletedAt.values (h : CompletedAt ctx st s) : s.values = [] := by
  obtain ⟨data, bookOwner, tradesOwner, facts⟩ := h
  exact LoopInvariant.CompletedAt.values ⟨data, facts.base⟩

theorem Invariant.values (h : Invariant ctx st s) : s.values = [] :=
  h.elim RunningAt.values CompletedAt.values

theorem ExitAt.values (h : ExitAt ctx st s) : s.values = [] := by
  rcases h with hDone | ⟨data, owner, facts, _⟩
  · exact hDone.values
  · exact facts.base.locals.2.2.1

end Project.ClobLimit.MatchInvariant
