import Project.ClobMatchFuel.LoopResult

/-!
# Match export entry frame

The generated export first copies its public parameters into the recursive
local layout.  This module identifies the complete body decomposition and the
resulting initial loop frame.  Keeping these finite-list reductions separate
prevents the public theorem from expanding the generated dispatcher.
-/

namespace Project.ClobMatchFuel.Entry

open Wasm Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.LoopInvariant

def entryFrame (ctx : Context) (book trades : UInt64) : Locals :=
  func14Def.toLocals
    [.i64 ctx.initialFuel, .i64 ctx.taker.oid, .i64 ctx.taker.otrader,
     .i64 ctx.taker.oside, .i64 ctx.taker.oprice, .i64 ctx.taker.oqty,
     .i64 book, .i64 trades, .i64 ctx.initialState.remaining]

set_option maxRecDepth 1048576 in
theorem func14_decomposition :
    func14 = Initialization.initProg ++ Loop.loopProg ++
      LoopControl.resultEpilogueProg := by
  unfold func14 Initialization.initProg Loop.loopProg Loop.bodyProg
    LoopControl.loopGuardProg Iteration.dispatchProg Iteration.completeProg
    LoopControl.resultEpilogueProg
  simp only [List.cons_append, List.nil_append]
  rfl

set_option Elab.async false in
theorem initialized_loop_locals (ctx : Context)
    (book bookCapacity trades tradesCapacity g0 : UInt64)
    (nodes : List Project.Runtime.FreeNode) :
    LoopLocalsAt ctx
      (LoopInitial.initialData ctx book bookCapacity trades tradesCapacity g0
        nodes)
      (Initialization.initFrame (entryFrame ctx book trades) ctx.taker book
        trades ctx.initialState.remaining) := by
  simp (config := { maxSteps := 1000000 })
    [LoopLocalsAt, LoopInitial.initialData, Initialization.initFrame,
      Initialization.initLocals, entryFrame, func14Def, Function.toLocals,
      FullTradeUpdate.AllocScratchAt]
  exact ⟨0, rfl⟩

end Project.ClobMatchFuel.Entry
