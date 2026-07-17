import Project.ClobLimit.InternalInitialization

/-!
# Internal matcher entry frame

Function 17 first clears its completion flag, executes the verified loop, and
returns the loop result.  This module identifies that complete decomposition
and the initial running local frame.  The finite-list calculations remain
separate from the final termination theorem.
-/

namespace Project.ClobLimit.InternalEntry

open Wasm Project.ClobLimit Project.ClobLimit.InternalLoopInvariant

def entryFrame (ctx : Context)
    (bookOwner book tradesOwner trades : UInt64) : Locals :=
  func17Def.toLocals
    [.i64 ctx.initialFuel, .i64 ctx.taker.oid, .i64 ctx.taker.otrader,
      .i64 ctx.taker.oside, .i64 ctx.taker.oprice, .i64 ctx.taker.oqty,
      .i64 bookOwner, .i64 book, .i64 tradesOwner, .i64 trades,
      .i64 ctx.initialState.remaining]

set_option maxRecDepth 1048576 in
theorem func17_decomposition :
    func17 = InternalInitialization.initProg ++ InternalLoop.loopProg ++
      InternalLoopControl.resultEpilogueProg := by
  unfold func17 InternalInitialization.initProg InternalLoop.loopProg
    InternalLoop.bodyProg InternalLoopControl.loopGuardProg
    InternalIteration.dispatchProg InternalIteration.completeProg
    InternalLoopControl.resultEpilogueProg
  simp only [List.cons_append, List.nil_append]
  rfl

set_option Elab.async false in
theorem initialized_loop_locals (ctx : Context)
    (bookOwner book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64) :
    LoopLocalsAt ctx
      (InternalLoopInitial.initialData ctx bookOwner book bookCapacity
        tradesOwner trades tradesCapacity g0)
      (InternalInitialization.initFrame
        (entryFrame ctx bookOwner book tradesOwner trades)) := by
  simp (config := { maxSteps := 1000000 })
    [LoopLocalsAt, InternalLoopInitial.initialData,
      InternalInitialization.initFrame, entryFrame, func17Def,
      Function.toLocals, InternalIteration.AllocScratchAt, Locals.get]
  exact ⟨0, rfl⟩

end Project.ClobLimit.InternalEntry
