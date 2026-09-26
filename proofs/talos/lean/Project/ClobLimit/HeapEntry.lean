import Project.ClobLimit.HeapResult

namespace Project.ClobLimit.HeapEntry
open Wasm Project.Clob Project.Runtime Project.LocalRegion Project.ClobLimit.HeapProgram
open Project.ClobMatchFuel.LoopInvariant
set_option maxRecDepth 1048576

def args (ctx : Context) (book tradesOwner trades : UInt64) : List Value :=
  [.i64 ctx.initialState.remaining, .i64 trades, .i64 tradesOwner, .i64 book, .i64 0,
   .i64 ctx.taker.oqty, .i64 ctx.taker.oprice, .i64 ctx.taker.oside,
   .i64 ctx.taker.otrader, .i64 ctx.taker.oid, .i64 ctx.initialFuel]

def entryFrame (ctx : Context) (book tradesOwner trades : UInt64) : Locals :=
  func17Def.toLocals (args ctx book tradesOwner trades).reverse

def sourceFrame (ctx : Context) (book tradesOwner trades : UInt64) : Locals :=
  layout.sourceFrame (entryFrame ctx book tradesOwner trades)

theorem related (ctx : Context) (book tradesOwner trades : UInt64) :
    layout.Related (sourceFrame ctx book tradesOwner trades)
      (entryFrame ctx book tradesOwner trades) :=
  layout.sourceFrame_related _ rfl rfl

theorem source_locals (ctx : Context) (book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64)
    (nodes : List FreeNode) :
    LoopLocalsAt ctx
      (Project.ClobMatchFuel.LoopInitial.initialData ctx book bookCapacity trades tradesCapacity g0 nodes)
      (sourceFrame ctx book tradesOwner trades) := by
  repeat' apply And.intro
  all_goals first | rfl | exact ⟨0, 0, 0, 0, rfl, rfl, rfl, rfl⟩

set_option Elab.async false in
theorem init_spec (env : HostEnv Unit) (st : Store Unit) (ctx : Context)
    (book tradesOwner trades : UInt64) (Q : Assertion Unit) (rest : Program)
    (hNext : wp Project.ClobLimit.«module» rest Q st (entryFrame ctx book tradesOwner trades) env) :
    wp Project.ClobLimit.«module» (initProg ++ rest) Q st
      (entryFrame ctx book tradesOwner trades) env := by
  simpa [initProg, entryFrame, args, func17Def, Function.toLocals, ValueType.zero, wp_simp] using hNext

#print axioms source_locals
#print axioms init_spec
end Project.ClobLimit.HeapEntry
