import Project.ClobLimit.MatchTargetLoop
import Project.ClobMatchFuel.LoopInitial

namespace Project.ClobLimit.MatchEntry
open Wasm Project.Clob Project.ClobLimit.MatchInvariant

def internalArgs (fuel : UInt64) (taker : OrderL)
    (bookOwner book tradesOwner trades remaining : UInt64) : List Value :=
  [.i64 remaining, .i64 trades, .i64 tradesOwner, .i64 book,
    .i64 bookOwner, .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
    .i64 taker.otrader, .i64 taker.oid, .i64 fuel]

def args (ctx : Context) (bookOwner book tradesOwner trades : UInt64) : List Value :=
  internalArgs ctx.initialFuel ctx.taker bookOwner book tradesOwner trades ctx.initialState.remaining

def entryFrame (ctx : Context) (bookOwner book tradesOwner trades : UInt64) : Locals :=
  func17Def.toLocals (args ctx bookOwner book tradesOwner trades).reverse

def sourceFrame (ctx : Context) (bookOwner book tradesOwner trades : UInt64) : Locals :=
  MatchLocals.mapping.pull (entryFrame ctx bookOwner book tradesOwner trades)

def initialData (ctx : Context) (bookOwner book bookCapacity trades tradesCapacity g0 : UInt64) :
    RunningData :=
  Project.ClobMatchFuel.LoopInitial.initialData ctx.base book bookCapacity trades
    tradesCapacity g0 [] bookOwner

theorem related (ctx : Context) (bookOwner book tradesOwner trades : UInt64) :
    MatchLocals.mapping.Related (sourceFrame ctx bookOwner book tradesOwner trades)
      (entryFrame ctx bookOwner book tradesOwner trades) :=
  MatchLocals.mapping.pull_related _ (by constructor <;> rfl)

set_option Elab.async false in
theorem initial_locals (ctx : Context)
    (bookOwner book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64) :
    Project.ClobMatchFuel.LoopInvariant.LoopLocalsAt ctx.base
      (initialData ctx bookOwner book bookCapacity trades tradesCapacity g0)
      (sourceFrame ctx bookOwner book tradesOwner trades) := by
  have hRelated := related ctx bookOwner book tradesOwner trades
  refine ⟨hRelated.1.1, hRelated.1.2, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hRelated.2.2.2 0 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 9 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 10 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 11 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 12 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 13 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 14 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 15 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 17 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 18 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 19 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 20 (by decide)).trans (by rfl)
  · exact (hRelated.2.2.2 24 (by decide)).trans (by rfl)
  · refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_⟩
    · have h := (hRelated.2.2.2 89 (by decide)).trans (show
          (entryFrame ctx bookOwner book tradesOwner trades).get (MatchLocals.rename 89) =
            some (.i64 0) from rfl)
      simpa [Locals.get, hRelated.1.1, hRelated.1.2, MatchLocals.mapping] using h
    · have h := (hRelated.2.2.2 90 (by decide)).trans (show
          (entryFrame ctx bookOwner book tradesOwner trades).get (MatchLocals.rename 90) =
            some (.i64 0) from rfl)
      simpa [Locals.get, hRelated.1.1, hRelated.1.2, MatchLocals.mapping] using h
    · have h := (hRelated.2.2.2 92 (by decide)).trans (show
          (entryFrame ctx bookOwner book tradesOwner trades).get (MatchLocals.rename 92) =
            some (.i64 0) from rfl)
      simpa [Locals.get, hRelated.1.1, hRelated.1.2, MatchLocals.mapping] using h
    · have h := (hRelated.2.2.2 93 (by decide)).trans (show
          (entryFrame ctx bookOwner book tradesOwner trades).get (MatchLocals.rename 93) =
            some (.i64 0) from rfl)
      simpa [Locals.get, hRelated.1.1, hRelated.1.2, MatchLocals.mapping] using h

theorem initial_owner (ctx : Context) (bookOwner book tradesOwner trades : UInt64) :
    (sourceFrame ctx bookOwner book tradesOwner trades).get 16 = some (.i64 tradesOwner) := by
  have h := (related ctx bookOwner book tradesOwner trades).2.2.2 16 (by decide)
  exact h.trans (by rfl)

set_option Elab.async false in
theorem init_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (bookOwner book tradesOwner trades : UInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (entryFrame ctx bookOwner book tradesOwner trades) env) :
    wp «module» (MatchProgram.initProg ++ rest) Q st
      (entryFrame ctx bookOwner book tradesOwner trades) env := by
  simpa [MatchProgram.initProg, wp_simp, entryFrame, args, internalArgs,
    func17Def, Function.toLocals, ValueType.zero]
    using hNext

#print axioms initial_locals
#print axioms init_spec
end Project.ClobLimit.MatchEntry
