import Project.ClobLimit.MatchProgram

namespace Project.ClobLimit.MatchFinish
open Wasm

def resultFrame (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Locals :=
  { base with values := [.i64 remaining, .i64 trades, .i64 tradesOwner,
      .i64 book, .i64 bookOwner] }

def runningFrame (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Locals :=
  { base with
    locals := ((((base.locals.set 2 (.i64 bookOwner)).set 3 (.i64 book)).set 4
      (.i64 tradesOwner)).set 5 (.i64 trades)).set 6 (.i64 remaining)
    values := [.i64 remaining, .i64 trades, .i64 tradesOwner,
      .i64 book, .i64 bookOwner] }

set_option Elab.async false in
theorem completed_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64)
    (hValues : base.values = [])
    (hBookOwner : base.get 13 = some (.i64 bookOwner))
    (hBook : base.get 14 = some (.i64 book))
    (hTradesOwner : base.get 15 = some (.i64 tradesOwner))
    (hTrades : base.get 16 = some (.i64 trades))
    (hRemaining : base.get 17 = some (.i64 remaining))
    (hComplete : base.get 18 = some (.i64 1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (resultFrame base bookOwner book tradesOwner trades remaining) env) :
    wp «module» (MatchProgram.finish ++ rest) Q st base env := by
  simp only [Locals.get] at hBookOwner hBook hTradesOwner hTrades hRemaining hComplete
  unfold MatchProgram.finish
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hComplete]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  norm_num
  rw [hBookOwner]
  wp_run
  rw [hBook]
  wp_run
  rw [hTradesOwner]
  wp_run
  rw [hTrades]
  wp_run
  rw [hRemaining]
  wp_run
  simpa [resultFrame, hValues] using hDone

set_option Elab.async false in
theorem running_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64)
    (hParams : base.params.length = 11) (hLocals : base.locals.length = 78)
    (hValues : base.values = [])
    (hBookOwner : base.get 6 = some (.i64 bookOwner))
    (hBook : base.get 7 = some (.i64 book))
    (hTradesOwner : base.get 8 = some (.i64 tradesOwner))
    (hTrades : base.get 9 = some (.i64 trades))
    (hRemaining : base.get 10 = some (.i64 remaining))
    (hRunning : base.get 18 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (runningFrame base bookOwner book tradesOwner trades remaining) env) :
    wp «module» (MatchProgram.finish ++ rest) Q st base env := by
  simp only [Locals.get] at hBookOwner hBook hTradesOwner hTrades hRemaining hRunning
  have hBookOwner' : base.params[6] = .i64 bookOwner := by
    simpa [hParams, hLocals] using hBookOwner
  have hBook' : base.params[7] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hTradesOwner' : base.params[8] = .i64 tradesOwner := by
    simpa [hParams, hLocals] using hTradesOwner
  have hTrades' : base.params[9] = .i64 trades := by
    simpa [hParams, hLocals] using hTrades
  have hRemaining' : base.params[10] = .i64 remaining := by
    simpa [hParams, hLocals] using hRemaining
  unfold MatchProgram.finish
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hRunning]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  norm_num
  simp (config := { maxSteps := 1000000 }) [wp_simp, hParams, hLocals,
    hValues, hBookOwner', hBook', hTradesOwner', hTrades', hRemaining']
  simpa only [runningFrame] using hDone

#print axioms completed_spec
#print axioms running_spec
end Project.ClobLimit.MatchFinish
