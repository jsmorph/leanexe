import Project.ClobMatchFuel.PartialTradeUpdate

/-!
# Match-loop control

The outer matching loop checks fuel and its done flag before each iteration.
After the loop, its epilogue selects either the carried state or the completed
result and places the three public results on the value stack.
-/

namespace Project.ClobMatchFuel.LoopControl

open Wasm Project.ClobMatchFuel

def loopGuardProg : Wasm.Program :=
  [
  .localGet 0,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 24,
    .constI64 0,
    .eqI64
  ] [
    .const 0
  ],
  .eqz,
  .br_if 1
  ]

def resultEpilogueProg : Wasm.Program :=
  [
  .localGet 24,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .localGet 15,
    .localSet 21,
    .localGet 17,
    .localSet 22,
    .localGet 18,
    .localSet 23
  ] [],
  .localGet 21,
  .localGet 22,
  .localGet 23
  ]

def resultFrame (base : Locals) (book trades remaining : UInt64) : Locals :=
  { base with values := [.i64 remaining, .i64 trades, .i64 book] }

def runningResultFrame (base : Locals) (book trades remaining : UInt64) :
    Locals :=
  { base with
    locals := ((base.locals.set 12 (.i64 book)).set 13 (.i64 trades)).set 14
      (.i64 remaining)
    values := [.i64 remaining, .i64 trades, .i64 book] }

def CompletedResultAt (base : Locals) (book trades remaining : UInt64) : Prop :=
  base.locals[12]? = some (.i64 book) ∧
  base.locals[13]? = some (.i64 trades) ∧
  base.locals[14]? = some (.i64 remaining) ∧
  base.locals[15]? = some (.i64 1) ∧
  base.params.length = 9 ∧ base.locals.length = 76 ∧ base.values = []

set_option Elab.async false in
theorem loopGuard_done_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (fuel : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hDone : base.get 24 = some (.i64 1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hBreak : Q (.Break 1 st base)) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  simp only [Locals.get] at hFuel hDone
  have hBase : { base with values := [] } = base := by
    cases base
    simp_all
  unfold loopGuardProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hFuel]
  wp_run
  refine wp_iff_cons rfl ?_
  by_cases hFuelZero : fuel = 0
  · subst fuel
    rw [if_neg (by simp)]
    norm_num
    simpa [wp_simp, hValues, hBase] using hBreak
  · rw [if_pos (by simp [hFuelZero])]
    norm_num
    rw [hDone]
    norm_num
    simpa [wp_simp, hValues, hBase] using hBreak

set_option Elab.async false in
theorem loopGuard_zero_fuel_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hBreak : Q (.Break 1 st base)) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  simp only [Locals.get] at hFuel
  have hBase : { base with values := [] } = base := by
    cases base
    simp_all
  unfold loopGuardProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hFuel]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  norm_num
  simpa [wp_simp, hValues, hBase] using hBreak

set_option Elab.async false in
theorem loopGuard_running_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (fuel : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hFuelNonzero : fuel ≠ 0)
    (hDone : base.get 24 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hRest : wp «module» rest Q st base env) :
    wp «module» (loopGuardProg ++ rest) Q st base env := by
  simp only [Locals.get] at hFuel hDone
  have hBase : { base with values := [] } = base := by
    cases base
    simp_all
  unfold loopGuardProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hFuel]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hFuelNonzero])]
  norm_num
  rw [hDone]
  norm_num
  simpa [wp_simp, hValues, hBase] using hRest

set_option Elab.async false in
theorem resultEpilogue_completed_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades remaining : UInt64)
    (hResult : CompletedResultAt base book trades remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (resultFrame base book trades remaining) env) :
    wp «module» (resultEpilogueProg ++ rest) Q st base env := by
  rcases hResult with
    ⟨hBook, hTrades, hRemaining, hComplete, hParams, hLocals, hValues⟩
  have hBook' : base.locals[12] = .i64 book :=
    (List.getElem?_eq_some_iff.mp hBook).2
  have hTrades' : base.locals[13] = .i64 trades :=
    (List.getElem?_eq_some_iff.mp hTrades).2
  have hRemaining' : base.locals[14] = .i64 remaining :=
    (List.getElem?_eq_some_iff.mp hRemaining).2
  have hComplete' : base.locals[15] = .i64 1 :=
    (List.getElem?_eq_some_iff.mp hComplete).2
  have hBookGet : base.get 21 = some (.i64 book) := by
    simp [Locals.get, hParams, hLocals, hBook']
  have hTradesGet : base.get 22 = some (.i64 trades) := by
    simp [Locals.get, hParams, hLocals, hTrades']
  have hRemainingGet : base.get 23 = some (.i64 remaining) := by
    simp [Locals.get, hParams, hLocals, hRemaining']
  have hCompleteGet : base.get 24 = some (.i64 1) := by
    simp [Locals.get, hParams, hLocals, hComplete']
  simp only [Locals.get] at hBookGet hTradesGet hRemainingGet hCompleteGet
  unfold resultEpilogueProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hCompleteGet]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  norm_num
  rw [hBookGet]
  wp_run
  rw [hTradesGet]
  wp_run
  rw [hRemainingGet]
  wp_run
  simpa [resultFrame, hValues] using hDone

set_option Elab.async false in
theorem resultEpilogue_done_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades : UInt64)
    (hResult : PartialTradeUpdate.PartialResultAt base book trades)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st (resultFrame base book trades 0) env) :
    wp «module» (resultEpilogueProg ++ rest) Q st base env := by
  apply resultEpilogue_completed_spec env st base book trades 0
  · simpa [CompletedResultAt, PartialTradeUpdate.PartialResultAt] using
      hResult
  · exact hDone

set_option Elab.async false in
theorem resultEpilogue_running_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades remaining : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hBook : base.get 15 = some (.i64 book))
    (hTrades : base.get 17 = some (.i64 trades))
    (hRemaining : base.get 18 = some (.i64 remaining))
    (hRunning : base.get 24 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (runningResultFrame base book trades remaining) env) :
    wp «module» (resultEpilogueProg ++ rest) Q st base env := by
  simp only [Locals.get] at hBook hTrades hRemaining hRunning
  have hBook' : base.locals[6] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hTrades' : base.locals[8] = .i64 trades := by
    simpa [hParams, hLocals] using hTrades
  have hRemaining' : base.locals[9] = .i64 remaining := by
    simpa [hParams, hLocals] using hRemaining
  have hRunning' : base.locals[15] = .i64 0 := by
    simpa [hParams, hLocals] using hRunning
  unfold resultEpilogueProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hRunning]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  norm_num
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hBook', hTrades', hRemaining']
  simpa only [runningResultFrame] using hDone

end Project.ClobMatchFuel.LoopControl
