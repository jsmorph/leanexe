import Project.ClobLimit.InternalFullBranch
import Project.ClobLimit.InternalIteration
import Project.ClobLimit.InternalPartialBranch

/-!
# Internal match-loop control

The generated loop guard exits after fuel reaches zero or a branch records a
completed result.  The result epilogue selects the recursive parameters for a
running exit and returns the five owner-and-pointer values.
-/

namespace Project.ClobLimit.InternalLoopControl

open Wasm Project.ClobLimit

def loopGuardProg : Wasm.Program :=
  [
  .localGet 0,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 16,
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
  .localGet 16,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .localGet 6,
    .localSet 11,
    .localGet 7,
    .localSet 12,
    .localGet 8,
    .localSet 13,
    .localGet 9,
    .localSet 14,
    .localGet 10,
    .localSet 15
  ] [],
  .localGet 11,
  .localGet 12,
  .localGet 13,
  .localGet 14,
  .localGet 15
  ]

def resultFrame (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Locals :=
  { base with values := [.i64 remaining, .i64 trades, .i64 tradesOwner,
      .i64 book, .i64 bookOwner] }

def runningResultFrame (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64) : Locals :=
  { base with
    locals := ((((base.locals.set 0 (.i64 bookOwner)).set 1
      (.i64 book)).set 2 (.i64 tradesOwner)).set 3 (.i64 trades)).set 4
        (.i64 remaining)
    values := [.i64 remaining, .i64 trades, .i64 tradesOwner,
      .i64 book, .i64 bookOwner] }

set_option Elab.async false in
theorem loopGuard_done_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (fuel : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hDone : base.get 16 = some (.i64 1))
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
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
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
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hFuelNonzero : fuel ≠ 0)
    (hDone : base.get 16 = some (.i64 0))
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
    (bookOwner book tradesOwner trades remaining : UInt64)
    (hResult : InternalIteration.CompletedResultAt base bookOwner book
      tradesOwner trades remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (resultFrame base bookOwner book tradesOwner trades remaining) env) :
    wp «module» (resultEpilogueProg ++ rest) Q st base env := by
  rcases hResult with
    ⟨hBookOwner, hBook, hTradesOwner, hTrades, hRemaining, hComplete, hParams,
      hLocals, hValues⟩
  have hBookOwner' : base.locals[0] = .i64 bookOwner :=
    (List.getElem?_eq_some_iff.mp hBookOwner).2
  have hBook' : base.locals[1] = .i64 book :=
    (List.getElem?_eq_some_iff.mp hBook).2
  have hTradesOwner' : base.locals[2] = .i64 tradesOwner :=
    (List.getElem?_eq_some_iff.mp hTradesOwner).2
  have hTrades' : base.locals[3] = .i64 trades :=
    (List.getElem?_eq_some_iff.mp hTrades).2
  have hRemaining' : base.locals[4] = .i64 remaining :=
    (List.getElem?_eq_some_iff.mp hRemaining).2
  have hComplete' : base.locals[5] = .i64 1 :=
    (List.getElem?_eq_some_iff.mp hComplete).2
  have hBookOwnerGet : base.get 11 = some (.i64 bookOwner) := by
    simp [Locals.get, hParams, hLocals, hBookOwner']
  have hBookGet : base.get 12 = some (.i64 book) := by
    simp [Locals.get, hParams, hLocals, hBook']
  have hTradesOwnerGet : base.get 13 = some (.i64 tradesOwner) := by
    simp [Locals.get, hParams, hLocals, hTradesOwner']
  have hTradesGet : base.get 14 = some (.i64 trades) := by
    simp [Locals.get, hParams, hLocals, hTrades']
  have hRemainingGet : base.get 15 = some (.i64 remaining) := by
    simp [Locals.get, hParams, hLocals, hRemaining']
  have hCompleteGet : base.get 16 = some (.i64 1) := by
    simp [Locals.get, hParams, hLocals, hComplete']
  simp only [Locals.get] at hBookOwnerGet hBookGet hTradesOwnerGet hTradesGet hRemainingGet hCompleteGet
  unfold resultEpilogueProg
  simp only [List.cons_append, List.nil_append]
  wp_run
  rw [hCompleteGet]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  norm_num
  rw [hBookOwnerGet]
  wp_run
  rw [hBookGet]
  wp_run
  rw [hTradesOwnerGet]
  wp_run
  rw [hTradesGet]
  wp_run
  rw [hRemainingGet]
  wp_run
  simpa [resultFrame, hValues] using hDone

set_option Elab.async false in
theorem resultEpilogue_running_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (bookOwner book tradesOwner trades remaining : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hBookOwner : base.get 6 = some (.i64 bookOwner))
    (hBook : base.get 7 = some (.i64 book))
    (hTradesOwner : base.get 8 = some (.i64 tradesOwner))
    (hTrades : base.get 9 = some (.i64 trades))
    (hRemaining : base.get 10 = some (.i64 remaining))
    (hRunning : base.get 16 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (runningResultFrame base bookOwner book tradesOwner trades remaining) env) :
    wp «module» (resultEpilogueProg ++ rest) Q st base env := by
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
  have hRunning' : base.locals[5] = .i64 0 := by
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
    hValues, hBookOwner', hBook', hTradesOwner', hTrades', hRemaining']
  simpa only [runningResultFrame] using hDone

end Project.ClobLimit.InternalLoopControl
