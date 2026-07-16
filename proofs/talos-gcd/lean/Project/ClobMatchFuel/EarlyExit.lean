import Project.ClobMatchFuel.FindBestWrapper
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Early exits from `matchFuel`

The generated outer loop returns its current state when fuel is exhausted,
remaining quantity is zero, or the embedded search returns no maker.  These
branches preserve the complete store because they perform no allocation.
-/

namespace Project.ClobMatchFuel.EarlyExit

open Wasm Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

theorem func14_zero_fuel (env : HostEnv Unit) (st : Store Unit)
    (book trades : UInt64) (taker : OrderL) (remaining : UInt64) :
    TerminatesWith (m := «module») (id := 14) (initial := st) (env := env)
      [.i64 remaining, .i64 trades, .i64 book, .i64 taker.oqty,
       .i64 taker.oprice, .i64 taker.oside, .i64 taker.otrader,
       .i64 taker.oid, .i64 0]
      (fun st' vs =>
        vs = [.i64 remaining, .i64 trades, .i64 book] ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func14Def)
  · simp [«module»]
  · change wp «module» func14 _ st
      (func14Def.toLocals
        [.i64 0, .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
         .i64 taker.oprice, .i64 taker.oqty, .i64 book, .i64 trades,
         .i64 remaining]) env
    unfold func14
    wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st' s =>
        st' = st ∧
        s.get 0 = some (.i64 0) ∧
        s.get 15 = some (.i64 book) ∧
        s.get 17 = some (.i64 trades) ∧
        s.get 18 = some (.i64 remaining) ∧
        s.get 24 = some (.i64 0) ∧
        s.params.length = 9 ∧
        s.locals.length = 76)
      (μ := fun _ _ => 0)
    · simp [func14Def]
    · rintro st' s
        ⟨rfl, hFuel, hBook, hTrades, hRemaining, hDone, hParams, hLocals⟩
      simp only [Locals.get] at hFuel hBook hTrades hRemaining hDone
      have hBook' : s.locals[6] = .i64 book := by
        simpa [hParams, hLocals] using hBook
      have hTrades' : s.locals[8] = .i64 trades := by
        simpa [hParams, hLocals] using hTrades
      have hRemaining' : s.locals[9] = .i64 remaining := by
        simpa [hParams, hLocals] using hRemaining
      wp_run
      rw [hFuel]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      norm_num
      rw [hDone]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      norm_num
      simp [hBook', hTrades', hRemaining', hParams, hLocals, func14Def]

private def stopInv (st0 : Store Unit) (fuel book trades remaining : UInt64) :
    AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    s.get 0 = some (.i64 fuel) ∧
    s.get 15 = some (.i64 book) ∧
    s.get 17 = some (.i64 trades) ∧
    s.get 18 = some (.i64 remaining) ∧
    ((s.get 24 = some (.i64 0)) ∨
      (s.get 24 = some (.i64 1) ∧
        s.get 21 = some (.i64 book) ∧
        s.get 22 = some (.i64 trades) ∧
        s.get 23 = some (.i64 remaining))) ∧
    s.params.length = 9 ∧
    s.locals.length = 76

private def stopMeasure (_ : Store Unit) (s : Locals) : Nat :=
  if s.get 24 = some (.i64 0) then 1 else 0

theorem func14_zero_remaining (env : HostEnv Unit) (st : Store Unit)
    (fuel book trades : UInt64) (taker : OrderL) (hFuel : fuel ≠ 0) :
    TerminatesWith (m := «module») (id := 14) (initial := st) (env := env)
      [.i64 0, .i64 trades, .i64 book, .i64 taker.oqty,
       .i64 taker.oprice, .i64 taker.oside, .i64 taker.otrader,
       .i64 taker.oid, .i64 fuel]
      (fun st' vs => vs = [.i64 0, .i64 trades, .i64 book] ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func14Def)
  · simp [«module»]
  · change wp «module» func14 _ st
      (func14Def.toLocals
        [.i64 fuel, .i64 taker.oid, .i64 taker.otrader,
         .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty,
         .i64 book, .i64 trades, .i64 0]) env
    unfold func14
    wp_run
    apply wp_block_cons
    apply wp_loop_cons (Inv := stopInv st fuel book trades 0)
      (μ := stopMeasure)
    · unfold stopInv
      simp [func14Def]
    · rintro st' s hState
      unfold stopInv at hState
      rcases hState with
        ⟨rfl, hFuelLocal, hBook, hTrades, hRemaining, hPhase,
          hParams, hLocals⟩
      simp only [Locals.get] at hFuelLocal hBook hTrades hRemaining
      rcases hPhase with hRunning | ⟨hDone, hResult⟩
      · simp only [Locals.get] at hRunning
        have hFuelLocal' : s.params[0] = .i64 fuel := by
          simpa [hParams, hLocals] using hFuelLocal
        have hBook' : s.locals[6] = .i64 book := by
          simpa [hParams, hLocals] using hBook
        have hTrades' : s.locals[8] = .i64 trades := by
          simpa [hParams, hLocals] using hTrades
        have hRemaining' : s.locals[9] = .i64 0 := by
          simpa [hParams, hLocals] using hRemaining
        have hRunning' : s.locals[15] = .i64 0 := by
          simpa [hParams, hLocals] using hRunning
        wp_run
        rw [hFuelLocal]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hFuel])]
        norm_num
        rw [hRunning]
        wp_run
        norm_num
        rw [hRemaining]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        norm_num
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        norm_num
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        norm_num
        simp [stopInv, stopMeasure, hFuelLocal', hBook', hTrades',
          hRemaining', hRunning', hParams, hLocals]
      · rcases hResult with ⟨hBookResult, hTradesResult, hRemainingResult⟩
        simp only [Locals.get] at hDone hBookResult hTradesResult hRemainingResult
        have hBookResult' : s.locals[12] = .i64 book := by
          simpa [hParams, hLocals] using hBookResult
        have hTradesResult' : s.locals[13] = .i64 trades := by
          simpa [hParams, hLocals] using hTradesResult
        have hRemainingResult' : s.locals[14] = .i64 0 := by
          simpa [hParams, hLocals] using hRemainingResult
        wp_run
        rw [hFuelLocal]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hFuel])]
        norm_num
        rw [hDone]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        norm_num
        simp [hBookResult', hTradesResult', hRemainingResult', hParams,
          hLocals, func14Def]

end Project.ClobMatchFuel.EarlyExit
