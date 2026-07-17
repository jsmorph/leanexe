import Project.ClobLimit.FindBestWrapper
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Early exits from the internal matcher

The internal matcher returns owner-and-pointer pairs for its book and trade
arrays.  Fuel exhaustion and zero remaining quantity preserve those five
carried values and the complete store.
-/

namespace Project.ClobLimit.InternalEarlyExit

open Wasm Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def internalArgs (fuel : UInt64) (taker : OrderL)
    (bookOwner book tradesOwner trades remaining : UInt64) : List Value :=
  [.i64 remaining, .i64 trades, .i64 tradesOwner, .i64 book, .i64 bookOwner,
   .i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
   .i64 taker.otrader, .i64 taker.oid, .i64 fuel]

def internalResults (bookOwner book tradesOwner trades remaining : UInt64) :
    List Value :=
  [.i64 remaining, .i64 trades, .i64 tradesOwner, .i64 book, .i64 bookOwner]

theorem func17_zero_fuel (env : HostEnv Unit) (st : Store Unit)
    (bookOwner book tradesOwner trades remaining : UInt64) (taker : OrderL) :
    TerminatesWith (m := «module») (id := 17) (initial := st) (env := env)
      (internalArgs 0 taker bookOwner book tradesOwner trades remaining)
      (fun st' values =>
        values = internalResults bookOwner book tradesOwner trades remaining ∧
        st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [«module»]
  · change wp «module» func17 _ st
      (func17Def.toLocals
        [.i64 0, .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
         .i64 taker.oprice, .i64 taker.oqty, .i64 bookOwner, .i64 book,
         .i64 tradesOwner, .i64 trades, .i64 remaining]) env
    unfold func17
    wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st' s =>
        st' = st ∧
        s.get 0 = some (.i64 0) ∧
        s.get 6 = some (.i64 bookOwner) ∧
        s.get 7 = some (.i64 book) ∧
        s.get 8 = some (.i64 tradesOwner) ∧
        s.get 9 = some (.i64 trades) ∧
        s.get 10 = some (.i64 remaining) ∧
        s.get 16 = some (.i64 0) ∧
        s.params.length = 11 ∧ s.locals.length = 64)
      (μ := fun _ _ => 0)
    · simp [func17Def]
    · rintro st' s
        ⟨rfl, hFuel, hBookOwner, hBook, hTradesOwner, hTrades, hRemaining,
          hDone, hParams, hLocals⟩
      have hBookOwner' : s.params[6] = .i64 bookOwner := by
        simpa [Locals.get, hParams, hLocals] using hBookOwner
      have hBook' : s.params[7] = .i64 book := by
        simpa [Locals.get, hParams, hLocals] using hBook
      have hTradesOwner' : s.params[8] = .i64 tradesOwner := by
        simpa [Locals.get, hParams, hLocals] using hTradesOwner
      have hTrades' : s.params[9] = .i64 trades := by
        simpa [Locals.get, hParams, hLocals] using hTrades
      have hRemaining' : s.params[10] = .i64 remaining := by
        simpa [Locals.get, hParams, hLocals] using hRemaining
      simp only [Locals.get] at hFuel hDone
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
      simp [hBookOwner', hBook', hTradesOwner', hTrades', hRemaining',
        hParams, hLocals, func17Def, internalArgs, internalResults]

private def stopInv (st0 : Store Unit) (fuel : UInt64)
    (bookOwner book tradesOwner trades remaining : UInt64) : AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    s.get 0 = some (.i64 fuel) ∧
    s.get 6 = some (.i64 bookOwner) ∧
    s.get 7 = some (.i64 book) ∧
    s.get 8 = some (.i64 tradesOwner) ∧
    s.get 9 = some (.i64 trades) ∧
    s.get 10 = some (.i64 remaining) ∧
    (s.get 16 = some (.i64 0) ∨
      (s.get 16 = some (.i64 1) ∧
        s.get 11 = some (.i64 bookOwner) ∧
        s.get 12 = some (.i64 book) ∧
        s.get 13 = some (.i64 tradesOwner) ∧
        s.get 14 = some (.i64 trades) ∧
        s.get 15 = some (.i64 remaining))) ∧
    s.params.length = 11 ∧ s.locals.length = 64 ∧ s.values = []

private def stopMeasure (_ : Store Unit) (s : Locals) : Nat :=
  if s.get 16 = some (.i64 0) then 1 else 0

theorem func17_zero_remaining (env : HostEnv Unit) (st : Store Unit)
    (fuel bookOwner book tradesOwner trades : UInt64) (taker : OrderL)
    (hFuel : fuel ≠ 0) :
    TerminatesWith (m := «module») (id := 17) (initial := st) (env := env)
      (internalArgs fuel taker bookOwner book tradesOwner trades 0)
      (fun st' values =>
        values = internalResults bookOwner book tradesOwner trades 0 ∧
        st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [«module»]
  · change wp «module» func17 _ st
      (func17Def.toLocals
        [.i64 fuel, .i64 taker.oid, .i64 taker.otrader,
         .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty,
         .i64 bookOwner, .i64 book, .i64 tradesOwner, .i64 trades,
         .i64 0]) env
    unfold func17
    wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := stopInv st fuel bookOwner book tradesOwner trades 0)
      (μ := stopMeasure)
    · unfold stopInv
      simp [func17Def]
    · rintro st' s hState
      unfold stopInv at hState
      rcases hState with
        ⟨rfl, hFuelLocal, hBookOwner, hBook, hTradesOwner, hTrades,
          hRemaining, hPhase, hParams, hLocals, hValues⟩
      have hFuelLocal' : s.params[0] = .i64 fuel := by
        simpa [Locals.get, hParams, hLocals] using hFuelLocal
      have hBookOwner' : s.params[6] = .i64 bookOwner := by
        simpa [Locals.get, hParams, hLocals] using hBookOwner
      have hBook' : s.params[7] = .i64 book := by
        simpa [Locals.get, hParams, hLocals] using hBook
      have hTradesOwner' : s.params[8] = .i64 tradesOwner := by
        simpa [Locals.get, hParams, hLocals] using hTradesOwner
      have hTrades' : s.params[9] = .i64 trades := by
        simpa [Locals.get, hParams, hLocals] using hTrades
      have hRemaining' : s.params[10] = .i64 0 := by
        simpa [Locals.get, hParams, hLocals] using hRemaining
      simp only [Locals.get] at hFuelLocal hRemaining
      rcases hPhase with hRunning | ⟨hDone, hResult⟩
      ·
        have hRunning' : s.locals[5] = .i64 0 := by
          simpa [Locals.get, hParams, hLocals] using hRunning
        simp only [Locals.get] at hRunning
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
        simp [stopInv, stopMeasure, hFuelLocal', hBookOwner', hBook',
          hTradesOwner', hTrades', hRemaining', hRunning', hParams, hLocals,
          hValues]
      · rcases hResult with
          ⟨hBookOwnerResult, hBookResult, hTradesOwnerResult,
            hTradesResult, hRemainingResult⟩
        have hBookOwnerResult' : s.locals[0] = .i64 bookOwner := by
          simpa [Locals.get, hParams, hLocals] using hBookOwnerResult
        have hBookResult' : s.locals[1] = .i64 book := by
          simpa [Locals.get, hParams, hLocals] using hBookResult
        have hTradesOwnerResult' : s.locals[2] = .i64 tradesOwner := by
          simpa [Locals.get, hParams, hLocals] using hTradesOwnerResult
        have hTradesResult' : s.locals[3] = .i64 trades := by
          simpa [Locals.get, hParams, hLocals] using hTradesResult
        have hRemainingResult' : s.locals[4] = .i64 0 := by
          simpa [Locals.get, hParams, hLocals] using hRemainingResult
        simp only [Locals.get] at hDone
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
        simp [hBookOwnerResult', hBookResult', hTradesOwnerResult',
          hTradesResult', hRemainingResult', hParams, hLocals, func17Def,
          internalArgs, internalResults]

end Project.ClobLimit.InternalEarlyExit
