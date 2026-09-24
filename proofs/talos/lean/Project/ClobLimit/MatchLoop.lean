import Project.ClobLimit.MatchIteration
import Project.ClobLimit.MatchProgram
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobLimit.MatchLoop

open Wasm Project.ClobMatchFuel Project.ClobLimit.MatchInvariant

private abbrev sourceModule := Project.ClobMatchFuel.«module»

set_option Elab.async false in
theorem sourceLoop_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (hInvariant : Invariant ctx st base)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, ExitAt ctx st1 s1 →
      wp sourceModule rest Q st1 s1 env) :
    wp sourceModule (MatchProgram.sourceLoop ++ rest) Q st base env := by
  have hBaseValues := hInvariant.values
  simp only [MatchProgram.sourceLoop, List.cons_append, List.nil_append, List.append_assoc]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Invariant ctx) (μ := LoopInvariant.measure)
  · exact hInvariant
  · intro st1 s1 hInvariant1
    have hS1Values := hInvariant1.values
    have hS1 : { s1 with values := [] } = s1 := by
      cases s1
      simp_all
    rcases hInvariant1 with hRunning | hCompleted
    · rcases hRunning with ⟨data, owner, facts⟩
      rcases facts.base.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
        hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTrades, hRemaining,
        hOldBook, hOldTrades, hRunningFlag, hScratch⟩
      by_cases hFuelZero : data.fuel = 0
      · have hFuelLocalZero : s1.get 0 = some (.i64 0) := by
          rw [← hFuelZero]
          exact hFuelLocal
        apply LoopControl.loopGuard_zero_fuel_spec env st1 s1 hParams hLocals
          hValues hFuelLocalZero
        simpa [wp_simp, hBaseValues, hValues, hS1] using
          hDone st1 s1 (Or.inr ⟨data, owner, facts, hFuelZero⟩)
      · apply LoopControl.loopGuard_running_spec env st1 s1 data.fuel hParams
          hLocals hValues hFuelLocal hFuelZero hRunningFlag
        apply MatchIteration.dispatch_spec env ctx st1 s1 data owner facts hFuelZero
        intro st2 s2 hInvariant2 hMeasure
        have hS2Values := hInvariant2.values
        have hS2 : { s2 with values := [] } = s2 := by
          cases s2
          simp_all
        simpa [wp_simp, hValues, hS2Values, hS2] using
          And.intro hInvariant2 hMeasure
    · rcases hCompleted with ⟨data, bookOwner, tradesOwner, facts⟩
      rcases facts.base.result with ⟨hBook, hTrades, hRemaining, hDoneFlag, hParams,
        hLocals, hValues⟩
      have hDoneGet : s1.get 24 = some (.i64 1) := by
        simpa [Locals.get, hParams, hLocals] using hDoneFlag
      apply LoopControl.loopGuard_done_spec env st1 s1 data.fuel hParams hLocals
        hValues facts.base.fuelLocal hDoneGet
      simpa [wp_simp, hBaseValues, hValues, hS1] using
        hDone st1 s1 (Or.inl ⟨data, bookOwner, tradesOwner, facts⟩)

#print axioms sourceLoop_spec
end Project.ClobLimit.MatchLoop
