import Project.ClobLimit.InternalLoopIteration
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Generated internal match loop

The internal matcher places the guard and dispatcher in one zero-arity loop.
A trailing branch re-enters after every dispatcher outcome, including a
completed result.  The enclosing block exits with either a completed state or
a running state whose fuel reached zero.
-/

namespace Project.ClobLimit.InternalLoop

open Wasm Project.ClobLimit Project.ClobLimit.InternalLoopInvariant

def bodyProg : Wasm.Program :=
  InternalLoopControl.loopGuardProg ++
    (InternalIteration.dispatchProg InternalFullBranch.fullBranchProg
      InternalPartialBranch.partialBranchProg ++ [.br 0])

def loopProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 bodyProg]]

set_option Elab.async false in
theorem loopProg_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (hInvariant : Invariant ctx st base)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, ExitAt ctx st1 s1 →
      wp «module» rest Q st1 s1 env) :
    wp «module» (loopProg ++ rest) Q st base env := by
  have hBaseValues := hInvariant.values
  unfold loopProg
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Invariant ctx) (μ := measure)
  · exact hInvariant
  · intro st1 s1 hInvariant1
    have hS1Values := hInvariant1.values
    have hS1 : { s1 with values := [] } = s1 := by
      cases s1
      simp_all
    rcases hInvariant1 with hRunning | hCompleted
    · rcases hRunning with ⟨data, facts⟩
      rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
        hTrader, hSide, hPrice, hQty, hBookOwner, hBook, hTradesOwner,
        hTrades, hRemaining, hRunningFlag, hScratch⟩
      by_cases hFuelZero : data.fuel = 0
      · have hFuelLocalZero : s1.get 0 = some (.i64 0) := by
          rw [← hFuelZero]
          exact hFuelLocal
        unfold bodyProg
        apply InternalLoopControl.loopGuard_zero_fuel_spec env st1 s1 hParams
          hLocals hValues hFuelLocalZero
        simpa [wp_simp, hBaseValues, hValues, hS1] using
          hDone st1 s1 (Or.inr ⟨data, facts, hFuelZero⟩)
      · unfold bodyProg
        apply InternalLoopControl.loopGuard_running_spec env st1 s1 data.fuel
          hParams hLocals hValues hFuelLocal hFuelZero hRunningFlag
        apply InternalLoopIteration.dispatch_spec env ctx st1 s1 data facts
          hFuelZero
        intro st2 s2 hInvariant2 hMeasure
        have hS2Values := hInvariant2.values
        have hS2 : { s2 with values := [] } = s2 := by
          cases s2
          simp_all
        simpa [wp_simp, hValues, hS2Values, hS2] using
          And.intro hInvariant2 hMeasure
    · rcases hCompleted with ⟨data, facts⟩
      rcases facts.result with
        ⟨hBookOwner, hBook, hTradesOwner, hTrades, hRemaining, hDoneFlag,
          hParams, hLocals, hValues⟩
      have hDoneGet : s1.get 16 = some (.i64 1) := by
        simpa [Locals.get, hParams, hLocals] using hDoneFlag
      unfold bodyProg
      apply InternalLoopControl.loopGuard_done_spec env st1 s1 data.fuel
        hParams hLocals hValues facts.fuelLocal hDoneGet
      simpa [wp_simp, hBaseValues, hValues, hS1] using
        hDone st1 s1 (Or.inl ⟨data, facts⟩)

end Project.ClobLimit.InternalLoop
