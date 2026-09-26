import Project.Compiler.RangeLoopExecution
import LeanExe.Wasm.ScalarRangeExitCertificate

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Stmt Cond RangeExit)
open LeanExe.IR (rangeExitStore)

theorem rangeExitIndex_agrees {saved : List UInt64} {value stop flag : UInt64} {index : Nat} {state : State}
    (agree : Agrees (rangeExitStore saved value index stop flag) state) (bound : index ≤ stop.toNat) :
    rangeIndex state (saved.length + 1) = index := by
  simp only [rangeIndex, agree _ _ (LeanExe.IR.rangeExitStore_index saved value index stop flag)]
  exact LeanExe.Source.Scalar.Range.index_toNat bound

/-- Execution of the emitted loop with native early-exit semantics. The
invariant records the result of the remaining source iterations; a done step
reaches the bound immediately, while a yielding step advances once. -/
theorem range_exit_loop_spec (saved : List UInt64) (start stop : UInt64)
    (descriptor : RangeExit) (irStep irDone : LeanExe.IR.Expr) (step : Nat → UInt64 → ForInStep UInt64)
    (matchedStep : Expr.ofIR irStep = some descriptor.step)
    (matchedDone : Expr.ofIR irDone = some descriptor.done)
    (sourceStep : ∀ index, index < stop.toNat → ∀ value flag,
      (LeanExe.Extract.Core.ScalarStepCode.mk irStep irDone).Meaning
        (rangeExitStore saved value index stop flag) (step index value))
    (scratch : Nat) (initial : State) (values : List Wasm.Value)
    (above : saved.length + 4 ≤ scratch)
    (room : scratch + (descriptor.loop saved.length).scratchWidth ≤ capacity initial)
    (agree : Agrees (rangeExitStore saved start 0 stop 0) initial)
    (module_ : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α)
    (rest : Wasm.Program) (Q : Wasm.Assertion α)
    (next : ∀ state flag,
      Agrees (rangeExitStore saved (LeanExe.Source.Scalar.Range.Exit.iterate step stop.toNat 0 start)
        stop.toNat stop flag) state →
      capacity state = capacity initial →
      Wasm.wp module_ rest Q store (state.toLocals values) env) :
    Wasm.wp module_
      (Project.ProofKit.ScalarTransition.whileProgram scratch
        (condition (descriptor.loop saved.length).condition) (statement (descriptor.loop saved.length).body) ++ rest)
      Q store (initial.toLocals values) env := by
  let wanted := LeanExe.Source.Scalar.Range.Exit.iterate step stop.toNat 0 start
  let Inv := fun state => ∃ index value flag, index ≤ stop.toNat ∧
    Agrees (rangeExitStore saved value index stop flag) state ∧
    capacity state = capacity initial ∧
    LeanExe.Source.Scalar.Range.Exit.iterate step (stop.toNat - index) index value = wanted
  let measure := fun state => stop.toNat - rangeIndex state (saved.length + 1)
  apply Project.ProofKit.ScalarTransition.whileProgram_spec _ _ scratch initial values module_ env store rest Q Inv measure
  · exact ⟨0, start, 0, by omega, agree, rfl, by simp [wanted]⟩
  · intro current invariant
    obtain ⟨index, value, flag, bound, currentAgrees, currentSize, remaining⟩ := invariant
    have tested : (descriptor.loop saved.length).condition.eval (rangeExitStore saved value index stop flag) =
        some (decide (index < stop.toNat)) := by
      simp only [RangeExit.loop, Cond.eval, Expr.eval, LeanExe.IR.rangeExitStore_index, LeanExe.IR.rangeExitStore_stop]
      simp [LeanExe.Source.Scalar.Range.index_lt_stop bound]
    obtain ⟨afterCondition, conditionEval, conditionAgrees, conditionSize⟩ :=
      condition_eval (descriptor.loop saved.length).condition scratch tested currentAgrees
        (by simpa using above) (by simp only [LeanExe.Wasm.ScalarDescriptor.While.scratchWidth] at room; omega)
    refine ⟨decide (index < stop.toNat), afterCondition, conditionEval, ?_⟩
    by_cases below : index < stop.toNat
    · simp only [below, decide_true, ite_true]
      have recognized : Stmt.ofIR (LeanExe.IR.rangeExitBody saved.length irStep irDone) =
          some (descriptor.loop saved.length).body := by
        simp [LeanExe.IR.rangeExitBody, LeanExe.IR.rangeExitIndex, RangeExit.loop, RangeExit.index,
          Stmt.ofIR, Expr.ofIR, Cond.ofIR, matchedStep, matchedDone, LeanExe.Wasm.ScalarDescriptor.U64Op.ofIR]
      have bodyEval := Stmt.ofIR_eval
        (LeanExe.IR.rangeExitBody_step saved value index stop flag irStep irDone (step index value)
          (sourceStep index below value flag).2
          (sourceStep index below value (LeanExe.IR.rangeExitFlag (step index value))).1) recognized
      obtain ⟨afterBody, executed, bodyAgrees, bodySize⟩ :=
        statement_eval (descriptor.loop saved.length).body scratch bodyEval conditionAgrees
          (by simpa using above) (by simp only [LeanExe.IR.rangeExitStore_length]; omega)
          (by simp only [LeanExe.Wasm.ScalarDescriptor.While.scratchWidth] at room; omega)
      have nextBound : LeanExe.IR.rangeExitNextIndex index stop (step index value) ≤ stop.toNat := by
        cases step index value <;> simp [LeanExe.IR.rangeExitNextIndex, LeanExe.Source.Scalar.Range.Exit.isDone] <;> omega
      have resultRemaining : LeanExe.Source.Scalar.Range.Exit.iterate step
          (stop.toNat - LeanExe.IR.rangeExitNextIndex index stop (step index value))
          (LeanExe.IR.rangeExitNextIndex index stop (step index value))
          (LeanExe.Source.Scalar.Range.Exit.value (step index value)) = wanted := by
        rw [show stop.toNat - index = (stop.toNat - (index + 1)) + 1 by omega,
          LeanExe.Source.Scalar.Range.Exit.iterate] at remaining
        cases outcome : step index value <;>
          simpa [LeanExe.IR.rangeExitNextIndex, LeanExe.Source.Scalar.Range.Exit.isDone,
            LeanExe.Source.Scalar.Range.Exit.value, LeanExe.Source.Scalar.Range.Exit.iterate, outcome] using remaining
      refine ⟨afterBody, executed,
        ⟨_, _, _, nextBound, bodyAgrees, by omega, resultRemaining⟩, ?_⟩
      have beforeIndex := rangeExitIndex_agrees currentAgrees bound
      have afterIndex := rangeExitIndex_agrees bodyAgrees nextBound
      dsimp [measure]
      rw [beforeIndex, afterIndex]
      cases step index value <;> simp [LeanExe.IR.rangeExitNextIndex, LeanExe.Source.Scalar.Range.Exit.isDone] <;> omega
    · simp only [below, decide_false, Bool.false_eq_true, ite_false]
      have same : index = stop.toNat := by omega
      subst index
      have result : value = wanted := by simpa [LeanExe.Source.Scalar.Range.Exit.iterate] using remaining
      exact next afterCondition flag (by simpa only [result] using conditionAgrees) (by omega)

end Project.Compiler.ScalarLowering
