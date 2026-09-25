import Project.Compiler.ScalarStatements
import LeanExe.Wasm.ScalarRangeCertificate
import LeanExe.IR.ScalarRangeSlots

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Stmt Cond Range)
open LeanExe.IR (rangeStore)

/-- Used only as the terminating loop's rank; its read is proved present below. -/
def rangeIndex (state : State) (slot : Nat) : Nat :=
  match state.get slot with
  | some (.i64 value) => value.toNat
  | _ => 0

theorem rangeIndex_agrees {saved : List UInt64} {value stop : UInt64} {index : Nat} {state : State}
    (agree : Agrees (rangeStore saved value index stop) state) (bound : index ≤ stop.toNat) :
    rangeIndex state (saved.length + 1) = index := by
  simp only [rangeIndex, agree _ _ (LeanExe.IR.rangeStore_index saved value index stop)]
  exact LeanExe.Source.Scalar.Range.index_toNat bound

/-- Execution of the actual structured range loop for any captured arguments,
initial accumulator and UInt64 stop. The source iteration determines the result;
the decreasing rank is the remaining natural index count. -/
theorem range_loop_spec (saved : List UInt64) (start stop : UInt64)
    (descriptor : Range) (irStep : LeanExe.IR.Expr) (step : Nat → UInt64 → UInt64)
    (matched : Expr.ofIR irStep = some descriptor.step)
    (sourceStep : ∀ index, index < stop.toNat → ∀ value,
      irStep.ScalarEval (rangeStore saved value index stop) (step index value)
        (rangeStore saved value index stop))
    (scratch : Nat) (initial : State) (values : List Wasm.Value)
    (above : saved.length + 3 ≤ scratch)
    (room : scratch + (descriptor.loop saved.length).scratchWidth ≤ capacity initial)
    (agree : Agrees (rangeStore saved start 0 stop) initial)
    (module_ : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α)
    (rest : Wasm.Program) (Q : Wasm.Assertion α)
    (next : ∀ state,
      Agrees (rangeStore saved (LeanExe.Source.Scalar.Range.iterate step stop.toNat 0 start) stop.toNat stop) state →
      capacity state = capacity initial →
      Wasm.wp module_ rest Q store (state.toLocals values) env) :
    Wasm.wp module_
      (Project.ProofKit.ScalarTransition.whileProgram scratch
        (condition (descriptor.loop saved.length).condition) (statement (descriptor.loop saved.length).body) ++ rest)
      Q store (initial.toLocals values) env := by
  let Inv := fun state => ∃ index, index ≤ stop.toNat ∧
    Agrees (rangeStore saved (LeanExe.Source.Scalar.Range.iterate step index 0 start) index stop) state ∧
    capacity state = capacity initial
  let measure := fun state => stop.toNat - rangeIndex state (saved.length + 1)
  apply Project.ProofKit.ScalarTransition.whileProgram_spec _ _ scratch initial values module_ env store rest Q Inv measure
  · exact ⟨0, by omega, agree, rfl⟩
  · intro current invariant
    obtain ⟨index, bound, currentAgrees, currentSize⟩ := invariant
    let value := LeanExe.Source.Scalar.Range.iterate step index 0 start
    have tested : (descriptor.loop saved.length).condition.eval (rangeStore saved value index stop) =
        some (decide (index < stop.toNat)) := by
      simp only [Range.loop, Cond.eval, Expr.eval, LeanExe.IR.rangeStore_index, LeanExe.IR.rangeStore_stop]
      simp [LeanExe.Source.Scalar.Range.index_lt_stop bound]
    obtain ⟨afterCondition, conditionEval, conditionAgrees, conditionSize⟩ :=
      condition_eval (descriptor.loop saved.length).condition scratch tested currentAgrees
        (by simpa using above) (by simp only [LeanExe.Wasm.ScalarDescriptor.While.scratchWidth] at room; omega)
    refine ⟨decide (index < stop.toNat), afterCondition, conditionEval, ?_⟩
    by_cases below : index < stop.toNat
    · simp only [below, decide_true, ite_true]
      have recognized : Stmt.ofIR (LeanExe.IR.rangeBody saved.length irStep) =
          some (descriptor.loop saved.length).body := by
        simp [LeanExe.IR.rangeBody, Range.loop, Stmt.ofIR, Expr.ofIR, matched,
          LeanExe.Wasm.ScalarDescriptor.U64Op.ofIR]
      have bodyEval := Stmt.ofIR_eval
        (LeanExe.IR.rangeBody_step saved value (step index value) index stop irStep (sourceStep index below value)) recognized
      obtain ⟨afterBody, executed, bodyAgrees, bodySize⟩ :=
        statement_eval (descriptor.loop saved.length).body scratch bodyEval conditionAgrees
          (by simpa using above) (by simp only [LeanExe.IR.rangeStore_length]; omega)
          (by simp only [LeanExe.Wasm.ScalarDescriptor.While.scratchWidth] at room; omega)
      refine ⟨afterBody, executed, ?_, ?_⟩
      · have nextValue : LeanExe.Source.Scalar.Range.iterate step (index + 1) 0 start = step index value := by
          rw [LeanExe.Source.Scalar.Range.iterate_add]
          simp [LeanExe.Source.Scalar.Range.iterate, value]
        exact ⟨index + 1, by omega, by simpa [nextValue] using bodyAgrees, by omega⟩
      · have beforeIndex := rangeIndex_agrees currentAgrees bound
        have afterIndex := rangeIndex_agrees bodyAgrees (by omega)
        dsimp [measure]
        rw [beforeIndex, afterIndex]
        omega
    · simp only [below, decide_false, Bool.false_eq_true, ite_false]
      have same : index = stop.toNat := by omega
      subst index
      exact next afterCondition conditionAgrees (by omega)

end Project.Compiler.ScalarLowering
