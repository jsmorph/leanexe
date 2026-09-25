import Project.Compiler.RangeExitLoopExecution
import Project.Compiler.RangeFunctionExecution
import Project.Compiler.FunctionState
import LeanExe.Extract.ScalarRangeExitCorrectness

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Stmt RangeExit)
open LeanExe.IR (rangeExitStore)

def rangeExitState (args : List UInt64) (width : Nat) : State :=
  { params := args.map Wasm.Value.i64, locals := List.replicate (width + 4) (.i64 0) }

theorem rangeExitState_agrees (args : List UInt64) (width : Nat) :
    Agrees (rangeExitStore args 0 0 0 0) (rangeExitState args width) := by
  apply agrees_of_flatten (List.replicate width (.i64 0))
  simp [rangeExitState, rangeExitStore, List.replicate_succ, List.append_assoc]

@[simp] theorem rangeExitState_capacity (args : List UInt64) (width : Nat) :
    capacity (rangeExitState args width) = args.length + 4 + width := by
  simp [capacity, rangeExitState]
  omega

/-- Complete range-function execution through the actual instruction emitter.
The source iteration is supplied only by the proved extraction relation. -/
theorem range_exit_function_execution (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {plan : LeanExe.Extract.Core.ScalarRangeExitPlan} {descriptor : RangeExit} {value : UInt64}
    (matched : descriptor.Matches plan) (meaning : plan.Meaning args value)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (code : Wasm.Program) (next : State),
      program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
        (plan.func name exportName args.length)) = some code ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((functionState (plan.func name exportName args.length) args).toLocals []) env := by
  have original := matched
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := meaning
  let initial := rangeExitState args descriptor.scratchWidth
  let scratch := args.length + 4
  let loopCode := Project.ProofKit.ScalarTransition.whileProgram scratch
    (condition (descriptor.loop args.length).condition) (statement (descriptor.loop args.length).body)
  let tail := (expression descriptor.result).program scratch ++ [.localSet args.length, .localGet args.length]
  let code := (statement (descriptor.setup args.length)).program scratch ++ loopCode ++ tail
  have lowered : program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
      (plan.func name exportName args.length)) = some code := by
    rw [RangeExit.func_emit original]
    simp [code, tail, loopCode, scratch, program_append, statement_program, while_program,
      expression_program, program, instruction, List.append_assoc]
  have countWrite : (rangeExitStore args 0 0 0 0).write (args.length + 2) stop =
      some (rangeExitStore args 0 0 stop 0) := by
    simpa [rangeExitStore] using LeanExe.IR.write_suffix args [0, 0, 0, 0] 2 stop (by simp)
  have setupEval : (descriptor.setup args.length).eval (rangeExitStore args 0 0 0 0) =
      some (rangeExitStore args start 0 stop 0) := by
    simp only [RangeExit.setup, Stmt.eval, (Expr.ofIR_eval countEval hc).1, countWrite,
      (Expr.ofIR_eval initialEval hi).1, LeanExe.IR.rangeExitStore_write_value, Expr.eval,
      LeanExe.IR.rangeExitStore_write_index, LeanExe.IR.rangeExitStore_write_flag, bind, pure, Option.bind_some]
    rfl
  have setupRoom : scratch + (descriptor.setup args.length).scratchWidth ≤ capacity initial := by
    simp [scratch, initial, RangeExit.setup, Stmt.scratchWidth, Expr.scratchWidth, RangeExit.scratchWidth]
    omega
  obtain ⟨afterSetup, setupComputed, setupAgrees, setupSize⟩ :=
    statement_eval (descriptor.setup args.length) scratch setupEval (rangeExitState_agrees args descriptor.scratchWidth)
      (by simp [scratch]) (by simp [initial]) setupRoom
  have loopRoom : scratch + (descriptor.loop args.length).scratchWidth ≤ capacity afterSetup := by
    rw [setupSize]
    simp [scratch, initial, RangeExit.loop, RangeExit.index, LeanExe.Wasm.ScalarDescriptor.While.scratchWidth,
      Stmt.scratchWidth, LeanExe.Wasm.ScalarDescriptor.Cond.scratchWidth, Expr.scratchWidth,
      BEq.beq, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op.beq,
      LeanExe.Wasm.ScalarDescriptor.U64Op.ctorIdx, RangeExit.scratchWidth]
    omega
  have executed : Wasm.wp m code (fun outcome => ∃ next : State,
      outcome = .Fallthrough store (next.toLocals [.i64 value])) store (initial.toLocals []) env := by
    dsimp only [code]
    rw [List.append_assoc]
    apply Project.ProofKit.ScalarTransition.Stmt.program_spec _ scratch initial afterSetup [] m env store
      (loopCode ++ tail) _ setupComputed
    apply range_exit_loop_spec args start stop descriptor plan.step plan.done step hs hd stepEval scratch afterSetup []
      (by simp [scratch]) loopRoom setupAgrees m env store tail
    intro afterLoop flag loopAgrees loopSize
    have resultRoom : scratch + descriptor.result.scratchWidth ≤ capacity afterLoop := by
      rw [loopSize, setupSize]
      simp [scratch, RangeExit.scratchWidth]
    obtain ⟨afterResult, resultComputed, resultAgrees, resultSize⟩ :=
      expression_eval descriptor.result scratch (Expr.ofIR_eval (resultEval flag) hr).1 loopAgrees
        (by simp [scratch]) resultRoom
    obtain ⟨next, written, nextSize⟩ := set_exists (state := afterResult) (index := args.length) (.i64 value)
      (by simp [scratch] at resultRoom; omega)
    apply Project.ProofKit.ScalarTransition.Expr.program_spec _ scratch afterLoop afterResult value [] m env store
      [.localSet args.length, .localGet args.length] _ resultComputed
    apply Project.ProofKit.ScalarTransition.localSet_spec written
    apply Project.ProofKit.ScalarTransition.localGet_spec (State.get_set?_same written)
    simp
    exact ⟨next, rfl, rfl⟩
  obtain ⟨next, finished⟩ := fixed_final_state m code store (initial.toLocals []) env value executed
  refine ⟨code, next, lowered, ?_⟩
  have initialEq : functionState (plan.func name exportName args.length) args = initial := by
    unfold functionState
    rw [RangeExit.func_scratch original]
    simp [initial, rangeExitState, LeanExe.Extract.Core.ScalarRangeExitPlan.func, Nat.add_comm]
  simpa only [initialEq] using finished

end Project.Compiler.ScalarLowering
