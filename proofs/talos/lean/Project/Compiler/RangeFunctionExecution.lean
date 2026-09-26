import Project.Compiler.RangeLoopExecution
import Project.Compiler.FunctionState
import LeanExe.Extract.ScalarRangeCorrectness

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Stmt Range)
open LeanExe.IR (rangeStore)

def rangeState (args : List UInt64) (width : Nat) : State :=
  { params := args.map Wasm.Value.i64, locals := List.replicate (width + 3) (.i64 0) }

theorem rangeState_agrees (args : List UInt64) (width : Nat) :
    Agrees (rangeStore args 0 0 0) (rangeState args width) := by
  apply agrees_of_flatten (List.replicate width (.i64 0))
  simp [rangeState, rangeStore, List.replicate_succ, List.append_assoc]

@[simp] theorem rangeState_capacity (args : List UInt64) (width : Nat) :
    capacity (rangeState args width) = args.length + 3 + width := by
  simp [capacity, rangeState]
  omega

/-- A terminating interpreter run chooses one final local state, even when its
postcondition initially hides scratch locals existentially. -/
theorem fixed_final_state (m : Wasm.Module) (code : Wasm.Program) (store : Wasm.Store α)
    (initial : Wasm.Locals) (env : Wasm.HostEnv α) (value : UInt64)
    (executed : Wasm.wp m code (fun outcome => ∃ next : State,
      outcome = .Fallthrough store (next.toLocals [.i64 value])) store initial env) :
    ∃ next : State, Wasm.wp m code
      (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value])) store initial env := by
  unfold Wasm.wp at executed ⊢
  obtain ⟨fuel, stable⟩ := executed
  obtain ⟨next, done⟩ := stable fuel le_rfl
  refine ⟨next, fuel, fun larger enough => ?_⟩
  exact (Wasm.exec_fuel_mono enough (by rw [done]; intro impossible; cases impossible)).trans done

/-- Complete range-function execution through the actual instruction emitter.
The source iteration is supplied only by the proved extraction relation. -/
theorem range_function_execution (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {plan : LeanExe.Extract.Core.ScalarRangePlan} {descriptor : Range} {value : UInt64}
    (matched : descriptor.Matches plan) (meaning : plan.Meaning args value)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (code : Wasm.Program) (next : State),
      program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
        (plan.func name exportName args.length)) = some code ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((functionState (plan.func name exportName args.length) args).toLocals []) env := by
  have original := matched
  obtain ⟨hc, hi, hs, hr⟩ := matched
  obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := meaning
  let initial := rangeState args descriptor.scratchWidth
  let scratch := args.length + 3
  let loopCode := Project.ProofKit.ScalarTransition.whileProgram scratch
    (condition (descriptor.loop args.length).condition) (statement (descriptor.loop args.length).body)
  let tail := (expression descriptor.result).program scratch ++ [.localSet args.length, .localGet args.length]
  let code := (statement (descriptor.setup args.length)).program scratch ++ loopCode ++ tail
  have lowered : program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
      (plan.func name exportName args.length)) = some code := by
    rw [Range.func_emit original]
    simp [code, tail, loopCode, scratch, program_append, statement_program, while_program,
      expression_program, program, instruction, List.append_assoc]
  have countWrite : (rangeStore args 0 0 0).write (args.length + 2) stop =
      some (rangeStore args 0 0 stop) := by
    simpa [rangeStore] using LeanExe.IR.write_suffix args [0, 0, 0] 2 stop (by simp)
  have setupEval : (descriptor.setup args.length).eval (rangeStore args 0 0 0) =
      some (rangeStore args start 0 stop) := by
    simp only [Range.setup, Stmt.eval, (Expr.ofIR_eval countEval hc).1, countWrite,
      (Expr.ofIR_eval initialEval hi).1, LeanExe.IR.rangeStore_write_value, Expr.eval,
      LeanExe.IR.rangeStore_write_index, bind, pure, Option.bind_some]
  have setupRoom : scratch + (descriptor.setup args.length).scratchWidth ≤ capacity initial := by
    simp [scratch, initial, Range.setup, Stmt.scratchWidth, Expr.scratchWidth, Range.scratchWidth]
    omega
  obtain ⟨afterSetup, setupComputed, setupAgrees, setupSize⟩ :=
    statement_eval (descriptor.setup args.length) scratch setupEval (rangeState_agrees args descriptor.scratchWidth)
      (by simp [scratch]) (by simp [initial]) setupRoom
  have loopRoom : scratch + (descriptor.loop args.length).scratchWidth ≤ capacity afterSetup := by
    rw [setupSize]
    simp [scratch, initial, Range.loop, LeanExe.Wasm.ScalarDescriptor.While.scratchWidth,
      Stmt.scratchWidth, LeanExe.Wasm.ScalarDescriptor.Cond.scratchWidth, Expr.scratchWidth,
      BEq.beq, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op.beq,
      LeanExe.Wasm.ScalarDescriptor.U64Op.ctorIdx, Range.scratchWidth]
  have executed : Wasm.wp m code (fun outcome => ∃ next : State,
      outcome = .Fallthrough store (next.toLocals [.i64 value])) store (initial.toLocals []) env := by
    dsimp only [code]
    rw [List.append_assoc]
    apply Project.ProofKit.ScalarTransition.Stmt.program_spec _ scratch initial afterSetup [] m env store
      (loopCode ++ tail) _ setupComputed
    apply range_loop_spec args start stop descriptor plan.step step hs stepEval scratch afterSetup []
      (by simp [scratch]) loopRoom setupAgrees m env store tail
    intro afterLoop loopAgrees loopSize
    have resultRoom : scratch + descriptor.result.scratchWidth ≤ capacity afterLoop := by
      rw [loopSize, setupSize]
      simp [scratch, Range.scratchWidth]
    obtain ⟨afterResult, resultComputed, resultAgrees, resultSize⟩ :=
      expression_eval descriptor.result scratch (Expr.ofIR_eval resultEval hr).1 loopAgrees
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
    rw [Range.func_scratch original]
    simp [initial, rangeState, LeanExe.Extract.Core.ScalarRangePlan.func, Nat.add_comm]
  simpa only [initialEq] using finished

end Project.Compiler.ScalarLowering
