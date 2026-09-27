import Project.Core.Compile
import Project.Compiler.ScalarExecution
import Interpreter.Wasm.Wp.Call

namespace Project.Core

open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

/-- A body proof at the current store gives a complete function invocation.
Arguments enter in source order and the public invocation uses operand-stack order. -/
theorem invoke_of_wp {module_ : Wasm.Module} {id : Nat} {function : Wasm.Function}
    {host : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List UInt64} {value : UInt64} {P : Wasm.Store α → Prop}
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some function)
    (arity : args.length = function.numParams)
    (oneResult : function.results.length = 1)
    (executed : Wasm.wp module_ function.body
      (fun outcome => ∃ final frame,
        outcome = .Fallthrough final frame ∧ P final ∧ frame.values = [.i64 value])
      initial (function.toLocals (args.map Wasm.Value.i64)) host) :
    Wasm.TerminatesWith host module_ id initial (args.map Wasm.Value.i64).reverse
      (fun final values => P final ∧ values = [.i64 value]) := by
  unfold Wasm.wp at executed
  obtain ⟨N, executed⟩ := executed
  refine ⟨N, ?_⟩
  intro fuel enough
  obtain ⟨final, frame, done, property, values⟩ := executed fuel enough
  have count : (args.map Wasm.Value.i64).reverse.length = function.numParams := by
    simp [arity]
  have taken : (args.map Wasm.Value.i64).reverse.take function.numParams =
      (args.map Wasm.Value.i64).reverse := by
    rw [← count, List.take_length]
  have dropped : (args.map Wasm.Value.i64).reverse.drop function.numParams = [] := by
    rw [← count, List.drop_length]
  refine ⟨[.i64 value], final, ?_, property, rfl⟩
  rw [Wasm.run_eq notImported, found]
  simp [taken, dropped, done, oneResult, values]

def initialState (imports : Nat) (effectCode : Nat → Wasm.Program)
    (function : LeanExe.Core.Function) (args : List UInt64) : State :=
  State.ofLocals ((compileFunction imports effectCode function).toLocals
    (args.map Wasm.Value.i64))

@[simp] theorem initialState_toLocals (imports : Nat) (effectCode : Nat → Wasm.Program)
    (function : LeanExe.Core.Function) (args : List UInt64) :
    (initialState imports effectCode function args).toLocals [] =
      (compileFunction imports effectCode function).toLocals (args.map Wasm.Value.i64) := rfl

theorem initialState_agrees (imports : Nat) (effectCode : Nat → Wasm.Program)
    (function : LeanExe.Core.Function) (args : List UInt64) :
    Agrees (args ++ List.replicate function.locals 0)
      (initialState imports effectCode function args) := by
  apply Project.Compiler.ScalarLowering.agrees_of_flatten
    (List.replicate (max (width function.body) function.result.scratchWidth) (.i64 0))
  simp [initialState, compileFunction, State.ofLocals, Wasm.Function.toLocals,
    Wasm.ValueType.zero, List.append_assoc]

theorem initialState_capacity (imports : Nat) (effectCode : Nat → Wasm.Program)
    (function : LeanExe.Core.Function) (args : List UInt64)
    (arity : args.length = function.params) :
    capacity (initialState imports effectCode function args) =
      function.params + function.locals + max (width function.body) function.result.scratchWidth := by
  simp [capacity, initialState, compileFunction, State.ofLocals, Wasm.Function.toLocals,
    arity, Nat.add_assoc]

end Project.Core
