import Verified.Wasi.EntryCorrect
import Verified.Wasi.ExitStack

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def startSignature : EffectSig := ⟨"_start", [], [], .unit⟩

def EffectMain.signature (main : EffectMain effectSigs) : EffectSig :=
  ⟨main.name, List.replicate main.tables.length (.array .word),
    List.replicate main.tables.length .borrowed, .value .word⟩

def EffectMain.action (main : EffectMain effectSigs) (pure : Funs pureSigs)
    (program : EffectProg pureSigs effectSigs) (args : Env main.signature.params) : Action Unit :=
  Action.bind ((program.funs pure).get main.callee args) fun status => .exit status

theorem start_after_main_trap {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {main : EffectMain effectSigs} {args : Env main.signature.params}
    {heap : Heap} {initial final : Store (Observed World)} {aborts : Bool} {message : String}
    (classification : FunctionResult host main.signature
      ((program.funs pure.funs).get main.callee args) args (main.tables.map Value.i64)
      heap initial aborts (.Trap final message)) :
    FunctionResult host startSignature (main.action pure.funs program args) .nil []
      heap initial aborts (.Trap final message) := by
  cases classification with
  | terminal final trace outcome message execution terminal =>
      cases outcome with
      | returned value => exact terminal.elim
      | exited code =>
          refine .terminal final trace (.exited code) message ?_ terminal
          change Exec (observedHost host)
            (Action.bind ((program.funs pure.funs).get main.callee args)
              (fun status => Action.exit (α := Unit) status))
            initial.host trace (@Outcome.exited Unit code) final.host
          have composed : Exec (observedHost host)
              (Action.bind ((program.funs pure.funs).get main.callee args)
                (fun status => Action.exit (α := Unit) status))
              initial.host (trace ++ []) (@Outcome.exited Unit code) final.host :=
            Exec.bind (α := UInt64) (β := Unit) execution
              (next := fun status => Action.exit (α := Unit) status) (rest := []) ⟨rfl, rfl, rfl⟩
          rw [List.append_nil] at composed
          exact composed
      | trapped cause =>
          refine .terminal final trace (.trapped cause) message ?_ terminal
          change Exec (observedHost host)
            (Action.bind ((program.funs pure.funs).get main.callee args)
              (fun status => Action.exit (α := Unit) status))
            initial.host trace (@Outcome.trapped Unit cause) final.host
          have composed : Exec (observedHost host)
              (Action.bind ((program.funs pure.funs).get main.callee args)
                (fun status => Action.exit (α := Unit) status))
              initial.host (trace ++ []) (@Outcome.trapped Unit cause) final.host :=
            Exec.bind (α := UInt64) (β := Unit) execution
              (next := fun status => Action.exit (α := Unit) status) (rest := []) ⟨rfl, rfl, rfl⟩
          rw [List.append_nil] at composed
          exact composed
  | resource final trace residual allowed progress =>
      exact .resource final trace (Action.bind residual fun status => Action.exit (α := Unit) status)
        allowed progress.bind

theorem wp_start_body {World : Type} {source target : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {main : EffectMain effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {args : Env main.signature.params} {budget : Nat} {aborts : Bool} {calleeFunction : Wasm.Function}
    (spec : CostEffectSpec source target pure program main.callee
      (Wrappers.effectIndex source main.callee.index) pool)
    (imports : target.imports = ABI.imports)
    (lookup : target.funcs[Wrappers.effectIndex source main.callee.index - target.imports.length]? =
      some calleeFunction)
    (arity : calleeFunction.numParams = 1 + widthSum main.signature.params)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep main.signature.mode heap (PureTransport.erase initial) (main.tables.map Value.i64) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args)
      (Env.reads (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args))
    (input : @Bytes.LiteralPool.Input (Env main.signature.params)
      (Env.represent main.signature.params main.signature.modes) pool heap (PureTransport.erase initial)
      (main.tables.map Value.i64) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) main.signature.mode
      (main.tables.map Value.i64) args, regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program main.callee 0 args initial.host budget) :
    wp target (main.function source typeIdx).body
      (FunctionRunPost 0 (FunctionResult host startSignature (main.action pure.funs program args)
        .nil [] heap initial aborts)) initial ((main.function source typeIdx).toLocals []) targetHost := by
  let locals := (main.function source typeIdx).toLocals []
  let Q := FunctionRunPost 0 (FunctionResult host startSignature (main.action pure.funs program args)
    .nil [] heap initial aborts)
  have noImport : target.imports[Wrappers.effectIndex source main.callee.index]? = none :=
    List.getElem?_eq_none (by
      rw [imports, ABI.imports_length]
      simp only [Wrappers.effectIndex, Module.extraIndex]
      omega)
  have call := wp_cost_effect_helper (locals := locals) (values := []) (depth := 0)
    (rest := [.wrapI64, .call 2, .unreachable]) (Q := Q)
    spec noImport lookup arity valid at_ rep separate input scratch cap resources
    (fun value finalHeap final words trace spent fits resourceExecution step representation top => by
      have wordsEq : words = [.i64 value] := representation
      subst words
      change wp target (.wrapI64 :: .call 2 :: .unreachable :: []) Q final
        { locals with values := .i64 value :: [] } targetHost
      refine wp_exit_stack imports valid ?_ ?_
      · intro ended accepted frame
        change FunctionResult host startSignature (main.action pure.funs program args) .nil []
          heap initial aborts (.Trap ended exitTrap)
        refine .terminal ended (trace ++ [.exit (exitStatus value)]) (.exited (exitStatus value)) exitTrap ?_ rfl
        exact resourceExecution.erase.bind (β := Unit)
          (next := fun status => Action.exit (α := Unit) status) (Exec.exit accepted)
      · intro ended message rejected frame
        change FunctionResult host startSignature (main.action pure.funs program args) .nil []
          heap initial aborts (.Trap ended message)
        refine .terminal ended (trace ++ [.exitTrap (exitStatus value) message]) (.trapped message) message ?_ rfl
        exact resourceExecution.erase.bind (β := Unit)
          (next := fun status => Action.exit (α := Unit) status) (Exec.exitTrap rejected))
    (fun final message classification => by
      change FunctionResult host startSignature (main.action pure.funs program args) .nil []
        heap initial aborts (.Trap final message)
      exact start_after_main_trap classification)
  have injected := wp_injected_arguments (locals := locals) main.tables ([] : List Value) rfl
    (by simpa only [locals, Function.toLocals, List.append_nil] using call)
  simpa only [EffectMain.function, List.length_nil, List.range_zero, List.map_nil,
    List.nil_append, List.append_nil, locals, Q] using injected

theorem compile_start_export (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    ({ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length } : Wasm.Export) ∈
      (compile source program entries (some main) pool).exports := by
  rw [compile_command_exports source program entries main pool]
  exact List.mem_singleton_self _

theorem compiled_start_run {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs) (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compile source program entries (some main) pool) pure program pool)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {args : Env main.signature.params} {budget : Nat} {aborts : Bool}
    (valid : targetHost.Satisfies (compile source program entries (some main) pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep main.signature.mode heap (PureTransport.erase initial) (main.tables.map Value.i64) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args)
      (Env.reads (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args))
    (input : @Bytes.LiteralPool.Input (Env main.signature.params)
      (Env.represent main.signature.params main.signature.modes) pool heap (PureTransport.erase initial)
      (main.tables.map Value.i64) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) main.signature.mode
      (main.tables.map Value.i64) args, regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap (compile source program entries (some main) pool) 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program main.callee 0 args initial.host budget) :
    ∃ bound, ∀ fuel ≥ bound,
      FunctionResult host startSignature (main.action pure.funs program args) .nil [] heap initial aborts
        (run fuel (compile source program entries (some main) pool)
          (Wrappers.effectIndex source effectSigs.length) initial [] targetHost) := by
  have lookup := compile_start source program entries main pool
  obtain ⟨calleeFunction, calleeLookup, arity⟩ :=
    compile_effect_arity source program entries (some main) pool main.callee
  have body := wp_start_body (typeIdx := effectTypeIndex source effectSigs.length)
    (calls main.callee) (compile_imports source program entries (some main) pool) calleeLookup arity
    valid at_ rep separate input scratch cap resources
  have execution := defined_function_run_post (compile_imports source program entries (some main) pool)
    lookup (params := []) (width := 0) rfl rfl body
  simpa only [Wrappers.effectIndex, Module.extraIndex, Nat.add_assoc, List.reverse_nil] using execution

end Verified.Wasi
