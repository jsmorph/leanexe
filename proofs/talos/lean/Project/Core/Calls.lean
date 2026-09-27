import Project.Core.Contract
import Project.Core.Invoke
import Project.Compiler.ScalarStatements

namespace Project.Core

open LeanExe.Core
open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

theorem invoke_compiled (context : Context σ α)
    {callee : Nat} {function : LeanExe.Core.Function} {args returned : List UInt64}
    {initial final : σ} {value : UInt64}
    (found : context.source[callee]? = some function)
    (arity : args.length = function.params)
    (body : StatementSpec context function.body initial
      (args ++ List.replicate function.locals 0) final returned)
    (length : returned.length = args.length + function.locals)
    (output : function.result.eval returned = some value)
    (store : Wasm.Store α) (represented : context.represents initial store) :
    Wasm.TerminatesWith context.host context.target
      (context.target.imports.length + callee) store (args.map Wasm.Value.i64).reverse
      (fun next values => context.represents final next ∧ values = [.i64 value]) := by
  apply invoke_of_wp
    (function := compileFunction context.target.imports.length context.effectCode function)
  · exact List.getElem?_eq_none (by omega)
  · simpa using context.functions callee function found
  · simpa [Wasm.Function.numParams, compileFunction] using arity
  · rfl
  · let state := initialState context.target.imports.length context.effectCode function args
    have size := initialState_capacity context.target.imports.length context.effectCode function args arity
    rw [← initialState_toLocals]
    apply body (function.params + function.locals) store state represented
      (initialState_agrees _ _ _ _)
      (by simp [arity]) (by simp only [List.length_append, List.length_replicate]; dsimp [state] at *; omega)
      (by dsimp [state] at *; omega)
    intro nextStore nextState nextRep agrees nextSize
    obtain ⟨last, computed, _, lastSize⟩ := Project.Compiler.ScalarLowering.expression_eval
      function.result (function.params + function.locals) output agrees
      (by omega) (by dsimp [state] at *; omega)
    have execution := Project.ProofKit.ScalarTransition.Expr.program_spec
      (Project.Compiler.ScalarLowering.expression function.result)
      (function.params + function.locals) nextState last value []
      context.target context.host nextStore []
      (fun outcome => ∃ finalStore frame,
        outcome = .Fallthrough finalStore frame ∧ context.represents final finalStore ∧
        frame.values = [.i64 value]) computed (by simpa using nextRep)
    simpa using execution

theorem call_spec (context : Context σ α)
    {destination callee : Nat} {function : LeanExe.Core.Function}
    {expressions : List LeanExe.Wasm.ScalarDescriptor.Expr}
    {args locals returned result : List UInt64} {initial final : σ} {value : UInt64}
    (found : context.source[callee]? = some function)
    (inputs : arguments expressions locals = some args)
    (arity : args.length = function.params)
    (body : StatementSpec context function.body initial
      (args ++ List.replicate function.locals 0) final returned)
    (length : returned.length = args.length + function.locals)
    (output : function.result.eval returned = some value)
    (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
    StatementSpec context (.call destination callee expressions) initial locals final result := by
  intro scratch store state represented agrees above localRoom room rest Q next
  have destinationBound : destination < locals.length := by
    unfold LeanExe.IR.ScalarStore.write at written
    split at written
    · assumption
    · contradiction
  obtain ⟨prepared, preparedAgree, preparedSize, argumentsSpec⟩ :=
    arguments_execution expressions scratch inputs agrees above room [] context.target context.host store
  simp only [statement, List.append_assoc, List.cons_append, List.nil_append]
  apply argumentsSpec
  have invoked := invoke_compiled context found arity body length output store represented
  apply Wasm.wp_call_tw (by simpa using invoked)
  rintro nextStore values ⟨nextRep, rfl⟩
  obtain ⟨last, set, size⟩ := Project.Compiler.ScalarLowering.set_exists
    (state := prepared) (index := destination) (.i64 value) (by omega)
  apply Project.ProofKit.ScalarTransition.localSet_spec set
  exact next nextStore last nextRep (preparedAgree.store_write written set) (size.trans preparedSize)

end Project.Core
