import Project.Compiler.FunctionState
import LeanExe.Wasm.ScalarScratch
import LeanExe.Wasm.ScalarAdmission

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr)

theorem scalar_function_execution (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {ir : LeanExe.IR.Expr} {descriptor : Expr} {value : UInt64}
    (recognized : Expr.ofIR ir = some descriptor)
    (evaluated : ir.ScalarEval (args ++ [0]) value (args ++ [0]))
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    let func := LeanExe.Extract.Core.scalarFunc name exportName args.length ir
    ∃ (code : Wasm.Program) (next : State),
      program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) = some code ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((functionState func args).toLocals []) env := by
  dsimp only
  have heval := (Expr.ofIR_eval evaluated recognized).1
  obtain ⟨afterExpr, computed, preserved, size⟩ := expression_eval descriptor (args.length + 1)
    heval (scalarState_agrees args descriptor.scratchWidth) (by simp) (by simp)
  obtain ⟨next, written, sizeNext⟩ := set_exists (state := afterExpr)
    (index := args.length) (.i64 value) (by simp_all; omega)
  let code := (expression descriptor).program (args.length + 1) ++
    [.localSet args.length, .localGet args.length]
  refine ⟨code, next, ?_, ?_⟩
  · rw [LeanExe.Wasm.ScalarDescriptor.scalarFunc_emit _ _ _ _ _ _ recognized]
    simp [code, program_append, expression_program, program, instruction]
  · have initial : functionState (LeanExe.Extract.Core.scalarFunc name exportName args.length ir) args =
        scalarState args descriptor.scratchWidth := by
      unfold functionState
      rw [LeanExe.Wasm.ScalarDescriptor.scalarFunc_scratch _ _ _ recognized]
      simp [scalarState, LeanExe.Extract.Core.scalarFunc, Nat.add_comm]
    rw [initial]
    apply Project.ProofKit.ScalarTransition.Expr.program_spec
      (expression descriptor) (args.length + 1) _ afterExpr value [] m env store
      [.localSet args.length, .localGet args.length] _ computed
    apply Project.ProofKit.ScalarTransition.localSet_spec written
    apply Project.ProofKit.ScalarTransition.localGet_spec (State.get_set?_same written)
    simp

/-- General source-declaration preservation through the complete production
function instruction emitter. The next proof boundary is the encoded module,
its decoder/validation, and exported-function invocation. -/
theorem extracted_function_execution {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : LeanExe.Extract.Core.extractScalarFunc name exportName type source = some func)
    (args : List UInt64) (len : args.length = func.params) (releaseIndex : Nat)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (value : UInt64) (code : Wasm.Program) (next : State), LeanExe.Source.Scalar.Apply source [] args value ∧
      program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) = some code ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((functionState func args).toLocals []) env := by
  open LeanExe.Extract.Core in
  simp only [extractScalarFunc, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨arity, ha, body, hb, ir, hi, rfl⟩ := compiled
  have hlen : args.length = arity := len
  subst arity
  have supported := LeanExe.Extract.Core.extractScalarExpr_supported hi
  obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp)
  have applied := LeanExe.Source.Scalar.apply_of_collectLambdas args [] hb (by simpa using semantics)
  have irEval := LeanExe.Extract.Core.extractScalarExpr_correct semantics hi
    (LeanExe.Extract.Core.scalarArgumentLocals args [0])
  obtain ⟨descriptor, recognized⟩ := LeanExe.Extract.Core.extractScalarExpr_descriptor hi
  obtain ⟨code, next, emitted, executed⟩ := scalar_function_execution args name exportName
    releaseIndex recognized irEval m env store
  exact ⟨value, code, next, applied, emitted, executed⟩

end Project.Compiler.ScalarLowering
