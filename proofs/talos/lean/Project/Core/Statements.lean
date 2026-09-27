import Project.Core.Contract
import Project.Compiler.ScalarStatements

namespace Project.Core

open LeanExe.Core
open LeanExe.Wasm.ScalarDescriptor (Expr Cond)
open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

theorem skip_spec (context : Context σ α) (world : σ) (locals : LeanExe.Core.Locals) :
    StatementSpec context .skip world locals world locals := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  simpa only [statement, List.nil_append] using next store state represented agree rfl

theorem assign_spec {context : Context σ α} {world : σ}
    {locals result : LeanExe.Core.Locals} {destination : Nat} {expression : Expr}
    {value : UInt64} (evaluated : expression.eval locals = some value)
    (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
    StatementSpec context (.assign destination expression) world locals world result := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  obtain ⟨middle, computed, middleAgree, middleSize⟩ :=
    Project.Compiler.ScalarLowering.expression_eval expression scratch evaluated agree above room
  have bound : destination < locals.length := by
    unfold LeanExe.IR.ScalarStore.write at written
    split at written
    · assumption
    · contradiction
  obtain ⟨afterWrite, targetWrite, writeSize⟩ :=
    Project.Compiler.ScalarLowering.set_exists (state := middle) (index := destination)
      (.i64 value) (by omega)
  simp only [statement, List.append_assoc, List.singleton_append]
  apply Project.ProofKit.ScalarTransition.Expr.program_spec
    (Project.Compiler.ScalarLowering.expression expression) scratch state middle value []
    context.target context.host store (.localSet destination :: rest) Q computed
  apply Project.ProofKit.ScalarTransition.localSet_spec targetWrite
  exact next store afterWrite represented (middleAgree.store_write written targetWrite)
    (writeSize.trans middleSize)

theorem seq_spec {context : Context σ α} {a b : Stmt} {initial middle final : σ}
    {locals saved result : LeanExe.Core.Locals}
    (first : StatementSpec context a initial locals middle saved)
    (second : StatementSpec context b middle saved final result)
    (sameLength : saved.length = locals.length) :
    StatementSpec context (.seq a b) initial locals final result := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  simp only [width] at room
  rw [statement, List.append_assoc]
  apply first scratch store state represented agree above sourceRoom (by omega)
  intro middleStore middleState middleRep middleAgree middleSize
  apply second scratch middleStore middleState middleRep middleAgree (by omega) (by omega)
    (by omega)
  intro finalStore finalState finalRep finalAgree finalSize
  exact next finalStore finalState finalRep finalAgree (finalSize.trans middleSize)

theorem branch_yes_spec {context : Context σ α} {condition : Cond} {yes no : Stmt}
    {initial final : σ} {locals result : LeanExe.Core.Locals}
    (tested : condition.eval locals = some true)
    (body : StatementSpec context yes initial locals final result) :
    StatementSpec context (.branch condition yes no) initial locals final result := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  simp only [width] at room
  obtain ⟨checked, computed, checkedAgree, checkedSize⟩ :=
    Project.Compiler.ScalarLowering.condition_eval condition scratch tested agree above (by omega)
  simp only [statement, List.append_assoc, List.singleton_append]
  apply Project.ProofKit.ScalarTransition.Expr.program_spec
    (Project.Compiler.ScalarLowering.condition condition) scratch state checked true []
    context.target context.host store
    (.iff 0 0 (statement context.target.imports.length context.effectCode scratch yes)
      (statement context.target.imports.length context.effectCode scratch no) :: rest) Q computed
  refine Wasm.wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  rw [← List.append_nil (statement context.target.imports.length context.effectCode scratch yes)]
  apply body scratch store checked represented checkedAgree above (by omega) (by omega)
  intro finalStore finalState finalRep finalAgree finalSize
  simpa [wp_simp, State.toLocals] using
    next finalStore finalState finalRep finalAgree (finalSize.trans checkedSize)

theorem branch_no_spec {context : Context σ α} {condition : Cond} {yes no : Stmt}
    {initial final : σ} {locals result : LeanExe.Core.Locals}
    (tested : condition.eval locals = some false)
    (body : StatementSpec context no initial locals final result) :
    StatementSpec context (.branch condition yes no) initial locals final result := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  simp only [width] at room
  obtain ⟨checked, computed, checkedAgree, checkedSize⟩ :=
    Project.Compiler.ScalarLowering.condition_eval condition scratch tested agree above (by omega)
  simp only [statement, List.append_assoc, List.singleton_append]
  apply Project.ProofKit.ScalarTransition.Expr.program_spec
    (Project.Compiler.ScalarLowering.condition condition) scratch state checked false []
    context.target context.host store
    (.iff 0 0 (statement context.target.imports.length context.effectCode scratch yes)
      (statement context.target.imports.length context.effectCode scratch no) :: rest) Q computed
  refine Wasm.wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  rw [← List.append_nil (statement context.target.imports.length context.effectCode scratch no)]
  apply body scratch store checked represented checkedAgree above (by omega) (by omega)
  intro finalStore finalState finalRep finalAgree finalSize
  simpa [wp_simp, State.toLocals] using
    next finalStore finalState finalRep finalAgree (finalSize.trans checkedSize)

theorem effect_spec {context : Context σ α} {initial final : σ}
    {locals result : LeanExe.Core.Locals} {destination operation : Nat}
    {expressions : List Expr} {args : List UInt64} {value : UInt64}
    (inputs : LeanExe.Core.arguments expressions locals = some args)
    (performed : context.effects operation args initial value final)
    (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
    StatementSpec context (.effect destination operation expressions) initial locals final result := by
  intro scratch store state represented agree above sourceRoom room rest Q next
  obtain ⟨afterArguments, argsAgree, argsSize, argsSpec⟩ :=
    arguments_execution expressions scratch inputs agree above room []
      context.target context.host store
  have bound : destination < locals.length := by
    unfold LeanExe.IR.ScalarStore.write at written
    split at written
    · assumption
    · contradiction
  obtain ⟨afterWrite, targetWrite, writeSize⟩ :=
    Project.Compiler.ScalarLowering.set_exists (state := afterArguments) (index := destination)
      (.i64 value) (by omega)
  simp only [statement, List.append_assoc, List.singleton_append]
  apply argsSpec
  simp only [List.append_nil]
  apply context.effectCorrect operation args initial value final performed store afterArguments represented
  intro nextStore nextRep
  apply Project.ProofKit.ScalarTransition.localSet_spec targetWrite
  exact next nextStore afterWrite nextRep (argsAgree.store_write written targetWrite)
    (writeSize.trans argsSize)

end Project.Core
