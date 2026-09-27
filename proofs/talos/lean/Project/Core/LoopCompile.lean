import Project.Core.Contract

namespace Project.Core

open LeanExe.Core
open LeanExe.Wasm.ScalarDescriptor (Cond)
open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

/-- The generic loop rule composes the condition compiler with certified body
executions, including bodies with recursive calls and further loops. -/
theorem loop_spec (context : Context σ α)
    {condition : Cond} {body : Stmt}
    {initial final : σ} {locals result : LeanExe.Core.Locals}
    (trace : LoopSpec context (.loop condition body) initial locals final result) :
    StatementSpec context (.loop condition body) initial locals final result := by
  obtain ⟨count, trace⟩ := trace
  intro scratch store state represented agree above fits room rest Q next
  simp only [width] at room
  let Represents := fun (source : σ × LeanExe.Core.Locals)
      (currentStore : Wasm.Store α) (currentFrame : Wasm.Locals) =>
    context.represents source.1 currentStore ∧
      Agrees source.2 (State.ofLocals currentFrame) ∧
      source.2.length = locals.length ∧
      capacity (State.ofLocals currentFrame) = capacity state
  change Wasm.wp context.target
    (whileProgram ((Project.Compiler.ScalarLowering.condition condition).program scratch)
      (statement context.target.imports.length context.effectCode scratch body) ++ rest)
    Q store (state.toLocals []) context.host
  refine trace.program_spec context.target context.host Represents
    ((Project.Compiler.ScalarLowering.condition condition).program scratch)
    (statement context.target.imports.length context.effectCode scratch body)
    ?_ ?_ store (state.toLocals []) ⟨represented, agree, rfl, rfl⟩ rfl rest Q ?_
  · intro source flag evaluated currentStore currentFrame currentRep currentEmpty
      continuation post afterCondition
    rcases currentRep with ⟨worldRep, localsAgree, sameLength, sameCapacity⟩
    obtain ⟨checked, computed, checkedAgree, checkedCapacity⟩ :=
      Project.Compiler.ScalarLowering.condition_eval condition scratch evaluated
        localsAgree (by omega) (by omega)
    have frameEq : (State.ofLocals currentFrame).toLocals [] = currentFrame :=
      Project.ProofKit.Frame.ext _ _ rfl rfl currentEmpty.symm
    rw [← frameEq]
    apply Project.ProofKit.ScalarTransition.Expr.program_spec
      (Project.Compiler.ScalarLowering.condition condition) scratch
      (State.ofLocals currentFrame) checked flag [] context.target context.host
      currentStore continuation post computed
    exact afterCondition currentStore (checked.toLocals [])
      ⟨worldRep, checkedAgree, sameLength, checkedCapacity.trans sameCapacity⟩ rfl
  · intro before after executed currentStore currentFrame currentRep currentEmpty
      continuation post afterBody
    rcases currentRep with ⟨worldRep, localsAgree, sameLength, sameCapacity⟩
    have frameEq : (State.ofLocals currentFrame).toLocals [] = currentFrame :=
      Project.ProofKit.Frame.ext _ _ rfl rfl currentEmpty.symm
    rw [← frameEq]
    apply executed.2 scratch currentStore (State.ofLocals currentFrame)
      worldRep localsAgree (by omega) (by omega) (by omega) continuation post
    intro bodyStore bodyState bodyRep bodyAgree bodyCapacity
    exact afterBody bodyStore (bodyState.toLocals [])
      ⟨bodyRep, bodyAgree, executed.1.trans sameLength,
        bodyCapacity.trans sameCapacity⟩ rfl
  · intro finalStore finalFrame finalRep finalEmpty
    rcases finalRep with ⟨worldRep, localsAgree, _, sameCapacity⟩
    have frameEq : (State.ofLocals finalFrame).toLocals [] = finalFrame :=
      Project.ProofKit.Frame.ext _ _ rfl rfl finalEmpty.symm
    simpa only [frameEq] using
      next finalStore (State.ofLocals finalFrame) worldRep localsAgree sameCapacity

end Project.Core
