import Project.ProofKit.BlockLoop
import Interpreter.Wasm.Wp.Atomic

namespace Project.Core

open Wasm

/-- A finite execution of a native loop. The state and body relation can include
data, recursive calls and observable effects. -/
inductive WhileTrace (condition : σ → Bool → Prop) (body : σ → σ → Prop) :
    σ → σ → Nat → Prop where
  | done (tested : condition current false) :
      WhileTrace condition body current current 0
  | step (tested : condition current true) (executed : body current next)
      (rest : WhileTrace condition body next final count) :
      WhileTrace condition body current final (count + 1)

/-- Both arguments are unrestricted Talos instruction sequences. -/
def whileProgram (conditionCode bodyCode : Wasm.Program) : Wasm.Program :=
  [.block 0 0 [.loop 0 0
    (conditionCode ++ [.eqz, .br_if 1] ++ bodyCode ++ [.br 0])]]

/-- Compile a finite native loop execution compositionally. The condition and
body contracts allow representation-preserving changes to memory and locals;
the body can contain nested loops, recursive calls and host calls. -/
theorem WhileTrace.program_spec
    {condition : σ → Bool → Prop} {body : σ → σ → Prop}
    {initial final : σ} {count : Nat}
    (trace : WhileTrace condition body initial final count)
    (module_ : Wasm.Module) (env : HostEnv α)
    (Represents : σ → Store α → Locals → Prop)
    (conditionCode bodyCode : Wasm.Program)
    (conditionCorrect : ∀ source flag, condition source flag → ∀ store frame,
      Represents source store frame → frame.values = [] →
      ∀ (rest : Wasm.Program) (Q : Assertion α),
        (∀ nextStore nextFrame,
          Represents source nextStore nextFrame → nextFrame.values = [] →
          wp module_ rest Q nextStore
            { nextFrame with values := [.i32 (if flag then 1 else 0)] } env) →
        wp module_ (conditionCode ++ rest) Q store frame env)
    (bodyCorrect : ∀ source next, body source next →
      ∀ store frame, Represents source store frame → frame.values = [] →
      ∀ (rest : Wasm.Program) (Q : Assertion α),
        (∀ nextStore nextFrame,
          Represents next nextStore nextFrame → nextFrame.values = [] →
          wp module_ rest Q nextStore nextFrame env) →
        wp module_ (bodyCode ++ rest) Q store frame env)
    (store : Store α) (frame : Locals)
    (represented : Represents initial store frame) (empty : frame.values = [])
    (rest : Wasm.Program) (Q : Assertion α)
    (next : ∀ finalStore finalFrame,
      Represents final finalStore finalFrame → finalFrame.values = [] →
      wp module_ rest Q finalStore finalFrame env) :
    wp module_ (whileProgram conditionCode bodyCode ++ rest) Q store frame env := by
  classical
  let Witness := fun (currentStore : Store α) (currentFrame : Locals) (n : Nat) =>
    ∃ source, Represents source currentStore currentFrame ∧
      WhileTrace condition body source final n
  let Inv : AssertionF α := fun currentStore currentFrame =>
    currentFrame.values = [] ∧ ∃ n, Witness currentStore currentFrame n
  let Done : AssertionF α := fun finalStore finalFrame =>
    finalFrame.values = [] ∧ Represents final finalStore finalFrame
  let measure := fun currentStore currentFrame =>
    if h : ∃ n, Witness currentStore currentFrame n then Nat.find h else 0
  unfold whileProgram
  refine Project.ProofKit.BlockLoop.program_spec module_ env store frame
    (conditionCode ++ [Instruction.eqz, Instruction.br_if 1] ++ bodyCode ++
      [Instruction.br 0]) Inv Done measure ?_ ?_ ?_ ?_ Q rest ?_
  · intro _ _ h
    exact h.1
  · intro _ _ h
    exact h.1
  · exact ⟨empty, count, initial, represented, trace⟩
  · intro currentStore currentFrame invariant
    rcases invariant with ⟨currentEmpty, remaining⟩
    obtain ⟨source, sourceRep, selected⟩ := Nat.find_spec remaining
    generalize countEq : Nat.find remaining = selectedCount at selected
    simp only [List.append_assoc]
    cases selected with
    | done tested =>
      apply conditionCorrect _ false tested currentStore currentFrame sourceRep currentEmpty
      intro checkedStore checkedFrame checkedRep checkedEmpty
      have checkedFrameEq : ({ checkedFrame with values := [] } : Locals) = checkedFrame :=
        Project.ProofKit.Frame.ext _ _ rfl rfl checkedEmpty.symm
      simpa [wp_simp, Project.ProofKit.BlockLoop.stepPost, checkedFrameEq] using
        (show Done checkedStore checkedFrame from ⟨checkedEmpty, checkedRep⟩)
    | step tested executed tail =>
      apply conditionCorrect _ true tested currentStore currentFrame sourceRep currentEmpty
      intro checkedStore checkedFrame checkedRep checkedEmpty
      have checkedFrameEq : ({ checkedFrame with values := [] } : Locals) = checkedFrame :=
        Project.ProofKit.Frame.ext _ _ rfl rfl checkedEmpty.symm
      simp [wp_simp, checkedFrameEq]
      apply bodyCorrect _ _ executed checkedStore checkedFrame checkedRep checkedEmpty
      intro bodyStore bodyFrame bodyRep bodyEmpty
      simp only [wp_br_cons, Project.ProofKit.BlockLoop.stepPost]
      have bodyRemaining : ∃ n, Witness bodyStore bodyFrame n :=
        ⟨_, _, bodyRep, tail⟩
      refine ⟨⟨bodyEmpty, bodyRemaining⟩, ?_⟩
      have bound := Nat.find_min' bodyRemaining (show Witness bodyStore bodyFrame _ from
        ⟨_, bodyRep, tail⟩)
      simp only [measure, dite_eq_left bodyRemaining, dite_eq_left remaining, countEq]
      omega
  · intro finalStore finalFrame finished
    exact next finalStore finalFrame finished.2 finished.1

end Project.Core
