import Interpreter.Wasm.Semantics.Lemmas
import Interpreter.Wasm.Wp.Defs

namespace Project.Compiler.ControlAnnotations

open Wasm

mutual
  /-- Programs may differ only in static structured-control type annotations.
  Arities, instructions, and branch bodies are otherwise preserved. -/
  inductive InstructionEq : Instruction → Instruction → Prop where
    | refl : InstructionEq instruction instruction
    | block (body : ProgramEq a b) :
        InstructionEq (.block ps rs a pts rts) (.block ps rs b pts' rts')
    | loop (body : ProgramEq a b) :
        InstructionEq (.loop ps rs a pts rts) (.loop ps rs b pts' rts')
    | iff (thn : ProgramEq a b) (els : ProgramEq c d) :
        InstructionEq (.iff ps rs a c pts rts) (.iff ps rs b d pts' rts')

  inductive ProgramEq : Program → Program → Prop where
    | nil : ProgramEq [] []
    | cons (head : InstructionEq a b) (tail : ProgramEq as bs) :
        ProgramEq (a :: as) (b :: bs)
end

private theorem program_of_instruction (fuel : Nat)
    (instructions : ∀ {a b}, InstructionEq a b → ∀ (m : Module) (st : Store α)
      (s : Locals) (env : HostEnv α), execOne fuel m st s a env = execOne fuel m st s b env)
    {a b : Program} (h : ProgramEq a b) (m : Module) (st : Store α) (s : Locals)
    (env : HostEnv α) : exec fuel m st s a env = exec fuel m st s b env := by
  induction a generalizing b st s with
  | nil => cases h; rfl
  | cons head tail ih =>
    cases h with
    | cons headEq tailEq =>
      rw [exec, exec, instructions headEq]
      split
      · exact ih tailEq _ _
      · rfl


theorem execution_eq (fuel : Nat) :
    (∀ {a b}, InstructionEq a b → ∀ (m : Module) (st : Store α) (s : Locals) (env : HostEnv α),
      execOne fuel m st s a env = execOne fuel m st s b env) ∧
    (∀ {a b}, ProgramEq a b → ∀ (m : Module) (st : Store α) (s : Locals) (env : HostEnv α),
      exec fuel m st s a env = exec fuel m st s b env) := by
  induction fuel with
  | zero =>
    have instructions : ∀ {a b}, InstructionEq a b → ∀ (m : Module) (st : Store α)
        (s : Locals) (env : HostEnv α), execOne 0 m st s a env = execOne 0 m st s b env := by
      intros
      simp only [execOne.eq_def]
    exact ⟨instructions, fun h m st s env => program_of_instruction 0 instructions h m st s env⟩
  | succ fuel ih =>
    have instructions : ∀ {a b}, InstructionEq a b → ∀ (m : Module) (st : Store α)
        (s : Locals) (env : HostEnv α),
        execOne (fuel + 1) m st s a env = execOne (fuel + 1) m st s b env := by
      intro a b h m st s env
      cases h with
      | refl => rfl
      | block body =>
        simp only [execOne.eq_def]
        rw [ih.2 body]
      | loop body =>
        simp only [execOne_loop_succ]
        rw [ih.2 body]
        split <;> try rfl
        exact ih.1 (.loop body) m _ _ env
      | iff thn els =>
        simp only [execOne.eq_def]
        cases s.values with
        | nil => rfl
        | cons v vs =>
          cases v with
          | i32 n =>
            by_cases hn : n ≠ 0
            · simp only [if_pos hn]
              rw [ih.2 thn]
            · simp only [if_neg hn]
              rw [ih.2 els]
          | _ => rfl
    exact ⟨instructions, fun h m st s env => program_of_instruction _ instructions h m st s env⟩

theorem ProgramEq.wp_iff {a b : Program} (h : ProgramEq a b)
    (m : Module) (st : Store α) (s : Locals) (env : HostEnv α) (Q : Assertion α) :
    wp m a Q st s env ↔ wp m b Q st s env :=
  wp_of_exec_eq_succ (fun fuel => (execution_eq (fuel + 1)).2 h m st s env)

end Project.Compiler.ControlAnnotations
