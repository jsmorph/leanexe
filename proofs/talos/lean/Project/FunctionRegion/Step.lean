import Project.FunctionRegion.Syntax
import Interpreter.Wasm.Semantics.Lemmas

/-!
# One renamed instruction step

The successor-fuel instruction theorem consumes lower-fuel simulations for
nested programs, loop restarts, and direct calls.  Module-independent atomic
instructions reduce by definition.
Memory size and growth use the required memory-declaration equality.
-/

namespace Project.FunctionRegion

open Wasm

theorem execOne_succ
    (hMemory : source.memory = target.memory)
    (hOne : ∀ (env : HostEnv α) st s inst,
      PortableInstruction domain inst →
      execOne fuel target st s (renameInstruction rename inst) env =
        execOne fuel source st s inst env)
    (hExec : ∀ (env : HostEnv α) st s program,
      PortableProgram domain program →
      exec fuel target st s (renameProgram rename program) env =
        exec fuel source st s program env)
    (hRun : ∀ (env : HostEnv α) st args id,
      domain id →
      run fuel target (rename id) st args env =
        run fuel source id st args env)
    (env : HostEnv α) (st : Store α) (s : Locals) (inst : Instruction)
    (hPortable : PortableInstruction domain inst) :
    execOne (fuel + 1) target st s (renameInstruction rename inst) env =
      execOne (fuel + 1) source st s inst env := by
  cases hPortable with
  | localGet => simp only [renameInstruction, execOne.eq_def]
  | localSet => simp only [renameInstruction, execOne.eq_def]
  | globalGet => simp only [renameInstruction, execOne.eq_def]
  | globalSet => simp only [renameInstruction, execOne.eq_def]
  | const32 => simp only [renameInstruction, execOne.eq_def]
  | const64 => simp only [renameInstruction, execOne.eq_def]
  | eqI32 => simp only [renameInstruction, execOne.eq_def]
  | addI64 => simp only [renameInstruction, execOne.eq_def]
  | subI64 => simp only [renameInstruction, execOne.eq_def]
  | mulI64 => simp only [renameInstruction, execOne.eq_def]
  | divUI64 => simp only [renameInstruction, execOne.eq_def]
  | eqI64 => simp only [renameInstruction, execOne.eq_def]
  | neI64 => simp only [renameInstruction, execOne.eq_def]
  | eqz => simp only [renameInstruction, execOne.eq_def]
  | leUI64 => simp only [renameInstruction, execOne.eq_def]
  | ltUI64 => simp only [renameInstruction, execOne.eq_def]
  | geUI64 => simp only [renameInstruction, execOne.eq_def]
  | wrapI64 => simp only [renameInstruction, execOne.eq_def]
  | extendUI32 => simp only [renameInstruction, execOne.eq_def]
  | load64 => simp only [renameInstruction, execOne.eq_def]
  | store64 => simp only [renameInstruction, execOne.eq_def]
  | memorySize =>
      simp only [renameInstruction, execOne.eq_def, Module.memIs64]
      rw [hMemory]
  | memoryGrow =>
      simp only [renameInstruction, execOne.eq_def, Module.memoryCap]
      rw [hMemory]
  | unreachable => simp only [renameInstruction, execOne.eq_def]
  | br => simp only [renameInstruction, execOne.eq_def]
  | brIf => simp only [renameInstruction, execOne.eq_def]
  | block params results body hBody =>
      simp only [renameInstruction, execOne.eq_def]
      rw [hExec env st s body hBody]
  | loop params results body hBody =>
      simp only [renameInstruction, execOne_loop_succ]
      rw [hExec env st s body hBody]
      generalize hResult : exec fuel source st s body env = result
      cases result with
      | Break label st' s' =>
          cases label with
          | zero =>
              exact hOne env st'
                { s' with
                  values := s'.values.take params ++ s.values.drop params }
                (.loop params results body) (.loop params results body hBody)
          | succ label => rfl
      | _ => rfl
  | branch params results thenBody elseBody hThen hElse =>
      simp only [renameInstruction, execOne.eq_def]
      cases hValues : s.values with
      | nil => rfl
      | cons value values =>
          cases value with
          | i32 condition =>
              by_cases hCondition : condition ≠ 0
              · simp only [if_pos hCondition]
                rw [hExec env st { s with values := values } thenBody hThen]
              · simp only [if_neg hCondition]
                rw [hExec env st { s with values := values } elseBody hElse]
          | _ => rfl
  | call id hDomain =>
      simp only [renameInstruction, execOne.eq_def]
      rw [hRun env st s.values id hDomain]

end Project.FunctionRegion
