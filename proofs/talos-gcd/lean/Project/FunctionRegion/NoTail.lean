import Project.FunctionRegion.Syntax
import Interpreter.Wasm.Semantics.Lemmas

/-!
# Portable programs do not produce tail calls

The function-region syntax excludes the three tail-call instructions.  The
interpreter can therefore never return a `ReturnCall` continuation while it
executes a portable instruction or program.
The included store and memory operations complete as ordinary atomic steps.
-/

namespace Project.FunctionRegion

open Wasm

private def HasNoReturnCall : Continuation α → Prop
  | .ReturnCall _ _ _ => False
  | _ => True

macro "no_return_call_atomic" : tactic => `(tactic|
  (simp only [execOne.eq_def]
   repeat' (first | split | simp_all [HasNoReturnCall])))

private theorem noReturnCall_aux : ∀ fuel,
    (∀ (m : Module) (env : HostEnv α) st s inst,
      PortableInstruction domain inst →
      HasNoReturnCall (execOne fuel m st s inst env)) ∧
    (∀ (m : Module) (env : HostEnv α) st s program,
      PortableProgram domain program →
      HasNoReturnCall (exec fuel m st s program env)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro m env st s inst hPortable
        cases hPortable <;> no_return_call_atomic
      · intro m env st s program hPortable
        cases program with
        | nil => simp [HasNoReturnCall, exec]
        | cons inst rest => simp [HasNoReturnCall, exec, execOne.eq_def]
  | succ fuel ih =>
      obtain ⟨ihOne, ihExec⟩ := ih
      have noOne : ∀ (m : Module) (env : HostEnv α) st s inst,
          PortableInstruction domain inst →
          HasNoReturnCall (execOne (fuel + 1) m st s inst env) := by
        intro m env st s inst hPortable
        cases hPortable with
        | localGet => no_return_call_atomic
        | localSet => no_return_call_atomic
        | globalGet => no_return_call_atomic
        | globalSet => no_return_call_atomic
        | const32 => no_return_call_atomic
        | const64 => no_return_call_atomic
        | eqI32 => no_return_call_atomic
        | addI64 => no_return_call_atomic
        | subI64 => no_return_call_atomic
        | mulI64 => no_return_call_atomic
        | divUI64 => no_return_call_atomic
        | eqI64 => no_return_call_atomic
        | neI64 => no_return_call_atomic
        | eqz => no_return_call_atomic
        | leUI64 => no_return_call_atomic
        | ltUI64 => no_return_call_atomic
        | geUI64 => no_return_call_atomic
        | wrapI64 => no_return_call_atomic
        | extendUI32 => no_return_call_atomic
        | load64 => no_return_call_atomic
        | store64 => no_return_call_atomic
        | memorySize => no_return_call_atomic
        | memoryGrow => no_return_call_atomic
        | unreachable => no_return_call_atomic
        | br => no_return_call_atomic
        | brIf => no_return_call_atomic
        | block params results body hBody =>
            simp only [execOne.eq_def]
            have hNoReturn := ihExec m env st s body hBody
            cases hResult : exec fuel m st s body env <;>
              simp only [HasNoReturnCall]
            case Break label bodyStore bodyLocals =>
              cases label <;> trivial
            case ReturnCall =>
              rw [hResult] at hNoReturn
              exact hNoReturn
        | loop params results body hBody =>
            simp only [execOne_loop_succ]
            have hNoReturn := ihExec m env st s body hBody
            cases hResult : exec fuel m st s body env <;>
              simp only [HasNoReturnCall]
            case Break label bodyStore bodyLocals =>
              cases label with
              | zero =>
                  exact ihOne m env bodyStore
                    { bodyLocals with
                      values := bodyLocals.values.take params ++ s.values.drop params }
                    (.loop params results body) (.loop params results body hBody)
              | succ label => trivial
            case ReturnCall =>
              rw [hResult] at hNoReturn
              exact hNoReturn
        | branch params results thenBody elseBody hThen hElse =>
            simp only [execOne.eq_def]
            cases hValues : s.values with
            | nil => trivial
            | cons value rest =>
                cases value with
                | i32 condition =>
                    by_cases hCondition : condition ≠ 0
                    · simp only [if_pos hCondition]
                      have hNoReturn := ihExec m env st
                        { s with values := rest } thenBody hThen
                      cases hResult : exec fuel m st
                          { s with values := rest } thenBody env <;>
                        simp only [HasNoReturnCall]
                      case Break label bodyStore bodyLocals =>
                        cases label <;> trivial
                      case ReturnCall =>
                        rw [hResult] at hNoReturn
                        exact hNoReturn
                    · simp only [if_neg hCondition]
                      have hNoReturn := ihExec m env st
                        { s with values := rest } elseBody hElse
                      cases hResult : exec fuel m st
                          { s with values := rest } elseBody env <;>
                        simp only [HasNoReturnCall]
                      case Break label bodyStore bodyLocals =>
                        cases label <;> trivial
                      case ReturnCall =>
                        rw [hResult] at hNoReturn
                        exact hNoReturn
                | _ => trivial
        | call id hDomain =>
            simp only [execOne.eq_def]
            cases hResult : run fuel m id st s.values env <;>
              simp [HasNoReturnCall]
      refine ⟨noOne, ?_⟩
      intro m env st s program hPortable
      induction program generalizing st s with
      | nil => simp [HasNoReturnCall, exec]
      | cons inst rest restIH =>
          cases hPortable with
          | cons _ _ hInst hRest =>
              simp only [exec]
              cases hResult : execOne (fuel + 1) m st s inst env <;>
                simp_all only [HasNoReturnCall]
              case ReturnCall =>
                have hNoReturn := noOne m env st s inst hInst
                rw [hResult] at hNoReturn
                exact hNoReturn

theorem portableProgram_noReturnCall
    (hPortable : PortableProgram domain program) :
    ∀ id st' values,
      exec fuel m st s program env ≠ .ReturnCall id st' values := by
  have hNoReturn :=
    (noReturnCall_aux (domain := domain) fuel).2 m env st s program hPortable
  intro id st' values hResult
  rw [hResult] at hNoReturn
  exact hNoReturn

end Project.FunctionRegion
