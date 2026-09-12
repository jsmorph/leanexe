import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Project.ProofKit.Frame

namespace Project.ProofKit.BlockLoop
open Wasm

def stepPost (Inv Done : AssertionF α) (measure : Store α → Locals → Nat)
    (bound : Nat) : Assertion α
  | .Break 0 store frame => Inv store frame ∧ measure store frame < bound
  | .Break 1 store frame => Done store frame
  | _ => False

theorem program_spec (module_ : Wasm.Module) (env : HostEnv α)
    (store : Store α) (frame : Locals) (body : Wasm.Program)
    (Inv Done : AssertionF α) (measure : Store α → Locals → Nat)
    (hValues : ∀ store frame, Inv store frame → frame.values = [])
    (hDoneValues : ∀ store frame, Done store frame → frame.values = [])
    (hInit : Inv store frame)
    (hStep : ∀ store frame, Inv store frame →
      wp module_ body (stepPost Inv Done measure (measure store frame)) store frame env)
    (Q : Assertion α) (rest : Wasm.Program)
    (hNext : ∀ store frame, Done store frame → wp module_ rest Q store frame env) :
    wp module_ ([.block 0 0 [.loop 0 0 body]] ++ rest) Q store frame env := by
  have hEntryValues := hValues store frame hInit
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons Inv measure hInit
  intro current currentFrame hCurrent
  have hCurrentValues := hValues current currentFrame hCurrent
  refine wp.conseq ?_ (hStep current currentFrame hCurrent)
  intro cont hPost
  cases cont with
  | Break depth final resultFrame =>
    cases depth with
    | zero =>
      have hResultValues := hValues final resultFrame hPost.1
      have hTrim : ({ resultFrame with values := [] } : Locals) = resultFrame :=
        Frame.ext _ _ rfl rfl hResultValues.symm
      simpa only [stepPost, List.take_zero, List.drop_zero, List.nil_append, hCurrentValues, hTrim]
        using hPost
    | succ depth =>
      cases depth with
      | zero =>
        have hResultValues := hDoneValues final resultFrame hPost
        have hTrim : ({ resultFrame with values := [] } : Locals) = resultFrame :=
          Frame.ext _ _ rfl rfl hResultValues.symm
        simpa only [List.take_zero, List.drop_zero, List.nil_append, hEntryValues, hTrim]
          using hNext final resultFrame hPost
      | succ depth => exact False.elim hPost
  | _ => exact False.elim hPost

#print axioms program_spec

end Project.ProofKit.BlockLoop
