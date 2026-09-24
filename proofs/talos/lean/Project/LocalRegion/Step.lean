import Project.LocalRegion.LocalStep
import Project.LocalRegion.AtomicStep
import Project.LocalRegion.Control

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

theorem execOne_succ
    (mapping : FrameMap rename domain Related)
    (hOne : ∀ (env : HostEnv α) st source target inst,
      Related source target → PortableInstruction calls inst →
      AllowsInstruction domain inst →
      ContinuationRel Related (execOne fuel m st source inst env)
        (execOne fuel m st target (renameInstruction rename inst) env))
    (hExec : ∀ (env : HostEnv α) st source target program,
      Related source target → PortableProgram calls program →
      AllowsProgram domain program →
      ContinuationRel Related (exec fuel m st source program env)
        (exec fuel m st target (renameProgram rename program) env))
    (env : HostEnv α) (st : Store α) (source target : Locals) (inst : Instruction)
    (hRelated : Related source target) (hPortable : PortableInstruction calls inst)
    (hAllowed : AllowsInstruction domain inst) :
    ContinuationRel Related (execOne (fuel + 1) m st source inst env)
      (execOne (fuel + 1) m st target (renameInstruction rename inst) env) := by
  have hSaved := hPortable
  cases hPortable with
  | localGet i => exact localGet_step mapping hRelated hAllowed env m st
  | localSet i => exact localSet_step mapping hRelated hAllowed env m st
  | localTee i => exact localTee_step mapping hRelated hAllowed env m st
  | block params results body paramTypes resultTypes hBody =>
      exact block_step mapping hRelated
        (hExec env st source target body hRelated hBody hAllowed)
  | loop params results body paramTypes resultTypes hBody =>
      apply loop_step mapping hRelated
        (hExec env st source target body hRelated hBody hAllowed)
      intro nextStore nextSource nextTarget hNext
      exact hOne env nextStore nextSource nextTarget _ hNext hSaved hAllowed
  | branch params results yes no paramTypes resultTypes hYes hNo =>
      apply branch_step mapping hRelated
      · intro values
        exact hExec env st _ _ yes (mapping.stack hRelated values) hYes hAllowed.1
      · intro values
        exact hExec env st _ _ no (mapping.stack hRelated values) hNo hAllowed.2
  | _ =>
      simpa only [renameInstruction] using
        atomic_step mapping hRelated hSaved (by trivial) env m st

end Project.LocalRegion
