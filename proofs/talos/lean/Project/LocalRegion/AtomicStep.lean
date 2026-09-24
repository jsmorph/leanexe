import Project.LocalRegion.Relation

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

def AtomicInstruction : Instruction → Prop
  | .localGet _ | .localSet _ | .localTee _ => False
  | .block .. | .loop .. | .iff .. => False
  | _ => True

set_option maxHeartbeats 800000 in
theorem atomic_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hPortable : PortableInstruction calls inst)
    (hAtomic : AtomicInstruction inst)
    (env : HostEnv α) (m : Module) (st : Store α) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source inst env)
      (execOne (fuel + 1) m st target inst env) := by
  cases hPortable <;> simp only [AtomicInstruction] at hAtomic
  all_goals
    simp only [execOne.eq_def, ← mapping.values hRelated]
    repeat' first
      | exact ContinuationRel.fallthrough (mapping.stack hRelated _)
      | exact ContinuationRel.fallthrough hRelated
      | exact ContinuationRel.break (mapping.stack hRelated _)
      | exact ContinuationRel.break hRelated
      | exact ContinuationRel.returned _ _
      | exact ContinuationRel.trap _ _
      | exact ContinuationRel.invalid _
      | exact ContinuationRel.outOfFuel
      | exact ContinuationRel.throwing hRelated
      | split

end Project.LocalRegion
