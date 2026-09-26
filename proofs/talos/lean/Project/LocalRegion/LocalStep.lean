import Project.LocalRegion.Relation

namespace Project.LocalRegion
open Wasm

theorem localGet_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hi : domain i)
    (env : HostEnv α) (m : Module) (st : Store α) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.localGet i) env)
      (execOne (fuel + 1) m st target (.localGet (rename i)) env) := by
  simp only [execOne.eq_def]
  rw [← mapping.get hRelated i hi, ← mapping.values hRelated]
  cases source.get i with
  | none => exact .invalid _
  | some value => exact .fallthrough (mapping.stack hRelated _)

theorem localSet_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hi : domain i)
    (env : HostEnv α) (m : Module) (st : Store α) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.localSet i) env)
      (execOne (fuel + 1) m st target (.localSet (rename i)) env) := by
  simp only [execOne.eq_def]
  rw [← mapping.values hRelated]
  cases source.values with
  | nil => exact .invalid _
  | cons value values =>
      simp only
      have hSet := mapping.set hRelated i hi value
      cases hSource : source.set? i value with
      | none =>
          cases hTarget : target.set? (rename i) value with
          | none => exact .invalid _
          | some next => simp only [hSource, hTarget] at hSet
      | some nextSource =>
          cases hTarget : target.set? (rename i) value with
          | none => simp only [hSource, hTarget] at hSet
          | some nextTarget =>
              simp only [hSource, hTarget] at hSet
              exact .fallthrough (mapping.stack hSet values)

theorem localTee_step (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hi : domain i)
    (env : HostEnv α) (m : Module) (st : Store α) :
    ContinuationRel Related
      (execOne (fuel + 1) m st source (.localTee i) env)
      (execOne (fuel + 1) m st target (.localTee (rename i)) env) := by
  simp only [execOne.eq_def]
  rw [← mapping.values hRelated]
  cases source.values with
  | nil => exact .invalid _
  | cons value values =>
      simp only
      have hSet := mapping.set hRelated i hi value
      cases hSource : source.set? i value with
      | none =>
          cases hTarget : target.set? (rename i) value with
          | none => exact .invalid _
          | some next => simp only [hSource, hTarget] at hSet
      | some nextSource =>
          cases hTarget : target.set? (rename i) value with
          | none => simp only [hSource, hTarget] at hSet
          | some nextTarget =>
              simp only [hSource, hTarget] at hSet
              exact .fallthrough hSet

end Project.LocalRegion
