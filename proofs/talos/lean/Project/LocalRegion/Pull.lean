import Project.LocalRegion.Slots

namespace Project.LocalRegion
open Wasm

def SlotMap.pull (mapping : SlotMap rename domain) (target : Locals) : Locals :=
  { params := List.ofFn fun i : Fin mapping.sourceLayout.params =>
      (target.get (rename i.val)).getD (.i64 0)
    locals := List.ofFn fun i : Fin mapping.sourceLayout.locals =>
      (target.get (rename (mapping.sourceLayout.params + i.val))).getD (.i64 0)
    values := target.values }

theorem SlotMap.pull_fits (mapping : SlotMap rename domain) (target : Locals) :
    mapping.sourceLayout.Fits (mapping.pull target) := by
  simp [Layout.Fits, SlotMap.pull]

private theorem get_exists (frame : Locals) (i : Nat)
    (hBound : i < frame.params.length + frame.locals.length) :
    ∃ value, frame.get i = some value := by
  unfold Locals.get
  split
  · exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨by assumption, rfl⟩⟩
  · exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩

theorem SlotMap.pull_get (mapping : SlotMap rename domain) (target : Locals)
    (hFits : mapping.targetLayout.Fits target) (i : Nat) (hi : domain i) :
    (mapping.pull target).get i = target.get (rename i) := by
  have hSource := mapping.sourceBound i hi
  have hTarget : rename i < target.params.length + target.locals.length := by
    rw [hFits.1, hFits.2]
    exact mapping.targetBound i hi
  obtain ⟨value, hValue⟩ := get_exists target (rename i) hTarget
  unfold Locals.get at hValue
  by_cases hParam : i < mapping.sourceLayout.params
  · simp [Locals.get, SlotMap.pull, hParam, hValue]
  · have hLocal : i - mapping.sourceLayout.params < mapping.sourceLayout.locals := by omega
    have hIndex : mapping.sourceLayout.params + (i - mapping.sourceLayout.params) = i := by omega
    simp [Locals.get, SlotMap.pull, hParam, hSource, hLocal, hIndex, hValue]

theorem SlotMap.pull_related (mapping : SlotMap rename domain) (target : Locals)
    (hFits : mapping.targetLayout.Fits target) :
    mapping.Related (mapping.pull target) target :=
  ⟨mapping.pull_fits target, hFits, rfl, mapping.pull_get target hFits⟩

#print axioms SlotMap.pull_related
end Project.LocalRegion
