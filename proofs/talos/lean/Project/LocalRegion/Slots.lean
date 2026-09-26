import Project.LocalRegion.Relation

namespace Project.LocalRegion
open Wasm

structure Layout where
  params : Nat
  locals : Nat

def Layout.Fits (layout : Layout) (frame : Locals) : Prop :=
  frame.params.length = layout.params ∧ frame.locals.length = layout.locals

structure SlotMap (rename : Nat → Nat) (domain : Nat → Prop) where
  sourceLayout : Layout
  targetLayout : Layout
  sourceBound : ∀ i, domain i → i < sourceLayout.params + sourceLayout.locals
  targetBound : ∀ i, domain i → rename i < targetLayout.params + targetLayout.locals
  injective : ∀ i j, domain i → domain j → rename i = rename j → i = j

def SlotMap.Related (mapping : SlotMap rename domain) (source target : Locals) : Prop :=
  mapping.sourceLayout.Fits source ∧ mapping.targetLayout.Fits target ∧
    source.values = target.values ∧ ∀ i, domain i → source.get i = target.get (rename i)

private theorem set_exists (frame : Locals) (i : Nat) (value : Value)
    (hi : i < frame.params.length + frame.locals.length) :
    ∃ next, frame.set? i value = some next := by
  unfold Locals.set?
  split
  · exact ⟨_, rfl⟩
  · exact ⟨{ frame with locals := frame.locals.set (i - frame.params.length) value },
      by simp [hi]⟩

private theorem set_fits {layout : Layout} {frame next : Locals} {i : Nat} {value : Value}
    (hFits : layout.Fits frame)
    (hSet : frame.set? i value = some next) : layout.Fits next := by
  unfold Locals.set? at hSet
  split at hSet
  · obtain rfl := Option.some.inj hSet
    simpa only [Layout.Fits, List.length_set] using hFits
  · split at hSet
    · obtain rfl := Option.some.inj hSet
      simpa only [Layout.Fits, List.length_set] using hFits
    · contradiction

private theorem set_values {frame next : Locals} {i : Nat} {value : Value}
    (hSet : frame.set? i value = some next) :
    next.values = frame.values := by
  unfold Locals.set? at hSet
  split at hSet
  · obtain rfl := Option.some.inj hSet
    rfl
  · split at hSet
    · obtain rfl := Option.some.inj hSet
      rfl
    · contradiction

private theorem get_set_same {frame next : Locals} {i : Nat} {value : Value}
    (hSet : frame.set? i value = some next) :
    next.get i = some value := by
  unfold Locals.set? at hSet
  split at hSet
  · obtain rfl := Option.some.inj hSet
    simp [Locals.get, *]
  · split at hSet
    · obtain rfl := Option.some.inj hSet
      have hi : i - frame.params.length < frame.locals.length := by omega
      simp [Locals.get, *]
    · contradiction

private theorem get_set_ne {frame next : Locals} {i j : Nat} {value : Value}
    (hNe : j ≠ i) (hSet : frame.set? i value = some next) :
    next.get j = frame.get j := by
  unfold Locals.set? at hSet
  split at hSet
  · obtain rfl := Option.some.inj hSet
    by_cases hRead : j < frame.params.length
    · simp only [Locals.get, List.length_set, if_pos hRead]
      rw [List.getElem?_set]
      simp [hNe.symm]
    · simp [Locals.get, hRead]
  · split at hSet
    · obtain rfl := Option.some.inj hSet
      by_cases hReadParam : j < frame.params.length
      · simp [Locals.get, hReadParam]
      · by_cases hRead : j < frame.params.length + frame.locals.length
        · have hLocalNe : j - frame.params.length ≠ i - frame.params.length := by omega
          simp only [Locals.get, List.length_set, hReadParam, hRead, if_false, if_true]
          rw [List.getElem?_set]
          simp [hLocalNe.symm]
        · simp [Locals.get, hReadParam, hRead]
    · contradiction

theorem SlotMap.frameMap (mapping : SlotMap rename domain) :
    FrameMap rename domain mapping.Related where
  values h := h.2.2.1
  stack h values := ⟨h.1, h.2.1, rfl, h.2.2.2⟩
  get h i hi := h.2.2.2 i hi
  set {source target} h i hi value := by
    have hSourceBound : i < source.params.length + source.locals.length := by
      rw [h.1.1, h.1.2]
      exact mapping.sourceBound i hi
    have hTargetBound : rename i < target.params.length + target.locals.length := by
      rw [h.2.1.1, h.2.1.2]
      exact mapping.targetBound i hi
    obtain ⟨nextSource, hSource⟩ := set_exists source i value hSourceBound
    obtain ⟨nextTarget, hTarget⟩ := set_exists target (rename i) value hTargetBound
    rw [hSource, hTarget]
    refine ⟨set_fits h.1 hSource, set_fits h.2.1 hTarget, ?_, ?_⟩
    · rw [set_values hSource, set_values hTarget]
      exact h.2.2.1
    · intro j hj
      by_cases hSame : j = i
      · subst j
        rw [get_set_same hSource, get_set_same hTarget]
      · have hRenamed : rename j ≠ rename i := fun hEq =>
          hSame (mapping.injective j i hj hi hEq)
        rw [get_set_ne hSame hSource, get_set_ne hRenamed hTarget]
        exact h.2.2.2 j hj

#print axioms SlotMap.frameMap
end Project.LocalRegion
