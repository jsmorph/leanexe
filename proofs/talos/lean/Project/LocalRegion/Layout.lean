import Project.LocalRegion.Syntax
import Mathlib.Tactic

namespace Project.LocalRegion
open Wasm

def update (s : Locals) (i : Nat) (v : Value) : Locals :=
  if i < s.params.length then { s with params := s.params.set i v }
  else { s with locals := s.locals.set (i - s.params.length) v }

@[simp] theorem update_params_length :
    (update s i v).params.length = s.params.length := by
  simp [update]; split <;> simp

@[simp] theorem update_locals_length :
    (update s i v).locals.length = s.locals.length := by
  simp [update]; split <;> simp

@[simp] theorem update_values : (update s i v).values = s.values := by
  simp [update]; split <;> rfl

theorem set?_eq_update (h : i < s.params.length + s.locals.length) :
    s.set? i v = some (update s i v) := by
  simp only [Locals.set?, update, h, ite_true]
  split <;> rfl

theorem get_update (hi : i < s.params.length + s.locals.length)
    (hj : j < s.params.length + s.locals.length) :
    (update s i v).get j = if i = j then some v else s.get j := by
  by_cases hp : i < s.params.length <;> by_cases hq : j < s.params.length
  · simp only [update, hp, hq, ite_true, Locals.get, List.length_set]
    by_cases hij : i = j <;> simp [List.getElem_set, hq, hij]
  · simp only [update, hp, ite_true, Locals.get, List.length_set, hq, ite_false,
      hj, ite_true]
    simp [show i ≠ j by omega]
  · simp only [update, hp, ite_false, Locals.get, hq, ite_true]
    simp [show i ≠ j by omega]
  · simp only [update, hp, ite_false, Locals.get, hq, List.length_set, hj, ite_true]
    have hLocal : j - s.params.length < s.locals.length := by omega
    have hEq : i - s.params.length = j - s.params.length ↔ i = j := by omega
    by_cases hij : i = j <;> simp [List.getElem_set, hLocal, hEq, hij]

structure Layout (slots : Nat → Nat) (domain : Nat → Prop) where
  sourceParams : Nat
  sourceLocals : Nat
  targetParams : Nat
  targetLocals : Nat
  sourceBound : ∀ i, domain i → i < sourceParams + sourceLocals
  targetBound : ∀ i, domain i → slots i < targetParams + targetLocals
  injective : ∀ i j, domain i → domain j → slots i = slots j → i = j

structure Layout.Related (layout : Layout slots domain) (s t : Locals) : Prop where
  sourceParams : s.params.length = layout.sourceParams
  sourceLocals : s.locals.length = layout.sourceLocals
  targetParams : t.params.length = layout.targetParams
  targetLocals : t.locals.length = layout.targetLocals
  values : t.values = s.values
  reads : ∀ i, domain i → t.get (slots i) = s.get i

def Layout.frame (layout : Layout slots domain) : Frame slots domain where
  Related := layout.Related
  values h := h.values
  stack h values := ⟨h.sourceParams, h.sourceLocals, h.targetParams,
    h.targetLocals, rfl, h.reads⟩
  read h hi := h.reads _ hi
  write {s t i} h hi value := by
    have hSource : i < s.params.length + s.locals.length := by
      rw [h.sourceParams, h.sourceLocals]
      exact layout.sourceBound i hi
    have hTarget : slots i < t.params.length + t.locals.length := by
      rw [h.targetParams, h.targetLocals]
      exact layout.targetBound i hi
    rw [set?_eq_update hSource, set?_eq_update hTarget]
    apply Option.Rel.some
    refine ⟨by simpa using h.sourceParams, by simpa using h.sourceLocals,
      by simpa using h.targetParams, by simpa using h.targetLocals,
      by simpa using h.values, ?_⟩
    intro j hj
    have hSourceJ : j < s.params.length + s.locals.length := by
      rw [h.sourceParams, h.sourceLocals]
      exact layout.sourceBound j hj
    have hTargetJ : slots j < t.params.length + t.locals.length := by
      rw [h.targetParams, h.targetLocals]
      exact layout.targetBound j hj
    rw [get_update hSource hSourceJ, get_update hTarget hTargetJ]
    have hEq : slots i = slots j ↔ i = j :=
      ⟨layout.injective i j hi hj, congrArg slots⟩
    simp only [hEq, h.reads j hj]

/-- Updating corresponding live cells preserves the complete frame relation. -/
theorem Layout.update_related (layout : Layout slots domain)
    (h : layout.Related s t) (hi : domain i) (value : Value) :
    layout.Related (update s i value) (update t (slots i) value) := by
  have hSource : i < s.params.length + s.locals.length := by
    rw [h.sourceParams, h.sourceLocals]
    exact layout.sourceBound i hi
  have hTarget : slots i < t.params.length + t.locals.length := by
    rw [h.targetParams, h.targetLocals]
    exact layout.targetBound i hi
  have hWrite := layout.frame.write h hi value
  rw [set?_eq_update hSource, set?_eq_update hTarget] at hWrite
  cases hWrite
  assumption

#print axioms Layout.frame
end Project.LocalRegion
