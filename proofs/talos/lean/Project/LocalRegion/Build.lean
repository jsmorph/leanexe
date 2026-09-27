import Project.LocalRegion.Layout

namespace Project.LocalRegion
open Wasm

def Layout.sourceFrame (layout : Layout slots domain) (target : Locals) : Locals :=
  { params := List.ofFn (fun i : Fin layout.sourceParams =>
      (target.get (slots i.val)).getD (.i64 0))
    locals := List.ofFn (fun i : Fin layout.sourceLocals =>
      (target.get (slots (layout.sourceParams + i.val))).getD (.i64 0))
    values := target.values }

theorem get_some_getD (s : Locals) (i : Nat)
    (h : i < s.params.length + s.locals.length) :
    some ((s.get i).getD (.i64 0)) = s.get i := by
  unfold Locals.get
  by_cases hp : i < s.params.length
  · simp [hp]
  · simp [hp, h, show i - s.params.length < s.locals.length by omega]

theorem Layout.sourceFrame_get (layout : Layout slots domain) (target : Locals)
    (i : Nat) (hi : domain i)
    (hParams : target.params.length = layout.targetParams)
    (hLocals : target.locals.length = layout.targetLocals) :
    (layout.sourceFrame target).get i = target.get (slots i) := by
  have hSource := layout.sourceBound i hi
  have hTarget : slots i < target.params.length + target.locals.length := by
    rw [hParams, hLocals]
    exact layout.targetBound i hi
  unfold sourceFrame Locals.get
  simp only [List.length_ofFn]
  by_cases hp : i < layout.sourceParams
  · simp only [hp, ite_true, List.getElem?_ofFn]
    simp only [hp, dite_true]
    exact get_some_getD target (slots i) hTarget
  · have hl : i - layout.sourceParams < layout.sourceLocals := by omega
    simp only [hp, ite_false, hSource, ite_true, List.getElem?_ofFn, hl, dite_true]
    have hIndex : layout.sourceParams + (i - layout.sourceParams) = i := by omega
    rw [hIndex]
    exact get_some_getD target (slots i) hTarget

theorem Layout.sourceFrame_related (layout : Layout slots domain) (target : Locals)
    (hParams : target.params.length = layout.targetParams)
    (hLocals : target.locals.length = layout.targetLocals) :
    layout.Related (layout.sourceFrame target) target := by
  refine ⟨?_, ?_, hParams, hLocals, rfl, ?_⟩
  · simp [sourceFrame]
  · simp [sourceFrame]
  · intro i hi
    exact (layout.sourceFrame_get target i hi hParams hLocals).symm

#print axioms Layout.sourceFrame_related
end Project.LocalRegion
