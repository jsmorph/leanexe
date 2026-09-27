import Project.Encoding

namespace Wasm.Encoding.Examples

def constant : Wasm.Module :=
  { funcs := [{ body := [.constI64 42], results := [.i64], typeIdx := some 0 }]
    types := [{ results := [.i64] }]
    gcTypes := [{ comp := .func { results := [.i64] } }]
    exports := [{ name := "answer", funcIdx := 0 }] }

theorem constant_ready : Ready constant := by
  refine {
    shape := by constructor <;> rfl
    types := ?_
    imports := by simp [constant]
    functions := ?_
    memories := by simp [constant]
    globals := by simp [constant]
    exports := ?_
    typeCount := by decide
    importCount := by decide
    functionCount := by decide
    globalCount := by decide
    exportCount := by decide
    typeSize := by decide
    importSize := by decide
    functionSize := by decide
    memorySize := by decide
    globalSize := by decide
    exportSize := by decide
    codeSize := by decide }
  · intro type member
    simp only [constant, List.mem_singleton] at member
    subst type
    exact ⟨by simp, by simp [Numeric], by decide, by decide⟩
  · intro func member
    simp only [constant, List.mem_singleton] at member
    subst func
    exact {
      typeIndex := ⟨0, rfl, rfl, by decide⟩
      locals := by simp
      localCount := by decide
      body := .cons _ _ (.const64 42) .nil
      bodySize := by decide }
  · intro entry member
    simp only [constant, Spec.exports, List.map, List.append_nil, List.mem_singleton] at member
    subst entry
    exact ⟨Or.inl rfl, by decide, by decide⟩

theorem constant_valid : Spec.Validity.Module constant := by
  refine {
    shape := by constructor <;> rfl
    types := ?_
    imports := by simp [constant]
    functions := ?_
    memories := by simp [constant]
    globals := by simp [constant]
    functionCount := by decide
    functionExports := by simp [constant]
    globalExports := by simp [constant]
    memoryExports := by simp [constant]
    distinctExports := by decide }
  · simp [constant, Spec.Validity.Types, Numeric]
  · intro func member
    simp only [constant, List.mem_singleton] at member
    subst func
    refine ⟨⟨0, rfl, rfl⟩, by simp [Spec.Validity.Types], by decide, ?_⟩
    exact .cons (.const64 42) (.nil (by simp [Spec.Validity.Types, Numeric]))

theorem constant_encoding :
    ∃ bytes, encode constant = .ok bytes ∧ Encodes constant bytes ∧ ValidBinary bytes :=
  encode_valid_complete constant constant_ready constant_valid

end Wasm.Encoding.Examples
