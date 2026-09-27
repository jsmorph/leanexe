import Project.Core.Validity

namespace Project.Core.Validity

open Wasm.Encoding
open Wasm.Encoding.Spec.Validity

theorem program_form {context : Context} {code : Wasm.Program}
    {inputs outputs : List Wasm.ValueType}
    (typed : Program context code inputs outputs)
    (functions : context.functions.length < 2 ^ 32)
    (locals : context.locals.length < 2 ^ 32)
    (globals : context.globals.length < 2 ^ 32)
    (labels : context.labels.length + Size.program code < 2 ^ 32) :
    ProgramForm code := by
  revert functions locals globals labels
  induction typed using Program.rec
    (motive_1 := fun context instruction _ _ _ =>
      context.functions.length < 2 ^ 32 →
      context.locals.length < 2 ^ 32 →
      context.globals.length < 2 ^ 32 →
      context.labels.length + Size.instruction instruction < 2 ^ 32 →
      InstructionForm instruction) with
  | nop => intros; exact .nop
  | unreachable => intros; exact .unreachable
  | drop => intros; exact .drop
  | unary op => intros; cases op <;> constructor
  | binary op => intros; cases op <;> constructor
  | const32 value => intros; exact .const32 value
  | const64 value => intros; exact .const64 value
  | localGet index found =>
      rename_i functions locals globals labels
      exact .localGet index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 locals)
  | localSet index found =>
      rename_i functions locals globals labels
      exact .localSet index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 locals)
  | localTee index found =>
      rename_i functions locals globals labels
      exact .localTee index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 locals)
  | globalGet index found =>
      rename_i functions locals globals labels
      exact .globalGet index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 globals)
  | globalSet index found =>
      rename_i functions locals globals labels
      exact .globalSet index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 globals)
  | call index type found =>
      rename_i functions locals globals labels
      exact .call index (Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 functions)
  | load op offset => intros; cases op <;> constructor
  | store op offset => intros; cases op <;> constructor
  | memorySize => intros; exact .memorySize
  | memoryGrow => intros; exact .memoryGrow
  | block form body ih =>
      rename_i functions locals globals labels
      refine .block _ _ form (ih functions locals globals ?_)
      simp only [Size.instruction] at labels
      simp only [List.length_cons]
      omega
  | loop form body ih =>
      rename_i functions locals globals labels
      refine .loop _ _ form (ih functions locals globals ?_)
      simp only [Size.instruction] at labels
      simp only [List.length_cons]
      omega
  | iff form yes no ihYes ihNo =>
      rename_i functions locals globals labels
      refine .iff _ _ _ form (ihYes functions locals globals ?_) (ihNo functions locals globals ?_)
      all_goals
        simp only [Size.instruction] at labels
        simp only [List.length_cons]
        omega
  | br index found =>
      rename_i functions locals globals labels
      have bound := (List.getElem?_eq_some_iff.mp found).1
      exact .br index (by omega)
  | brIf index found =>
      rename_i functions locals globals labels
      have bound := (List.getElem?_eq_some_iff.mp found).1
      exact .br_if index (by omega)
  | ret => intros; exact .ret
  | frame typed stackTypes ih =>
      rename_i functions locals globals labels
      exact ih functions locals globals labels
  | nil => intros; exact .nil
  | cons head tail ihHead ihTail =>
      intro functions locals globals labels
      simp only [Size.program] at labels
      exact .cons _ _ (ihHead functions locals globals (by omega))
        (ihTail functions locals globals (by omega))

/-- These are finite numeric checks on a module and its computed encoded sizes.
They contain no execution or per-program semantic proof obligations. -/
def ReadyLimits (module_ : Wasm.Module) : Prop :=
  module_.types.length < 2 ^ 32 ∧
  (∀ type ∈ module_.types, type.params.length < 2 ^ 32 ∧ type.results.length < 2 ^ 32) ∧
  (∀ decl ∈ module_.imports,
    decl.module.toUTF8.size < 2 ^ 32 ∧ decl.name.toUTF8.size < 2 ^ 32) ∧
  (∀ func ∈ module_.funcs, Size.bodyPayload func < 2 ^ 32) ∧
  (∀ entry ∈ Spec.exports module_, entry.2.1.toUTF8.size < 2 ^ 32) ∧
  module_.globals.length < 2 ^ 32 ∧
  (Spec.exports module_).length < 2 ^ 32 ∧
  Size.vector (module_.types.map Size.functionType) < 2 ^ 32 ∧
  Size.vector (module_.imports.map (Size.importFunction module_.types)) < 2 ^ 32 ∧
  Size.vector (module_.funcs.map (fun f => Size.u32 (f.typeIdx.getD 0))) < 2 ^ 32 ∧
  Size.vector (module_.memory.toList.map Size.memory) < 2 ^ 32 ∧
  Size.vector (module_.globals.map Size.global) < 2 ^ 32 ∧
  Size.vector ((Spec.exports module_).map Size.exportEntry) < 2 ^ 32 ∧
  Size.vector (module_.funcs.map Size.functionBody) < 2 ^ 32

instance (module_ : Wasm.Module) : Decidable (ReadyLimits module_) := by
  unfold ReadyLimits
  infer_instance

theorem typeIndex_bound {signature : Wasm.FuncType} {types : List Wasm.FuncType}
    (member : signature ∈ types) : Size.typeIndex signature types < types.length := by
  induction types with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = signature
      · simp [Size.typeIndex, same]
      · have rest : signature ∈ tail := by simpa [List.mem_cons, Ne.symm same] using member
        simpa [Size.typeIndex, same] using Nat.succ_lt_succ (ih rest)

/-- A valid module within the format's finite size limits is accepted by the
verified encoder. Instruction eligibility follows from the typing proof. -/
theorem module_ready {module_ : Wasm.Module}
    (valid : Wasm.Encoding.Spec.Validity.Module module_)
    (limits : ReadyLimits module_) : Ready module_ := by
  rcases limits with ⟨typeCount, typeCounts, importNames, bodies, exportNames,
    globalCount, exportCount, typeSize, importSize, functionSize, memorySize,
    globalSize, exportSize, codeSize⟩
  have functionsBound := valid.functionCount
  refine {
    shape := valid.shape
    types := ?_
    imports := ?_
    functions := ?_
    memories := ?_
    globals := valid.globals
    exports := ?_
    typeCount := typeCount
    importCount := by omega
    functionCount := by omega
    globalCount := globalCount
    exportCount := exportCount
    typeSize := typeSize
    importSize := importSize
    functionSize := functionSize
    memorySize := memorySize
    globalSize := globalSize
    exportSize := exportSize
    codeSize := codeSize }
  · intro type member
    exact ⟨(valid.types type member).1, (valid.types type member).2,
      (typeCounts type member).1, (typeCounts type member).2⟩
  · intro decl member
    have signature := valid.imports decl member
    exact ⟨signature, Nat.lt_trans (typeIndex_bound signature) typeCount,
      (importNames decl member).1, (importNames decl member).2⟩
  · intro func member
    obtain ⟨⟨index, declared, found⟩, localTypes, localBound, typed⟩ := valid.functions func member
    have bodyBound := bodies func member
    refine ⟨⟨index, declared, found,
      Nat.lt_trans (List.getElem?_eq_some_iff.mp found).1 typeCount⟩,
      localTypes, by omega, ?_, bodyBound⟩
    apply program_form typed
    · simpa [functionContext, functionTypes] using functionsBound
    · simpa [functionContext] using localBound
    · simpa [functionContext, globalTypes] using globalCount
    · simp only [functionContext, List.length_singleton]
      simp only [Size.bodyPayload] at bodyBound
      omega
  · intro decl member
    have memory := valid.memories decl (by simpa using member)
    exact ⟨memory.2.1, memory.1⟩
  · intro entry member
    have name := exportNames entry member
    unfold Spec.exports at member
    rcases List.mem_append.mp member with first | memoryExport
    · rcases List.mem_append.mp first with functionExport | globalExport
      · obtain ⟨entryValue, exportMember, rfl⟩ := List.mem_map.mp functionExport
        exact ⟨Or.inl rfl, name, Nat.lt_trans (valid.functionExports entryValue exportMember) functionsBound⟩
      · obtain ⟨entryValue, exportMember, rfl⟩ := List.mem_map.mp globalExport
        exact ⟨Or.inr (Or.inr rfl), name,
          Nat.lt_trans (valid.globalExports entryValue exportMember) globalCount⟩
    · obtain ⟨entryValue, exportMember, rfl⟩ := List.mem_map.mp memoryExport
      have zero := (valid.memoryExports entryValue exportMember).1
      refine ⟨Or.inr (Or.inl rfl), name, ?_⟩
      change entryValue.2 < 2 ^ 32
      rw [zero]
      decide

end Project.Core.Validity
