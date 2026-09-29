import Project.Encoding.Modules
import Project.Encoding.Domain

namespace Wasm.Encoding

def Produces (result : Result relation value) (size : Nat) : Prop :=
  ∃ output, result = .ok output ∧ output.val.length = size

theorem u32_produces (value : Nat) (bound : value < 2 ^ 32) :
    Produces (u32 value) (Size.u32 value) := by
  simp only [Produces, u32, bound, dite_true]
  exact ⟨_, rfl, rfl⟩

theorem items_produces (encode : (value : α) → Result relation value)
    (size : α → Nat) (values : List α)
    (accepted : ∀ value ∈ values, Produces (encode value) (size value)) :
    Produces (items encode values) (values.map size).sum := by
  induction values with
  | nil => exact ⟨_, rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨first, hf, hfs⟩ := accepted head (by simp)
      obtain ⟨rest, hr, hrs⟩ := ih (fun value member => accepted value (by simp [member]))
      simp only [Produces, items, hf, hr]
      refine ⟨_, rfl, ?_⟩
      simp [hfs, hrs]

theorem vector_produces (encode : (value : α) → Result relation value)
    (size : α → Nat) (values : List α) (bound : values.length < 2 ^ 32)
    (accepted : ∀ value ∈ values, Produces (encode value) (size value)) :
    Produces (vector encode values) (Size.vector (values.map size)) := by
  obtain ⟨count, hc, hcs⟩ := u32_produces values.length bound
  obtain ⟨body, hb, hbs⟩ := items_produces encode size values accepted
  simp only [Produces, vector, hc, hb]
  refine ⟨_, rfl, ?_⟩
  simp [Size.vector, hcs, hbs]

theorem sized_produces (payload : Encoded relation value) (size : Nat)
    (length : payload.val.length = size) (bound : size < 2 ^ 32) :
    Produces (sized payload) (Size.u32 size + size) := by
  obtain ⟨count, hc, hcs⟩ := u32_produces payload.val.length (by omega)
  simp only [Produces, sized, hc]
  refine ⟨_, rfl, ?_⟩
  simp [hcs, length]

theorem section_produces (id : UInt8) (payload : Encoded relation value) (size : Nat)
    (length : payload.val.length = size) (bound : size < 2 ^ 32) :
    Produces (sectionBytes id payload) (1 + Size.u32 size + size) := by
  obtain ⟨count, hc, hcs⟩ := u32_produces payload.val.length (by omega)
  simp only [Produces, sectionBytes, hc]
  refine ⟨_, rfl, ?_⟩
  simp [hcs, length, Nat.add_comm, Nat.add_left_comm]

theorem name_produces (value : String) (bound : value.toUTF8.size < 2 ^ 32) :
    Produces (name value) (Size.name value) := by
  obtain ⟨count, hc, hcs⟩ := u32_produces value.toUTF8.size bound
  simp only [Produces, name, hc]
  refine ⟨_, rfl, ?_⟩
  simpa only [Size.name, List.length_append, Array.length_toList, ByteArray.size] using
    congrArg (fun n => n + value.toUTF8.data.size) hcs

theorem sum_const (values : List α) (n : Nat) :
    (values.map (fun _ => n)).sum = n * values.length := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem valueType_produces (type : Wasm.ValueType) (numeric : Numeric type) :
    Produces (valueType type) 1 := by
  rcases numeric with h | h | h | h <;> subst type <;> exact ⟨_, rfl, rfl⟩

theorem blockType_produces (types : List Wasm.ValueType) (form : BlockForm types) :
    Produces (blockType types) 1 := by
  cases form with
  | empty => exact ⟨_, rfl, rfl⟩
  | value type numeric =>
      obtain ⟨encoded, he, hes⟩ := valueType_produces type numeric
      simp only [Produces, blockType, he]
      exact ⟨_, rfl, hes⟩

theorem functionType_produces (type : Wasm.FuncType) (ready : TypeReady type) :
    Produces (functionType type) (Size.functionType type) := by
  obtain ⟨parameters, hp, hps⟩ := vector_produces valueType (fun _ => 1) type.params
    ready.paramCount (fun t member => valueType_produces t (ready.params t member))
  obtain ⟨results, hr, hrs⟩ := vector_produces valueType (fun _ => 1) type.results
    ready.resultCount (fun t member => valueType_produces t (ready.results t member))
  simp only [Produces, functionType, hp, hr]
  refine ⟨_, rfl, ?_⟩
  simp only [List.length_cons, List.length_append, hps, hrs, Size.functionType,
    Size.vector, List.length_map, sum_const, Nat.one_mul]
  omega

end Wasm.Encoding
