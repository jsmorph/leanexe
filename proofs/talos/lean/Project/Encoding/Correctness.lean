import Project.Encoding.Completeness.Modules
import Project.Encoding.Spec.Validity

namespace Wasm.Encoding

def ValidBinary (bytes : ByteArray) : Prop :=
  ∃ m, Encodes m bytes ∧ Spec.Validity.Module m

def Represents (property : Wasm.Module → Prop) (bytes : ByteArray) : Prop :=
  ∃ m, Encodes m bytes ∧ property m

theorem encode_valid (m : Wasm.Module) (bytes : ByteArray)
    (valid : Spec.Validity.Module m) (success : encode m = .ok bytes) :
    ValidBinary bytes :=
  ⟨m, encode_correct m bytes success, valid⟩

theorem encode_valid_complete (m : Wasm.Module) (ready : Ready m)
    (valid : Spec.Validity.Module m) :
    ∃ bytes, encode m = .ok bytes ∧ Encodes m bytes ∧ ValidBinary bytes := by
  obtain ⟨bytes, success, encoding⟩ := encode_complete m ready
  exact ⟨bytes, success, encoding, encode_valid m bytes valid success⟩

theorem encode_behavior (property : Wasm.Module → Prop) (m : Wasm.Module)
    (ready : Ready m) (valid : Spec.Validity.Module m) (behavior : property m) :
    ∃ bytes, encode m = .ok bytes ∧ Encodes m bytes ∧ ValidBinary bytes ∧
      Represents property bytes := by
  obtain ⟨bytes, success, encoding, binaryValid⟩ := encode_valid_complete m ready valid
  exact ⟨bytes, success, encoding, binaryValid, m, encoding, behavior⟩

end Wasm.Encoding
