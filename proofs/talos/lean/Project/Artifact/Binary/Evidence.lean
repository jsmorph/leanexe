import Project.Artifact.Binary.Translate

namespace Wasm.Binary

theorem ok_exists_of_toOption_isSome {value : Except ε α}
    (h : value.toOption.isSome = true) :
    ∃ result, value = .ok result := by
  cases value with
  | error error =>
      change false = true at h
      contradiction
  | ok result => exact ⟨result, rfl⟩

def verifiedModule? (bytes : ByteArray) : Option Wasm.Module := do
  let raw ← (decode bytes).toOption
  let validated ← (validate raw).toOption
  pure validated.toTalos

theorem evidenceOfIsSome (bytes : ByteArray)
    (evidence : (verifiedModule? bytes).isSome = true) :
    ∃ raw validated,
      decode bytes = .ok raw ∧
      validate raw = .ok validated ∧
      verifiedModule? bytes = some validated.toTalos := by
  unfold verifiedModule? at evidence ⊢
  cases hdecode : decode bytes with
  | error error =>
      rw [hdecode] at evidence
      simp [Except.toOption] at evidence
  | ok raw =>
      rw [hdecode] at evidence
      cases hvalidate : validate raw with
      | error error =>
          simp [Except.toOption, hvalidate] at evidence
      | ok validated =>
          refine ⟨raw, validated, rfl, hvalidate, ?_⟩
          simp [Except.toOption, hvalidate]

end Wasm.Binary
