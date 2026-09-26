import Project.Compiler.ArithmeticEncoding
import Project.Compiler.ScalarLowering
import Project.Compiler.ControlAnnotations
import Project.Artifact.Binary.Translate

namespace Project.Compiler.ArithmeticEncoding

open Project.Compiler.ControlAnnotations

theorem uint64_signed_roundtrip (value : UInt64) :
    UInt64.ofInt value.toBitVec.toInt = value := by
  apply UInt64.toNat.inj
  change (value.toBitVec.toInt % 18446744073709551616).toNat % 18446744073709551616 = value.toNat
  have bound := value.toNat_lt
  have same : value.toBitVec.toNat = value.toNat := rfl
  simp only [BitVec.toInt_eq_toNat_cond, same]
  split <;> omega

theorem Atom.translation {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : Atom a b) :
    ∃ instruction, ScalarLowering.instruction a = some instruction ∧
      b.toTalos = [instruction] := by
  cases h with
  | get index bound =>
    exact ⟨.localGet index, by simp [ScalarLowering.instruction], by
      simp [Wasm.Binary.Instr.toTalos, UInt32.toNat_ofNat_of_lt' bound]⟩
  | set index bound =>
    exact ⟨.localSet index, by simp [ScalarLowering.instruction], by
      simp [Wasm.Binary.Instr.toTalos, UInt32.toNat_ofNat_of_lt' bound]⟩
  | br depth bound =>
    exact ⟨.br depth, by simp [ScalarLowering.instruction], by
      simp [Wasm.Binary.Instr.toTalos, UInt32.toNat_ofNat_of_lt' bound]⟩
  | brIf depth bound =>
    exact ⟨.br_if depth, by simp [ScalarLowering.instruction], by
      simp [Wasm.Binary.Instr.toTalos, UInt32.toNat_ofNat_of_lt' bound]⟩
  | const n =>
    exact ⟨.constI64 (UInt64.ofNat n), by simp [ScalarLowering.instruction], by
      simp [Wasm.Binary.Instr.toTalos, uint64_signed_roundtrip]⟩
  | _ => exact ⟨_, by simp [ScalarLowering.instruction], rfl⟩

theorem programEq_append {a b c d : Wasm.Program}
    (left : ProgramEq a b) (right : ProgramEq c d) : ProgramEq (a ++ c) (b ++ d) := by
  induction a generalizing b with
  | nil => cases left; exact right
  | cons head tail ih =>
    cases left with
    | cons eh et => exact .cons eh (ih et)

mutual
  theorem InstructionEncoding.translation {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
      (h : InstructionEncoding a b) :
      ∃ instruction, ScalarLowering.instruction a = some instruction ∧
        ProgramEq b.toTalos [instruction] := by
    cases h with
    | atom h =>
      obtain ⟨i, lowered, translated⟩ := h.translation
      exact ⟨i, lowered, translated ▸ .cons .refl .nil⟩
    | if64 left right =>
      obtain ⟨l, hl, el⟩ := left.translation
      obtain ⟨r, hr, er⟩ := right.translation
      refine ⟨.iff 0 1 l r, ?_, .cons (.iff el er) .nil⟩
      simp [ScalarLowering.instruction, hl, hr]
    | if0 left right =>
      obtain ⟨l, hl, el⟩ := left.translation
      obtain ⟨r, hr, er⟩ := right.translation
      refine ⟨.iff 0 0 l r, ?_, .cons (.iff el er) .nil⟩
      simp [ScalarLowering.instruction, hl, hr]
    | block0 body =>
      obtain ⟨b, hb, eb⟩ := body.translation
      refine ⟨.block 0 0 b, ?_, .cons (.block eb) .nil⟩
      simp [ScalarLowering.instruction, hb]
    | loop0 body =>
      obtain ⟨b, hb, eb⟩ := body.translation
      refine ⟨.loop 0 0 b, ?_, .cons (.loop eb) .nil⟩
      simp [ScalarLowering.instruction, hb]
  termination_by sizeOf a

  theorem ProgramEncoding.translation {a : List LeanExe.Wasm.Instr} {b : List Wasm.Binary.Instr}
      (h : ProgramEncoding a b) :
      ∃ code, ScalarLowering.program a = some code ∧
        ProgramEq (Wasm.Binary.Instr.listToTalos b) code := by
    cases h with
    | nil => exact ⟨[], by simp [ScalarLowering.program], .nil⟩
    | cons head tail =>
      obtain ⟨i, hi, ei⟩ := head.translation
      obtain ⟨r, hr, er⟩ := tail.translation
      refine ⟨i :: r, ?_, programEq_append ei er⟩
      simp [ScalarLowering.program, hi, hr]
  termination_by sizeOf a
end

end Project.Compiler.ArithmeticEncoding
