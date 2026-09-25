import Project.LocalRegion.Syntax

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

mutual
  theorem portableInstruction_calls (inst : Instruction)
      (h : PortableInstruction calls inst) :
      PortableInstruction (fun _ => True)
        (FunctionRegion.renameInstruction rename inst) := by
    cases h with
    | block p r body pt rt hBody =>
        exact .block p r _ pt rt (portableProgram_calls body hBody)
    | loop p r body pt rt hBody =>
        exact .loop p r _ pt rt (portableProgram_calls body hBody)
    | branch p r yes no pt rt hYes hNo =>
        exact .branch p r _ _ pt rt
          (portableProgram_calls yes hYes) (portableProgram_calls no hNo)
    | call id _ => exact .call (rename id) trivial
    | _ => simp only [FunctionRegion.renameInstruction]; constructor

  theorem portableProgram_calls (program : Program)
      (h : PortableProgram calls program) :
      PortableProgram (fun _ => True)
        (FunctionRegion.renameProgram rename program) := by
    cases h with
    | nil => exact .nil
    | cons inst rest hInst hRest =>
        exact .cons _ _ (portableInstruction_calls inst hInst)
          (portableProgram_calls rest hRest)
end

mutual
  theorem allowsInstruction_calls (inst : Instruction)
      (h : AllowsInstruction domain inst) :
      AllowsInstruction domain (FunctionRegion.renameInstruction rename inst) := by
    cases inst with
    | block p r body pt rt => exact allowsProgram_calls body h
    | loop p r body pt rt => exact allowsProgram_calls body h
    | iff p r yes no pt rt =>
        exact ⟨allowsProgram_calls yes h.1, allowsProgram_calls no h.2⟩
    | _ => simpa only [FunctionRegion.renameInstruction, AllowsInstruction] using h

  theorem allowsProgram_calls (program : Program) (h : AllowsProgram domain program) :
      AllowsProgram domain (FunctionRegion.renameProgram rename program) := by
    cases program with
    | nil => trivial
    | cons inst rest =>
        exact ⟨allowsInstruction_calls inst h.1, allowsProgram_calls rest h.2⟩
end

end Project.LocalRegion
