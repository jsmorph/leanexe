import Project.LocalRegion.Syntax

namespace Project.LocalRegion
open Wasm

mutual
  def instructionDecidable (domain : Nat → Prop) (check : DecidablePred domain)
      (inst : Instruction) : Decidable (AllowsInstruction domain inst) := by
    cases inst with
    | localGet i | localSet i | localTee i => exact check i
    | block _ _ body _ _ | loop _ _ body _ _ =>
        exact programDecidable domain check body
    | iff _ _ yes no _ _ =>
        exact @instDecidableAnd _ _ (programDecidable domain check yes)
          (programDecidable domain check no)
    | _ => exact isTrue trivial

  def programDecidable (domain : Nat → Prop) (check : DecidablePred domain)
      (program : Program) : Decidable (AllowsProgram domain program) :=
    match program with
    | [] => isTrue trivial
    | inst :: rest =>
        @instDecidableAnd _ _ (instructionDecidable domain check inst)
          (programDecidable domain check rest)
end

instance [check : DecidablePred domain] (program : Program) :
    Decidable (AllowsProgram domain program) := programDecidable domain check program

end Project.LocalRegion
