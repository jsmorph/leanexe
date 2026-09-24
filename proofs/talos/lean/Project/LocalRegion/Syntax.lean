import Project.FunctionRegion.Syntax

namespace Project.LocalRegion
open Wasm

mutual
  def renameInstruction (rename : Nat → Nat) : Instruction → Instruction
    | .localGet i => .localGet (rename i)
    | .localSet i => .localSet (rename i)
    | .localTee i => .localTee (rename i)
    | .block params results body paramTypes resultTypes =>
        .block params results (renameProgram rename body) paramTypes resultTypes
    | .loop params results body paramTypes resultTypes =>
        .loop params results (renameProgram rename body) paramTypes resultTypes
    | .iff params results yes no paramTypes resultTypes =>
        .iff params results (renameProgram rename yes) (renameProgram rename no)
          paramTypes resultTypes
    | inst => inst

  def renameProgram (rename : Nat → Nat) : Program → Program
    | [] => []
    | inst :: rest => renameInstruction rename inst :: renameProgram rename rest
end

mutual
  def AllowsInstruction (domain : Nat → Prop) : Instruction → Prop
    | .localGet i | .localSet i | .localTee i => domain i
    | .block _ _ body _ _ | .loop _ _ body _ _ => AllowsProgram domain body
    | .iff _ _ yes no _ _ => AllowsProgram domain yes ∧ AllowsProgram domain no
    | _ => True

  def AllowsProgram (domain : Nat → Prop) : Program → Prop
    | [] => True
    | inst :: rest => AllowsInstruction domain inst ∧ AllowsProgram domain rest
end

end Project.LocalRegion
