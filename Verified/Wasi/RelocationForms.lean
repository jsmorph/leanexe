import Verified.Wasi.PureInstructionsBasic

namespace Verified.Wasi.Relocation

open Wasm

mutual
  theorem instruction_form (bound : Nat) (hBound : bound + 3 ≤ 2 ^ 32)
      {inst : Instruction} (hForm : Encoding.InstructionForm inst)
      (hClosed : instructionClosed bound inst = true) :
      Encoding.InstructionForm (instruction inst) := by
    by_cases hAtomic : PureTransport.atomic inst = true
    · rw [PureTransport.relocate_atomic hForm hAtomic]
      exact hForm
    · cases hForm with
      | call index hIndex32 =>
          have hIndex : index < bound := of_decide_eq_true
            (by simpa only [instructionClosed] using hClosed)
          exact .call (3 + index) (by omega)
      | block types body hTypes hBody =>
          exact .block types (program body) hTypes (program_form bound hBound hBody hClosed)
      | loop types body hTypes hBody =>
          exact .loop types (program body) hTypes (program_form bound hBound hBody hClosed)
      | iff types yes no hTypes hYes hNo =>
          simp only [instructionClosed, Bool.and_eq_true] at hClosed
          exact .iff types (program yes) (program no) hTypes
            (program_form bound hBound hYes hClosed.1)
            (program_form bound hBound hNo hClosed.2)
      | _ => simp [PureTransport.atomic] at hAtomic

  theorem program_form (bound : Nat) (hBound : bound + 3 ≤ 2 ^ 32)
      {code : Program} (hForm : Encoding.ProgramForm code)
      (hClosed : programClosed bound code = true) : Encoding.ProgramForm (program code) := by
    cases hForm with
    | nil => exact .nil
    | cons head tail hHead hTail =>
        simp only [programClosed, Bool.and_eq_true] at hClosed
        exact .cons (instruction head) (program tail)
          (instruction_form bound hBound hHead hClosed.1)
          (program_form bound hBound hTail hClosed.2)
end

end Verified.Wasi.Relocation
