import LeanExe.Encoding.Completeness.Instructions
import LeanExe.Encoding.DecodeCorrect.Basic

namespace Wasm.Encoding

theorem Spec.ValType.numeric {bytes : Spec.Bytes} {type : Wasm.ValueType}
    (encoding : Spec.ValType bytes type) : Numeric type := by
  cases encoding <;> simp [Numeric]

theorem Spec.BlockType.form {bytes : Spec.Bytes} {types : List Wasm.ValueType}
    (encoding : Spec.BlockType bytes types) : BlockForm types := by
  cases encoding with
  | empty => exact .empty
  | value bytes type encoding => exact .value type encoding.numeric

theorem Spec.Plain.form {bytes : Spec.Bytes} {instruction : Wasm.Instruction}
    (encoding : Spec.Plain bytes instruction) : InstructionForm instruction := by
  cases encoding <;> constructor

theorem Spec.IndexOp.form {opcode : UInt8} {make : Nat → Wasm.Instruction}
    (rule : Spec.IndexOp opcode make) (index : Nat) (bound : index < 2 ^ 32) :
    InstructionForm (make index) := by
  cases rule <;> constructor <;> exact bound

theorem Spec.MemoryOp.form {opcode : UInt8} {alignment : Nat} {make : UInt32 → Wasm.Instruction}
    (rule : Spec.MemoryOp opcode alignment make) (offset : UInt32) : InstructionForm (make offset) := by
  cases rule <;> constructor

mutual

theorem InstructionForm.of_spec {bytes : Spec.Bytes} {instruction : Wasm.Instruction}
    (encoding : Spec.Instr bytes instruction) : InstructionForm instruction := by
  cases encoding with
  | plain bytes instruction rule => exact rule.form
  | index opcode make index bytes rule immediate => exact rule.form index (Decoder.unsigned_lt immediate)
  | memory opcode alignment make offset bytes rule immediate => exact rule.form offset
  | const32 bytes value immediate => exact .const32 value
  | const64 bytes value immediate => exact .const64 value
  | constF64 value => exact .constF64 value
  | constF32 value => exact .constF32 value
  | block typeBytes bodyBytes types body typeEncoding bodyEncoding =>
    exact .block types body typeEncoding.form (ProgramForm.of_spec bodyEncoding)
  | loop typeBytes bodyBytes types body typeEncoding bodyEncoding =>
    exact .loop types body typeEncoding.form (ProgramForm.of_spec bodyEncoding)
  | iff typeBytes thenBytes elseBytes types yes no typeEncoding yesEncoding noEncoding =>
    exact .iff types yes no typeEncoding.form (ProgramForm.of_spec yesEncoding) (ProgramForm.of_spec noEncoding)

theorem ProgramForm.of_spec {bytes : Spec.Bytes} {code : Wasm.Program}
    (encoding : Spec.Instrs bytes code) : ProgramForm code := by
  cases encoding with
  | nil => exact .nil
  | cons headBytes tailBytes head tail first rest =>
    exact .cons head tail (InstructionForm.of_spec first) (ProgramForm.of_spec rest)

end

def checkInstructionForm (instruction : Wasm.Instruction) : Bool :=
  match Wasm.Encoding.instruction instruction with
  | .ok _ => true
  | .error _ => false

def checkProgramForm (code : Wasm.Program) : Bool :=
  match Wasm.Encoding.program code with
  | .ok _ => true
  | .error _ => false

theorem checkInstructionForm_sound {instruction : Wasm.Instruction}
    (accepted : checkInstructionForm instruction = true) : InstructionForm instruction := by
  cases result : Wasm.Encoding.instruction instruction with
  | error message => simp only [checkInstructionForm, result, Bool.false_eq_true] at accepted
  | ok output => exact InstructionForm.of_spec output.property

theorem checkProgramForm_sound {code : Wasm.Program}
    (accepted : checkProgramForm code = true) : ProgramForm code := by
  cases result : Wasm.Encoding.program code with
  | error message => simp only [checkProgramForm, result, Bool.false_eq_true] at accepted
  | ok output => exact ProgramForm.of_spec output.property

theorem checkInstructionForm_complete {instruction : Wasm.Instruction} (form : InstructionForm instruction) :
    checkInstructionForm instruction = true := by
  obtain ⟨output, result, size⟩ := instruction_produces instruction form
  simp only [checkInstructionForm, result]

theorem checkProgramForm_complete {code : Wasm.Program} (form : ProgramForm code) :
    checkProgramForm code = true := by
  obtain ⟨output, result, size⟩ := program_produces code form
  simp only [checkProgramForm, result]

end Wasm.Encoding
