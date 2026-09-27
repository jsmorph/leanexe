import Project.Encoding.Types
import Project.Encoding.Spec.Instructions

namespace Wasm.Encoding

def indexInstruction (opcode : UInt8) (make : Nat → Wasm.Instruction)
    (rule : Spec.IndexOp opcode make) (index : Nat) : Result Spec.Instr (make index) := do
  let immediate ← u32 index
  pure ⟨opcode :: immediate.val, .index _ _ _ _ rule immediate.property⟩

def memoryInstruction (opcode : UInt8) (alignment : Nat) (make : UInt32 → Wasm.Instruction)
    (rule : Spec.MemoryOp opcode alignment make) (offset : UInt32) :
    Result Spec.Instr (make offset) := do
  let immediate ← u32 offset.toNat
  let zero := unsigned_correct 32 0 (by decide) (by decide)
  pure ⟨opcode :: (unsigned 32 0 ++ immediate.val),
    .memory _ _ _ _ _ rule (.intro _ _ 0 _ zero (Nat.zero_le _) immediate.property)⟩

mutual
  def instruction (instr : Wasm.Instruction) : Result Spec.Instr instr :=
    match instr with
    | .unreachable => .ok ⟨[0x00], .plain _ _ .unreachable⟩
    | .nop => .ok ⟨[0x01], .plain _ _ .nop⟩
    | .ret => .ok ⟨[0x0f], .plain _ _ .ret⟩
    | .drop => .ok ⟨[0x1a], .plain _ _ .drop⟩
    | .eqz => .ok ⟨[0x45], .plain _ _ .eqz⟩
    | .eq => .ok ⟨[0x46], .plain _ _ .eq⟩
    | .ltU => .ok ⟨[0x49], .plain _ _ .ltU⟩
    | .gtU => .ok ⟨[0x4b], .plain _ _ .gtU⟩
    | .leU => .ok ⟨[0x4d], .plain _ _ .leU⟩
    | .geU => .ok ⟨[0x4f], .plain _ _ .geU⟩
    | .eqzI64 => .ok ⟨[0x50], .plain _ _ .eqzI64⟩
    | .eqI64 => .ok ⟨[0x51], .plain _ _ .eqI64⟩
    | .neI64 => .ok ⟨[0x52], .plain _ _ .neI64⟩
    | .ltUI64 => .ok ⟨[0x54], .plain _ _ .ltUI64⟩
    | .leUI64 => .ok ⟨[0x58], .plain _ _ .leUI64⟩
    | .geUI64 => .ok ⟨[0x5a], .plain _ _ .geUI64⟩
    | .add => .ok ⟨[0x6a], .plain _ _ .add⟩
    | .and => .ok ⟨[0x71], .plain _ _ .and⟩
    | .addI64 => .ok ⟨[0x7c], .plain _ _ .addI64⟩
    | .subI64 => .ok ⟨[0x7d], .plain _ _ .subI64⟩
    | .mulI64 => .ok ⟨[0x7e], .plain _ _ .mulI64⟩
    | .divUI64 => .ok ⟨[0x80], .plain _ _ .divUI64⟩
    | .remUI64 => .ok ⟨[0x82], .plain _ _ .remUI64⟩
    | .andI64 => .ok ⟨[0x83], .plain _ _ .andI64⟩
    | .orI64 => .ok ⟨[0x84], .plain _ _ .orI64⟩
    | .xorI64 => .ok ⟨[0x85], .plain _ _ .xorI64⟩
    | .shlI64 => .ok ⟨[0x86], .plain _ _ .shlI64⟩
    | .shrUI64 => .ok ⟨[0x88], .plain _ _ .shrUI64⟩
    | .f32Nearest => .ok ⟨[0x90], .plain _ _ .f32Nearest⟩
    | .f32Sqrt => .ok ⟨[0x91], .plain _ _ .f32Sqrt⟩
    | .f32Add => .ok ⟨[0x92], .plain _ _ .f32Add⟩
    | .f32Sub => .ok ⟨[0x93], .plain _ _ .f32Sub⟩
    | .f32Mul => .ok ⟨[0x94], .plain _ _ .f32Mul⟩
    | .f32Div => .ok ⟨[0x95], .plain _ _ .f32Div⟩
    | .f64Sqrt => .ok ⟨[0x9f], .plain _ _ .f64Sqrt⟩
    | .f64Add => .ok ⟨[0xa0], .plain _ _ .f64Add⟩
    | .f64Sub => .ok ⟨[0xa1], .plain _ _ .f64Sub⟩
    | .f64Mul => .ok ⟨[0xa2], .plain _ _ .f64Mul⟩
    | .f64Div => .ok ⟨[0xa3], .plain _ _ .f64Div⟩
    | .wrapI64 => .ok ⟨[0xa7], .plain _ _ .wrapI64⟩
    | .extendUI32 => .ok ⟨[0xad], .plain _ _ .extendUI32⟩
    | .f32ConvertI32S => .ok ⟨[0xb2], .plain _ _ .f32ConvertI32S⟩
    | .f32DemoteF64 => .ok ⟨[0xb6], .plain _ _ .f32DemoteF64⟩
    | .f64PromoteF32 => .ok ⟨[0xbb], .plain _ _ .f64PromoteF32⟩
    | .i32ReinterpretF32 => .ok ⟨[0xbc], .plain _ _ .i32ReinterpretF32⟩
    | .i64ReinterpretF64 => .ok ⟨[0xbd], .plain _ _ .i64ReinterpretF64⟩
    | .f32ReinterpretI32 => .ok ⟨[0xbe], .plain _ _ .f32ReinterpretI32⟩
    | .f64ReinterpretI64 => .ok ⟨[0xbf], .plain _ _ .f64ReinterpretI64⟩
    | .extend8S => .ok ⟨[0xc0], .plain _ _ .extend8S⟩
    | .i32TruncSatF32S => .ok ⟨[0xfc, 0x00], .plain _ _ .i32TruncSatF32S⟩
    | .memorySize => .ok ⟨[0x3f, 0x00], .plain _ _ .memorySize⟩
    | .memoryGrow => .ok ⟨[0x40, 0x00], .plain _ _ .memoryGrow⟩
    | .br index => indexInstruction 0x0c .br .br index
    | .br_if index => indexInstruction 0x0d .br_if .br_if index
    | .call index => indexInstruction 0x10 .call .call index
    | .localGet index => indexInstruction 0x20 .localGet .localGet index
    | .localSet index => indexInstruction 0x21 .localSet .localSet index
    | .localTee index => indexInstruction 0x22 .localTee .localTee index
    | .globalGet index => indexInstruction 0x23 .globalGet .globalGet index
    | .globalSet index => indexInstruction 0x24 .globalSet .globalSet index
    | .load32 offset => memoryInstruction 0x28 2 .load32 .load32 offset
    | .load64 offset => memoryInstruction 0x29 3 .load64 .load64 offset
    | .load8U offset => memoryInstruction 0x2d 0 .load8U .load8U offset
    | .store32 offset => memoryInstruction 0x36 2 .store32 .store32 offset
    | .store64 offset => memoryInstruction 0x37 3 .store64 .store64 offset
    | .store8 offset => memoryInstruction 0x3a 0 .store8 .store8 offset
    | .const value =>
        let encoded := signed32 value
        .ok ⟨0x41 :: encoded.val, .const32 _ _ encoded.property⟩
    | .constI64 value =>
        let encoded := signed64 value
        .ok ⟨0x42 :: encoded.val, .const64 _ _ encoded.property⟩
    | .block 0 count body [] types =>
        if arity : count = types.length then do
          let typeBytes ← blockType types
          let bodyBytes ← program body
          pure ⟨0x02 :: (typeBytes.val ++ bodyBytes.val ++ [0x0b]), by
            simpa only [arity] using Spec.Instr.block _ _ _ _ typeBytes.property bodyBytes.property⟩
        else .error "block arity disagrees with its type annotation"
    | .loop 0 count body [] types =>
        if arity : count = types.length then do
          let typeBytes ← blockType types
          let bodyBytes ← program body
          pure ⟨0x03 :: (typeBytes.val ++ bodyBytes.val ++ [0x0b]), by
            simpa only [arity] using Spec.Instr.loop _ _ _ _ typeBytes.property bodyBytes.property⟩
        else .error "block arity disagrees with its type annotation"
    | .iff 0 count thenBody elseBody [] types =>
        if arity : count = types.length then do
          let typeBytes ← blockType types
          let thenBytes ← program thenBody
          let elseBytes ← program elseBody
          pure ⟨0x04 :: (typeBytes.val ++ thenBytes.val ++ 0x05 :: elseBytes.val ++ [0x0b]), by
            simpa only [arity] using Spec.Instr.iff _ _ _ _ _ _
              typeBytes.property thenBytes.property elseBytes.property⟩
        else .error "if arity disagrees with its type annotation"
    | _ => .error "instruction is outside LeanExe's emitted WASM"
  termination_by sizeOf instr

  def program (code : Wasm.Program) : Result Spec.Instrs code :=
    match code with
    | [] => .ok ⟨[], .nil⟩
    | head :: tail => do
        let first ← instruction head
        let rest ← program tail
        pure ⟨first.val ++ rest.val, .cons _ _ _ _ first.property rest.property⟩
  termination_by sizeOf code
end

end Wasm.Encoding
