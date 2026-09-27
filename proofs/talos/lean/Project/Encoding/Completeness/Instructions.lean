import Project.Encoding.Completeness.Basic

namespace Wasm.Encoding

theorem indexInstruction_produces (opcode : UInt8) (make : Nat → Wasm.Instruction)
    (rule : Spec.IndexOp opcode make) (index : Nat) (bound : index < 2 ^ 32) :
    Produces (indexInstruction opcode make rule index) (1 + Size.u32 index) := by
  obtain ⟨encoded, he, hes⟩ := u32_produces index bound
  simp only [Produces, indexInstruction, he]
  refine ⟨_, rfl, ?_⟩
  simp [hes, Nat.add_comm]

theorem memoryInstruction_produces (opcode : UInt8) (alignment : Nat)
    (make : UInt32 → Wasm.Instruction) (rule : Spec.MemoryOp opcode alignment make)
    (offset : UInt32) :
    Produces (memoryInstruction opcode alignment make rule offset) (2 + Size.u32 offset.toNat) := by
  obtain ⟨encoded, he, hes⟩ := u32_produces offset.toNat offset.toNat_lt
  simp only [Produces, memoryInstruction, he]
  refine ⟨_, rfl, ?_⟩
  simp only [List.length_cons, List.length_append, hes,
    show (unsigned 32 0).length = 1 from rfl]
  omega

mutual
  theorem instruction_produces (instr : Wasm.Instruction) (form : InstructionForm instr) :
      Produces (instruction instr) (Size.instruction instr) := by
    cases form with
    | unreachable | nop | ret | drop | eqz | eq
    | ltU | gtU | leU | geU | eqzI64 | eqI64
    | neI64 | ltUI64 | leUI64 | geUI64 | add | and
    | addI64 | subI64 | mulI64 | divUI64 | remUI64 | andI64
    | orI64 | xorI64 | shlI64 | shrUI64 | f32Nearest | f32Sqrt
    | f32Add | f32Sub | f32Mul | f32Div | f64Sqrt | f64Add
    | f64Sub | f64Mul | f64Div | wrapI64 | extendUI32 | f32ConvertI32S
    | f32DemoteF64 | f64PromoteF32 | i32ReinterpretF32
    | i64ReinterpretF64 | f32ReinterpretI32 | f64ReinterpretI64
    | extend8S | i32TruncSatF32S | memorySize | memoryGrow =>
        simp only [Produces, instruction, Size.instruction]
        exact ⟨_, rfl, rfl⟩
    | br index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x0c .br .br index bound
    | br_if index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x0d .br_if .br_if index bound
    | call index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x10 .call .call index bound
    | localGet index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x20 .localGet .localGet index bound
    | localSet index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x21 .localSet .localSet index bound
    | localTee index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x22 .localTee .localTee index bound
    | globalGet index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x23 .globalGet .globalGet index bound
    | globalSet index bound =>
        simpa only [instruction, Size.instruction] using
          indexInstruction_produces 0x24 .globalSet .globalSet index bound
    | load32 offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x28 2 .load32 .load32 offset
    | load64 offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x29 3 .load64 .load64 offset
    | load8U offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x2d 0 .load8U .load8U offset
    | store32 offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x36 2 .store32 .store32 offset
    | store64 offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x37 3 .store64 .store64 offset
    | store8 offset =>
        simpa only [instruction, Size.instruction] using
          memoryInstruction_produces 0x3a 0 .store8 .store8 offset
    | const32 value =>
        simp only [Produces, instruction]
        refine ⟨_, rfl, ?_⟩
        simp [signed32, Size.instruction, Size.s32, Nat.add_comm]
    | const64 value =>
        simp only [Produces, instruction]
        refine ⟨_, rfl, ?_⟩
        simp [signed64, Size.instruction, Size.s64, Nat.add_comm]
    | block types body typeForm bodyForm =>
        obtain ⟨typeBytes, ht, hts⟩ := blockType_produces types typeForm
        obtain ⟨bodyBytes, hb, hbs⟩ := program_produces body bodyForm
        simp only [Produces, instruction, ht, hb]
        refine ⟨_, rfl, ?_⟩
        simp only [List.length_cons, List.length_append, List.length_nil, hts, hbs,
          Size.instruction]
        omega
    | loop types body typeForm bodyForm =>
        obtain ⟨typeBytes, ht, hts⟩ := blockType_produces types typeForm
        obtain ⟨bodyBytes, hb, hbs⟩ := program_produces body bodyForm
        simp only [Produces, instruction, ht, hb]
        refine ⟨_, rfl, ?_⟩
        simp only [List.length_cons, List.length_append, List.length_nil, hts, hbs,
          Size.instruction]
        omega
    | iff types thenBody elseBody typeForm thenForm elseForm =>
        obtain ⟨typeBytes, ht, hts⟩ := blockType_produces types typeForm
        obtain ⟨thenBytes, hthen, hthens⟩ := program_produces thenBody thenForm
        obtain ⟨elseBytes, helse, helses⟩ := program_produces elseBody elseForm
        simp only [Produces, instruction, ht, hthen, helse]
        refine ⟨_, rfl, ?_⟩
        simp only [List.length_cons, List.length_append, List.length_nil, hts, hthens,
          helses, Size.instruction]
        omega
  termination_by sizeOf instr

  theorem program_produces (code : Wasm.Program) (form : ProgramForm code) :
      Produces (program code) (Size.program code) := by
    cases form with
    | nil =>
        simp only [Produces, program, Size.program]
        exact ⟨_, rfl, rfl⟩
    | cons head tail headForm tailForm =>
        obtain ⟨first, hf, hfs⟩ := instruction_produces head headForm
        obtain ⟨rest, hr, hrs⟩ := program_produces tail tailForm
        simp only [Produces, program, hf, hr]
        refine ⟨_, rfl, ?_⟩
        simp [hfs, hrs, Size.program]
  termination_by sizeOf code
end

end Wasm.Encoding
