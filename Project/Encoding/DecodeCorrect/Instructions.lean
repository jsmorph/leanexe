import Project.Encoding.DecodeCorrect.Types
import Project.Encoding.Spec.Instructions

namespace Wasm.Encoding.Decoder

open Wasm.Encoding.Spec

theorem parses_memArg {maxAlignment : Nat} {bytes : List UInt8} {offset : UInt32}
    (h : MemArg maxAlignment bytes offset) (small : maxAlignment ≤ 3) :
    Parses (memArg maxAlignment) bytes offset := by
  match h with
  | .intro alignBytes offsetBytes alignment offset alignEncoding alignBound offsetEncoding =>
      unfold memArg
      have hOffset := unsigned_lt offsetEncoding
      refine Parses.bind (parses_unsigned alignEncoding 32 (Nat.le_refl _)) ?_
      simp only [show ¬ 64 ≤ alignment by omega, ite_false]
      refine Parses.bind_nil (parses_unsigned offsetEncoding 64 (by decide)) ?_
      simp only [show ¬ maxAlignment < alignment by omega,
        show ¬ 4294967296 ≤ offset.toNat by omega, ite_false, UInt32.ofNat_toNat]
      exact Parses.pure' _

theorem parses_decodeOther_plain {opcode : UInt8} {instr : Instruction}
    (h : plain opcode = some instr) : Parses (instructions.decodeOther opcode) [] instr := by
  unfold instructions.decodeOther
  rw [h]
  exact Parses.pure' _

theorem parses_decodeOther_index {opcode : UInt8} {make : Nat → Instruction}
    {bytes : List UInt8} {n : Nat} (hPlain : plain opcode = none)
    (hIndex : index opcode = some make) (h : Unsigned 32 bytes n) :
    Parses (instructions.decodeOther opcode) bytes (make n) := by
  unfold instructions.decodeOther
  rw [hPlain, hIndex]
  exact Parses.bind_nil (parses_unsigned h 32 (Nat.le_refl _)) (Parses.pure' _)

theorem parses_decodeOther_memory {opcode : UInt8} {natural : Nat}
    {make : UInt32 → Instruction} {bytes : List UInt8} {offset : UInt32}
    (hPlain : plain opcode = none) (hIndex : index opcode = none)
    (hMemory : memory opcode = some (natural, make)) (h : MemArg natural bytes offset)
    (small : natural ≤ 3) :
    Parses (instructions.decodeOther opcode) bytes (make offset) := by
  unfold instructions.decodeOther
  rw [hPlain, hIndex, hMemory]
  exact Parses.bind_nil (parses_memArg h small) (Parses.pure' _)

theorem parses_decodeOther_const32 {bytes : List UInt8} {value : UInt32}
    (h : Signed 32 bytes value.toBitVec.toInt) :
    Parses (instructions.decodeOther 0x41) bytes (.const value) := by
  unfold instructions.decodeOther
  show Parses (do return Wasm.Instruction.const (wrap32 (← signed 32))) bytes
    (Wasm.Instruction.const value)
  refine Parses.bind_nil (parses_signed h) ?_
  rw [wrap32_toInt]
  exact Parses.pure' _

theorem parses_decodeOther_const64 {bytes : List UInt8} {value : UInt64}
    (h : Signed 64 bytes value.toBitVec.toInt) :
    Parses (instructions.decodeOther 0x42) bytes (.constI64 value) := by
  unfold instructions.decodeOther
  show Parses (do return Wasm.Instruction.constI64 (wrap64 (← signed 64))) bytes
    (Wasm.Instruction.constI64 value)
  refine Parses.bind_nil (parses_signed h) ?_
  rw [wrap64_toInt]
  exact Parses.pure' _

theorem parses_fixed64 (value : UInt64) : Parses fixed64 (Spec.littleEndian64 value) value := by
  have hLength : (Spec.littleEndian64 value).length = 8 := by simp [Spec.littleEndian64]
  unfold fixed64
  rw [← hLength]
  refine Parses.bind_nil (parses_take _) ?_
  have hValue : UInt64.ofNat ((Spec.littleEndian64 value).foldr
      (fun b acc => b.toNat + 256 * acc) 0) = value := by
    apply UInt64.toNat_inj.mp
    have := value.toNat_lt
    simp [Spec.littleEndian64, List.range_succ, UInt64.toNat_ofNat']
    omega
  rw [hValue]
  exact Parses.pure' _

theorem parses_decodeOther_constF64 (value : UInt64) :
    Parses (instructions.decodeOther 0x44) (Spec.littleEndian64 value) (.f64Const value) := by
  unfold instructions.decodeOther
  show Parses (do return Wasm.Instruction.f64Const (← fixed64)) _ (Wasm.Instruction.f64Const value)
  exact Parses.bind_nil (parses_fixed64 value) (Parses.pure' _)

theorem unsigned_zero : Unsigned 32 [0x00] 0 :=
  Unsigned.terminal 32 0 (by decide) (by decide) (by decide)

theorem parses_decodeOther_memorySize :
    Parses (instructions.decodeOther 0x3f) [0x00] .memorySize := by
  unfold instructions.decodeOther
  show Parses (do
      if (← unsigned 32) ≠ 0 then unsupported "memory index"
      return if (0x3f : UInt8) = 0x3f then Wasm.Instruction.memorySize
        else Wasm.Instruction.memoryGrow) [0x00] Wasm.Instruction.memorySize
  refine Parses.bind_nil (parses_unsigned unsigned_zero 32 (Nat.le_refl _)) ?_
  exact Parses.pure' _

theorem parses_decodeOther_memoryGrow :
    Parses (instructions.decodeOther 0x40) [0x00] .memoryGrow := by
  unfold instructions.decodeOther
  show Parses (do
      if (← unsigned 32) ≠ 0 then unsupported "memory index"
      return if (0x40 : UInt8) = 0x3f then Wasm.Instruction.memorySize
        else Wasm.Instruction.memoryGrow) [0x00] Wasm.Instruction.memoryGrow
  refine Parses.bind_nil (parses_unsigned unsigned_zero 32 (Nat.le_refl _)) ?_
  exact Parses.pure' _

theorem parses_decodeOther_truncSat :
    Parses (instructions.decodeOther 0xfc) [0x00] .i32TruncSatF32S := by
  unfold instructions.decodeOther
  show Parses (do
      match ← unsigned 32 with
      | 0 => return Wasm.Instruction.i32TruncSatF32S
      | 7 => return Wasm.Instruction.i64TruncSatF64U
      | _ => unsupported "0xfc instruction") [0x00] Wasm.Instruction.i32TruncSatF32S
  refine Parses.bind_nil (parses_unsigned unsigned_zero 32 (Nat.le_refl _)) ?_
  exact Parses.pure' _

theorem unsigned_seven : Unsigned 32 [0x07] 7 :=
  Unsigned.terminal 32 7 (by decide) (by decide) (by decide)

theorem parses_decodeOther_truncSatU :
    Parses (instructions.decodeOther 0xfc) [0x07] .i64TruncSatF64U := by
  unfold instructions.decodeOther
  show Parses (do
      match ← unsigned 32 with
      | 0 => return Wasm.Instruction.i32TruncSatF32S
      | 7 => return Wasm.Instruction.i64TruncSatF64U
      | _ => unsupported "0xfc instruction") [0x07] Wasm.Instruction.i64TruncSatF64U
  refine Parses.bind_nil (parses_unsigned unsigned_seven 32 (Nat.le_refl _)) ?_
  exact Parses.pure' _

/-- The default branch of `instructions`: one instruction read by `decodeOther`,
followed by the rest of the sequence. -/
theorem instructions_other {opcode : UInt8}
    (control : opcode ≠ 0x0b ∧ opcode ≠ 0x05 ∧ opcode ≠ 0x02 ∧ opcode ≠ 0x03 ∧ opcode ≠ 0x04)
    {immediates tail : List UInt8} {instr : Instruction} {rest : List Instruction}
    {last : Terminator} {fuel : Nat}
    (hOther : Parses (instructions.decodeOther opcode) immediates instr)
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1)) (opcode :: immediates ++ tail) (instr :: rest, last) := by
  obtain ⟨h0b, h05, h02, h03, h04⟩ := control
  rw [instructions]
  rw [List.cons_append]
  refine Parses.bind_cons (parses_byte opcode) ?_
  dsimp only
  split
  · exact absurd rfl h0b
  · exact absurd rfl h05
  · exact absurd rfl h02
  · exact absurd rfl h03
  · exact absurd rfl h04
  · exact Parses.bind hOther (Parses.bind_nil hTail (Parses.pure' _))

theorem instructions_end (fuel : Nat) :
    Parses (instructions (fuel + 1)) [0x0b] ([], Terminator.end) := by
  rw [instructions]
  exact Parses.bind_nil (parses_byte 0x0b) (Parses.pure' _)

theorem instructions_else (fuel : Nat) :
    Parses (instructions (fuel + 1)) [0x05] ([], Terminator.else) := by
  rw [instructions]
  exact Parses.bind_nil (parses_byte 0x05) (Parses.pure' _)

theorem instructions_block {typeBytes bodyBytes tail : List UInt8}
    {types : List ValueType} {body rest : List Instruction} {last : Terminator} {fuel : Nat}
    (hType : Parses blockType typeBytes types)
    (hBody : Parses (instructions fuel) (bodyBytes ++ [0x0b]) (body, Terminator.end))
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1)) (0x02 :: (typeBytes ++ ((bodyBytes ++ [0x0b]) ++ tail)))
      (.block 0 types.length body [] types :: rest, last) := by
  rw [instructions]
  refine Parses.bind_cons (parses_byte 0x02) ?_
  show Parses (do
      let types ← blockType
      let (body, terminator) ← instructions fuel
      if terminator = .else then malformed "else outside if"
      let instruction : Instruction :=
        if (0x02 : UInt8) = 0x02 then .block 0 types.length body [] types
        else .loop 0 types.length body [] types
      let (rest, last) ← instructions fuel
      pure (instruction :: rest, last)) _ _
  refine Parses.bind hType ?_
  refine Parses.bind hBody ?_
  exact Parses.bind_nil hTail (Parses.pure' _)

theorem instructions_loop {typeBytes bodyBytes tail : List UInt8}
    {types : List ValueType} {body rest : List Instruction} {last : Terminator} {fuel : Nat}
    (hType : Parses blockType typeBytes types)
    (hBody : Parses (instructions fuel) (bodyBytes ++ [0x0b]) (body, Terminator.end))
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1)) (0x03 :: (typeBytes ++ ((bodyBytes ++ [0x0b]) ++ tail)))
      (.loop 0 types.length body [] types :: rest, last) := by
  rw [instructions]
  refine Parses.bind_cons (parses_byte 0x03) ?_
  show Parses (do
      let types ← blockType
      let (body, terminator) ← instructions fuel
      if terminator = .else then malformed "else outside if"
      let instruction : Instruction :=
        if (0x03 : UInt8) = 0x02 then .block 0 types.length body [] types
        else .loop 0 types.length body [] types
      let (rest, last) ← instructions fuel
      pure (instruction :: rest, last)) _ _
  refine Parses.bind hType ?_
  refine Parses.bind hBody ?_
  exact Parses.bind_nil hTail (Parses.pure' _)

theorem instructions_iff {typeBytes thenBytes elseBytes tail : List UInt8}
    {types : List ValueType} {thenBody elseBody rest : List Instruction} {last : Terminator}
    {fuel : Nat}
    (hType : Parses blockType typeBytes types)
    (hThen : Parses (instructions fuel) (thenBytes ++ [0x05]) (thenBody, Terminator.else))
    (hElse : Parses (instructions fuel) (elseBytes ++ [0x0b]) (elseBody, Terminator.end))
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1))
      (0x04 :: (typeBytes ++ ((thenBytes ++ [0x05]) ++ ((elseBytes ++ [0x0b]) ++ tail))))
      (.iff 0 types.length thenBody elseBody [] types :: rest, last) := by
  rw [instructions]
  refine Parses.bind_cons (parses_byte 0x04) ?_
  show Parses (do
      let types ← blockType
      let (thenBody, terminator) ← instructions fuel
      let elseBody ←
        if terminator = .else then do
          let (elseBody, elseTerminator) ← instructions fuel
          if elseTerminator = .else then malformed "else outside if"
          pure elseBody
        else pure []
      let (rest, last) ← instructions fuel
      pure (.iff 0 types.length thenBody elseBody [] types :: rest, last)) _ _
  refine Parses.bind hType ?_
  refine Parses.bind hThen ?_
  dsimp only
  rw [ite_eq_left rfl]
  refine Parses.bind hElse ?_
  refine Parses.bind (Parses.pure' _) ?_
  exact Parses.bind_nil hTail (Parses.pure' _)

theorem instr_nonempty {bytes : List UInt8} {instr : Instruction} (h : Instr bytes instr) :
    1 ≤ bytes.length := by
  cases h with
  | plain bytes instr rule => cases rule <;> simp
  | _ => simp

theorem plain_step {bytes : List UInt8} {instr : Instruction} (rule : Plain bytes instr)
    {tail : List UInt8} {rest : List Instruction} {last : Terminator} {fuel : Nat}
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1)) (bytes ++ tail) (instr :: rest, last) := by
  cases rule
  case memorySize =>
    exact instructions_other (by decide) parses_decodeOther_memorySize hTail
  case memoryGrow =>
    exact instructions_other (by decide) parses_decodeOther_memoryGrow hTail
  case i32TruncSatF32S =>
    exact instructions_other (by decide) parses_decodeOther_truncSat hTail
  case i64TruncSatF64U =>
    exact instructions_other (by decide) parses_decodeOther_truncSatU hTail
  all_goals exact instructions_other (by decide) (parses_decodeOther_plain rfl) hTail

mutual

theorem instr_step {bytes : List UInt8} {instr : Instruction} (h : Instr bytes instr)
    (fuel : Nat) (hFuel : bytes.length ≤ fuel) {tail : List UInt8}
    {rest : List Instruction} {last : Terminator}
    (hTail : Parses (instructions fuel) tail (rest, last)) :
    Parses (instructions (fuel + 1)) (bytes ++ tail) (instr :: rest, last) :=
  match h with
  | .plain _ _ rule => plain_step rule hTail
  | .index opcode make _ immediate rule encoding => by
      cases rule <;>
        exact instructions_other (by decide)
          (parses_decodeOther_index rfl rfl encoding) hTail
  | .memory opcode maxAlignment make offset immediate rule encoding => by
      cases rule <;>
        exact instructions_other (by decide)
          (parses_decodeOther_memory rfl rfl rfl encoding (by decide)) hTail
  | .const32 immediate value encoding =>
      instructions_other (by decide) (parses_decodeOther_const32 encoding) hTail
  | .const64 immediate value encoding =>
      instructions_other (by decide) (parses_decodeOther_const64 encoding) hTail
  | .constF64 value =>
      instructions_other (by decide) (parses_decodeOther_constF64 value) hTail
  | .block typeBytes bodyBytes types body typeEncoding bodyEncoding => by
      have hLength : bodyBytes.length < fuel := by
        simp only [List.length_cons, List.length_append] at hFuel
        omega
      have hBody := (instrs_seq bodyEncoding fuel hLength).1
      exact (instructions_block (parses_blockType typeEncoding) hBody hTail).cast (by simp)
  | .loop typeBytes bodyBytes types body typeEncoding bodyEncoding => by
      have hLength : bodyBytes.length < fuel := by
        simp only [List.length_cons, List.length_append] at hFuel
        omega
      have hBody := (instrs_seq bodyEncoding fuel hLength).1
      exact (instructions_loop (parses_blockType typeEncoding) hBody hTail).cast (by simp)
  | .iff typeBytes thenBytes elseBytes types thenBody elseBody typeEncoding thenEncoding
      elseEncoding => by
      have hThenLength : thenBytes.length < fuel := by
        simp only [List.length_cons, List.length_append] at hFuel
        omega
      have hElseLength : elseBytes.length < fuel := by
        simp only [List.length_cons, List.length_append] at hFuel
        omega
      have hThen := (instrs_seq thenEncoding fuel hThenLength).2
      have hElse := (instrs_seq elseEncoding fuel hElseLength).1
      exact (instructions_iff (parses_blockType typeEncoding) hThen hElse hTail).cast
        (by simp)

theorem instrs_seq {bytes : List UInt8} {body : List Instruction} (h : Instrs bytes body)
    (fuel : Nat) (hFuel : bytes.length < fuel) :
    Parses (instructions fuel) (bytes ++ [0x0b]) (body, Terminator.end) ∧
      Parses (instructions fuel) (bytes ++ [0x05]) (body, Terminator.else) :=
  match h with
  | .nil => by
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hFuel; omega⟩
      exact ⟨instructions_end fuel, instructions_else fuel⟩
  | .cons headBytes tailBytes head tail headEncoding tailEncoding => by
      have hHead := instr_nonempty headEncoding
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        simp only [List.length_append] at hFuel; omega⟩
      have hTailLength : tailBytes.length < fuel := by
        simp only [List.length_append] at hFuel
        omega
      have hHeadLength : headBytes.length ≤ fuel := by
        simp only [List.length_append] at hFuel
        omega
      have hTail := instrs_seq tailEncoding fuel hTailLength
      exact ⟨(instr_step headEncoding fuel hHeadLength hTail.1).cast (by simp),
        (instr_step headEncoding fuel hHeadLength hTail.2).cast (by simp)⟩

end

end Wasm.Encoding.Decoder
