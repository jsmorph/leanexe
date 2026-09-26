import Project.Compiler.UnsignedLeb
import Project.Compiler.SignedLeb

namespace Project.Compiler.ArithmeticEncoding

open LeanExe.Wasm (Instr)

/-- The scalar arithmetic instruction forms emitted by the production compiler.
Index bounds are format bounds, independent of semantic correctness. -/
inductive Atom : Instr → Wasm.Binary.Instr → Prop where
  | get (index : Nat) (bound : index < 2 ^ 32) : Atom (.localGet index) (.localGet (UInt32.ofNat index))
  | set (index : Nat) (bound : index < 2 ^ 32) : Atom (.localSet index) (.localSet (UInt32.ofNat index))
  | br (depth : Nat) (bound : depth < 2 ^ 32) : Atom (.br depth) (.br (UInt32.ofNat depth))
  | brIf (depth : Nat) (bound : depth < 2 ^ 32) : Atom (.brIf depth) (.brIf (UInt32.ofNat depth))
  | const (n : Nat) : Atom (.constI64 n) (.i64Const (UInt64.ofNat n).toBitVec.toInt)
  | add : Atom .addI64 .i64Add
  | sub : Atom .subI64 .i64Sub
  | mul : Atom .mulI64 .i64Mul
  | div : Atom .divUI64 .i64DivU
  | rem : Atom .remUI64 .i64RemU
  | and : Atom .andI64 .i64And
  | or : Atom .orI64 .i64Or
  | xor : Atom .xorI64 .i64Xor
  | shl : Atom .shlI64 .i64Shl
  | shr : Atom .shrUI64 .i64ShrU
  | eq : Atom .eqI64 .i64Eq
  | lt : Atom .ltUI64 .i64LtU
  | le : Atom .leUI64 .i64LeU
  | eqz32 : Atom .eqzI32 .i32Eqz

mutual
  inductive InstructionEncoding : Instr → Wasm.Binary.Instr → Prop where
    | atom (h : Atom a b) : InstructionEncoding a b
    | if64 (left : ProgramEncoding a ra) (right : ProgramEncoding b rb) :
        InstructionEncoding (.iff true a (some b)) (.iff (.value .i64) ra (some rb))

    | if0 (left : ProgramEncoding a ra) (right : ProgramEncoding b rb) :
        InstructionEncoding (.iff false a (some b)) (.iff .empty ra (some rb))
    | block0 (body : ProgramEncoding a ra) :
        InstructionEncoding (.block a) (.block .empty ra)
    | loop0 (body : ProgramEncoding a ra) :
        InstructionEncoding (.loop a) (.loop .empty ra)

  inductive ProgramEncoding : List Instr → List Wasm.Binary.Instr → Prop where
    | nil : ProgramEncoding [] []
    | cons (head : InstructionEncoding a ra) (tail : ProgramEncoding b rb) :
        ProgramEncoding (a :: b) (ra :: rb)
end

@[simp] theorem byte_list (n : Nat) : (LeanExe.Wasm.Image.byte n).toList = [UInt8.ofNat n] := by
  simp [byteArray_toList, LeanExe.Wasm.Image.byte, ByteArray.push]

@[simp] theorem append_list (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  simp [byteArray_toList, ByteArray.toList_data_append]

@[simp] theorem bytes2_list (a b : Nat) :
    (LeanExe.Wasm.Image.bytes2 a b).toList = [UInt8.ofNat a, UInt8.ofNat b] := by
  simp [byteArray_toList, LeanExe.Wasm.Image.bytes2, LeanExe.Wasm.Image.byte, ByteArray.push]

theorem image_sequence (code : List Instr) :
    (LeanExe.Wasm.Image.emitInstrs code).toList = LeanExe.Wasm.Binary.CoreWasm.encodeInstrs code := by
  induction code with
  | nil => simp [LeanExe.Wasm.Image.emitInstrs, LeanExe.Wasm.Binary.CoreWasm.encodeInstrs]
  | cons a b ih =>
    simp [LeanExe.Wasm.Image.emitInstrs, LeanExe.Wasm.Binary.CoreWasm.encodeInstrs,
      LeanExe.Wasm.Binary.CoreWasm.encodeInstr, ih]

theorem Atom.grammar {a : Instr} {b : Wasm.Binary.Instr} (h : Atom a b) :
    Wasm.Binary.Grammar.Instr (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
  cases h with
  | get index bound =>
    have hi : (UInt32.ofNat index).toNat = index := UInt32.toNat_ofNat_of_lt' bound
    simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64, LeanExe.Wasm.Binary.u32leb, Wasm.Binary.Grammar.byte, hi] using
      (Wasm.Binary.Grammar.Instr.localGet (LeanExe.Wasm.Binary.u32leb index) (UInt32.ofNat index)
        (by simpa [hi] using UnsignedLeb.production_u32 index bound))
  | set index bound =>
    have hi : (UInt32.ofNat index).toNat = index := UInt32.toNat_ofNat_of_lt' bound
    simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64, LeanExe.Wasm.Binary.u32leb, Wasm.Binary.Grammar.byte, hi] using
      (Wasm.Binary.Grammar.Instr.localSet (LeanExe.Wasm.Binary.u32leb index) (UInt32.ofNat index)
        (by simpa [hi] using UnsignedLeb.production_u32 index bound))
  | br depth bound =>
    have hi : (UInt32.ofNat depth).toNat = depth := UInt32.toNat_ofNat_of_lt' bound
    simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64, LeanExe.Wasm.Binary.u32leb, Wasm.Binary.Grammar.byte, hi] using
      (Wasm.Binary.Grammar.Instr.br (LeanExe.Wasm.Binary.u32leb depth) (UInt32.ofNat depth)
        (by simpa [hi] using UnsignedLeb.production_u32 depth bound))
  | brIf depth bound =>
    have hi : (UInt32.ofNat depth).toNat = depth := UInt32.toNat_ofNat_of_lt' bound
    simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64, LeanExe.Wasm.Binary.u32leb, Wasm.Binary.Grammar.byte, hi] using
      (Wasm.Binary.Grammar.Instr.brIf (LeanExe.Wasm.Binary.u32leb depth) (UInt32.ofNat depth)
        (by simpa [hi] using UnsignedLeb.production_u32 depth bound))
  | const n =>
    simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using
      (Wasm.Binary.Grammar.Instr.i64Const _ _ (SignedLeb.s64 (UInt64.ofNat n)))
  | add => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Add
  | sub => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Sub
  | mul => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Mul
  | div => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64DivU
  | rem => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64RemU
  | and => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64And
  | or => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Or
  | xor => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Xor
  | shl => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Shl
  | shr => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64ShrU
  | eq => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64Eq
  | lt => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64LtU
  | le => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i64LeU
  | eqz32 => simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, Wasm.Binary.Grammar.byte] using Wasm.Binary.Grammar.Instr.i32Eqz

mutual
  theorem InstructionEncoding.grammar {a : Instr} {b : Wasm.Binary.Instr}
      (h : InstructionEncoding a b) : Wasm.Binary.Grammar.Instr (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
    cases h with
    | atom h => exact h.grammar
    | if64 left right =>
      simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
        image_sequence, Wasm.Binary.Grammar.byte, List.append_assoc] using
        (Wasm.Binary.Grammar.Instr.iffElse [Wasm.Binary.Grammar.byte 126] _ _ (.value .i64) _ _
          Wasm.Binary.Grammar.BlockType.i64 left.grammar right.grammar)
    | if0 left right =>
      simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
        image_sequence, Wasm.Binary.Grammar.byte, List.append_assoc] using
        (Wasm.Binary.Grammar.Instr.iffElse [Wasm.Binary.Grammar.byte 64] _ _ .empty _ _
          Wasm.Binary.Grammar.BlockType.empty left.grammar right.grammar)
    | block0 body =>
      simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
        image_sequence, Wasm.Binary.Grammar.byte, List.append_assoc] using
        (Wasm.Binary.Grammar.Instr.block [Wasm.Binary.Grammar.byte 64] _ .empty _
          Wasm.Binary.Grammar.BlockType.empty body.grammar)
    | loop0 body =>
      simpa [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
        image_sequence, Wasm.Binary.Grammar.byte, List.append_assoc] using
        (Wasm.Binary.Grammar.Instr.loop [Wasm.Binary.Grammar.byte 64] _ .empty _
          Wasm.Binary.Grammar.BlockType.empty body.grammar)
  termination_by sizeOf a

  theorem ProgramEncoding.grammar {a : List Instr} {b : List Wasm.Binary.Instr}
      (h : ProgramEncoding a b) : Wasm.Binary.Grammar.Instrs (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a) b := by
    cases h with
    | nil => exact .nil
    | cons head tail => exact .cons _ _ _ _ head.grammar tail.grammar
  termination_by sizeOf a
end

end Project.Compiler.ArithmeticEncoding
