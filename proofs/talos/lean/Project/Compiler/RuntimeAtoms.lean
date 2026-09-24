import Project.Compiler.StructuredParsing

namespace Project.Compiler.RuntimeEncoding

open Project.Compiler.Parsing
open Project.Compiler.ArithmeticEncoding

inductive Indexed where
  | tee | globalGet | globalSet | call | br | brIf

def Indexed.source (kind : Indexed) (index : Nat) : LeanExe.Wasm.Instr :=
  match kind with
  | .tee => .localTee index
  | .globalGet => .globalGet index
  | .globalSet => .globalSet index
  | .call => .call index
  | .br => .br index
  | .brIf => .brIf index

def Indexed.raw (kind : Indexed) (index : Nat) : Wasm.Binary.Instr :=
  match kind with
  | .tee => .localTee (UInt32.ofNat index)
  | .globalGet => .globalGet (UInt32.ofNat index)
  | .globalSet => .globalSet (UInt32.ofNat index)
  | .call => .call (UInt32.ofNat index)
  | .br => .br (UInt32.ofNat index)
  | .brIf => .brIf (UInt32.ofNat index)

inductive Plain where
  | ne | lt | ge | wrap | extend | eq32 | unreachable | ret
  | load64 | store64 | memorySize | memoryGrow | negOne

def Plain.source : Plain → LeanExe.Wasm.Instr
  | .ne => .neI64
  | .lt => .ltUI64
  | .ge => .geUI64
  | .wrap => .wrapI64
  | .extend => .extendUI32
  | .eq32 => .eqI32
  | .unreachable => .unreachable
  | .ret => .ret
  | .load64 => .load64
  | .store64 => .store64
  | .memorySize => .memorySize
  | .memoryGrow => .memoryGrow
  | .negOne => .constI32NegOne

def Plain.raw : Plain → Wasm.Binary.Instr
  | .ne => .i64Ne
  | .lt => .i64LtU
  | .ge => .i64GeU
  | .wrap => .i32WrapI64
  | .extend => .i64ExtendI32U
  | .eq32 => .i32Eq
  | .unreachable => .unreachable
  | .ret => .ret
  | .load64 => .i64Load { align := 3, offset := 0 }
  | .store64 => .i64Store { align := 3, offset := 0 }
  | .memorySize => .memorySize 0
  | .memoryGrow => .memoryGrow 0
  | .negOne => .i32Const (-1)

/-- Additional fixed runtime instruction forms. Arithmetic user programs still
use their independently derived arithmetic-only encoding relation. -/
inductive RuntimeAtom : LeanExe.Wasm.Instr → Wasm.Binary.Instr → Prop where
  | arithmetic (h : Atom a b) : RuntimeAtom a b
  | indexed (kind : Indexed) (index : Nat) (bound : index < 2 ^ 32) :
      RuntimeAtom (kind.source index) (kind.raw index)
  | plain (kind : Plain) : RuntimeAtom kind.source kind.raw

@[simp] theorem bytes3_list (a b c : Nat) :
    (LeanExe.Wasm.Image.bytes3 a b c).toList = [UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c] := by
  simp [Project.Compiler.byteArray_toList, LeanExe.Wasm.Image.bytes3,
    LeanExe.Wasm.Image.bytes2, LeanExe.Wasm.Image.byte, ByteArray.push]

theorem RuntimeAtom.prefix {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : RuntimeAtom a b) :
    ∃ opcode rest, LeanExe.Wasm.Binary.CoreWasm.encodeInstr a = opcode :: rest ∧
      opcode ≠ 11 ∧ opcode ≠ 5 := by
  cases h with
  | arithmetic h => exact grammar_prefix h.grammar
  | indexed kind index bound =>
    cases kind <;>
      simp only [Indexed.source, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
        LeanExe.Wasm.Image.emitInstr, append_list, byte_list] <;>
      exact ⟨_, _, rfl, by decide, by decide⟩
  | plain kind =>
    cases kind <;>
      simp only [Plain.source, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
        LeanExe.Wasm.Image.emitInstr, bytes3_list, bytes2_list, byte_list] <;>
      exact ⟨_, _, rfl, by decide, by decide⟩

theorem indexed_parses (kind : Indexed) (index fuel : Nat) (bound : index < 2 ^ 32) :
    Parses (Wasm.Binary.instruction (fuel + 1))
      (LeanExe.Wasm.Binary.CoreWasm.encodeInstr (kind.source index)) (kind.raw index) := by
  cases kind <;>
    simp only [Indexed.source, Indexed.raw, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
      LeanExe.Wasm.Image.emitInstr, append_list, byte_list, LeanExe.Wasm.Image.encodeNat,
      LeanExe.Wasm.Image.encodeU64] <;>
    unfold Wasm.Binary.instruction
  · exact bind_parses (read_byte 34) (map_parses (u32 index bound) Wasm.Binary.Instr.localTee)
  · exact bind_parses (read_byte 35) (map_parses (u32 index bound) Wasm.Binary.Instr.globalGet)
  · exact bind_parses (read_byte 36) (map_parses (u32 index bound) Wasm.Binary.Instr.globalSet)
  · exact bind_parses (read_byte 16) (map_parses (u32 index bound) Wasm.Binary.Instr.call)
  · exact bind_parses (read_byte 12) (map_parses (u32 index bound) Wasm.Binary.Instr.br)
  · exact bind_parses (read_byte 13) (map_parses (u32 index bound) Wasm.Binary.Instr.brIf)

theorem u32_zero : Parses Wasm.Binary.Leb.u32 [0] 0 := by
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using u32 0 (by decide)
theorem u32_three : Parses Wasm.Binary.Leb.u32 [3] 3 := by
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using u32 3 (by decide)

theorem memarg64 : Parses Wasm.Binary.memArg [3, 0] { align := 3, offset := 0 } := by
  unfold Wasm.Binary.memArg
  exact bind_parses u32_three (map_parses u32_zero
    (fun offset => ({ align := 3, offset } : Wasm.Binary.MemArg)))

theorem s32_negOne : Parses Wasm.Binary.Leb.s32 [127] (-1) := by
  unfold Wasm.Binary.Leb.s32 Wasm.Binary.Leb.Internal.signedLoop
  apply bind_parses (a := [127]) (b := []) (read_byte 127)
  exact pure_parses _

theorem plain_parses (kind : Plain) (fuel : Nat) :
    Parses (Wasm.Binary.instruction (fuel + 1))
      (LeanExe.Wasm.Binary.CoreWasm.encodeInstr kind.source) kind.raw := by
  cases kind <;>
    simp only [Plain.source, Plain.raw, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
      LeanExe.Wasm.Image.emitInstr, bytes3_list, bytes2_list, byte_list] <;>
    unfold Wasm.Binary.instruction
  · exact bind_parses (read_byte 82) (pure_parses _)
  · exact bind_parses (read_byte 84) (pure_parses _)
  · exact bind_parses (read_byte 90) (pure_parses _)
  · exact bind_parses (read_byte 167) (pure_parses _)
  · exact bind_parses (read_byte 173) (pure_parses _)
  · exact bind_parses (read_byte 70) (pure_parses _)
  · exact bind_parses (read_byte 0) (pure_parses _)
  · exact bind_parses (read_byte 15) (pure_parses _)
  · exact bind_parses (read_byte 41) (map_parses memarg64 Wasm.Binary.Instr.i64Load)
  · exact bind_parses (read_byte 55) (map_parses memarg64 Wasm.Binary.Instr.i64Store)
  · exact bind_parses (read_byte 63) (map_parses u32_zero Wasm.Binary.Instr.memorySize)
  · exact bind_parses (read_byte 64) (map_parses u32_zero Wasm.Binary.Instr.memoryGrow)
  · exact bind_parses (read_byte 65) (map_parses s32_negOne Wasm.Binary.Instr.i32Const)

theorem RuntimeAtom.parses {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : RuntimeAtom a b) (fuel : Nat) :
    Parses (Wasm.Binary.instruction (fuel + 1)) (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
  cases h with
  | arithmetic h => exact h.parses fuel
  | indexed kind index bound => exact indexed_parses kind index fuel bound
  | plain kind => exact plain_parses kind fuel

end Project.Compiler.RuntimeEncoding
