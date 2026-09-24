import Project.Compiler.ArithmeticEncoding
import Project.Compiler.LebParsing
import Project.Artifact.Binary.Decode

namespace Project.Compiler.ArithmeticEncoding

open Project.Compiler.Parsing

theorem Atom.parses {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr} (h : Atom a b) (fuel : Nat) :
    Parses (Wasm.Binary.instruction (fuel + 1)) (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
  cases h with
  | get index bound =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      append_list, byte_list, LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64]
    unfold Wasm.Binary.instruction
    apply bind_parses (read_byte 32)
    exact map_parses (Parsing.u32 index bound) Wasm.Binary.Instr.localGet
  | set index bound =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      append_list, byte_list, LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64]
    unfold Wasm.Binary.instruction
    apply bind_parses (read_byte 33)
    exact map_parses (Parsing.u32 index bound) Wasm.Binary.Instr.localSet
  | const n =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      append_list, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (read_byte 66)
    exact map_parses (Parsing.s64 (UInt64.ofNat n)) Wasm.Binary.Instr.i64Const
  | add =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [124]) (b := []) (read_byte 124)
    exact pure_parses _
  | sub =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [125]) (b := []) (read_byte 125)
    exact pure_parses _
  | mul =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [126]) (b := []) (read_byte 126)
    exact pure_parses _
  | div =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [128]) (b := []) (read_byte 128)
    exact pure_parses _
  | rem =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [130]) (b := []) (read_byte 130)
    exact pure_parses _
  | and =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [131]) (b := []) (read_byte 131)
    exact pure_parses _
  | or =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [132]) (b := []) (read_byte 132)
    exact pure_parses _
  | xor =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [133]) (b := []) (read_byte 133)
    exact pure_parses _
  | shl =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [134]) (b := []) (read_byte 134)
    exact pure_parses _
  | shr =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [136]) (b := []) (read_byte 136)
    exact pure_parses _
  | eq =>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr, byte_list]
    unfold Wasm.Binary.instruction
    apply bind_parses (a := [81]) (b := []) (read_byte 81)
    exact pure_parses _

end Project.Compiler.ArithmeticEncoding
