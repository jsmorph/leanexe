import Project.Compiler.RuntimeBodies
import Project.Compiler.LebLengths

namespace Project.Compiler.RuntimeEncoding

open Project.Compiler.ArithmeticEncoding

mutual
  def instructionBound : LeanExe.Wasm.Instr → Nat
    | .block body | .loop body | .iff _ body none => 3 + programBound body
    | .iff _ left (some right) => 4 + programBound left + programBound right
    | _ => 11
  def programBound : List LeanExe.Wasm.Instr → Nat
    | [] => 0
    | instr :: rest => instructionBound instr + programBound rest
end

theorem arithmetic_length {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : Atom a b) : (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length ≤ 11 := by
  cases h <;>
    simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
      append_list, byte_list, LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64,
      List.length_append, List.length_cons, List.length_nil]
  case get index _ => have h := LebLengths.unsigned (UInt64.ofNat index); omega
  case set index _ => have h := LebLengths.unsigned (UInt64.ofNat index); omega
  case const n => have h := LebLengths.signed (UInt64.ofNat n); omega
  all_goals decide

theorem RuntimeAtom.length_le {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : RuntimeAtom a b) :
    (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length ≤ instructionBound a := by
  cases h with
  | arithmetic h =>
    have bounded := arithmetic_length h
    cases h <;> exact bounded
  | indexed kind index bound =>
    have h := LebLengths.unsigned (UInt64.ofNat index)
    cases kind <;>
      simp only [Indexed.source, instructionBound, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
        LeanExe.Wasm.Image.emitInstr, append_list, byte_list,
        LeanExe.Wasm.Image.encodeNat, LeanExe.Wasm.Image.encodeU64,
        List.length_append, List.length_cons, List.length_nil] <;> omega
  | plain kind =>
    cases kind <;>
      simp only [Plain.source, instructionBound, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
        LeanExe.Wasm.Image.emitInstr, byte_list, bytes2_list, bytes3_list,
        List.length_cons, List.length_nil] <;> decide

mutual
  theorem RuntimeInstruction.length_le {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
      (h : RuntimeInstruction a b) :
      (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length ≤ instructionBound a := by
    cases h with
    | atom h => exact h.length_le
    | control kind body =>
      rw [control_bytes]
      cases kind <;>
        have bounded := RuntimeProgram.length_le body <;>
        simp only [Control.source, instructionBound, List.length_append, List.length_cons,
          List.length_nil] <;> omega
    | ifElse left right =>
      have l := RuntimeProgram.length_le left
      have r := RuntimeProgram.length_le right
      rw [if_else_bytes]
      simp only [instructionBound, List.length_append, List.length_cons, List.length_nil]
      omega
  termination_by sizeOf a
  decreasing_by all_goals simp [Control.source] <;> omega

  theorem RuntimeProgram.length_le {a : List LeanExe.Wasm.Instr} {b : List Wasm.Binary.Instr}
      (h : RuntimeProgram a b) :
      (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a).length ≤ programBound a := by
    cases h with
    | nil => exact Nat.le_refl 0
    | cons head tail =>
      have l := RuntimeInstruction.length_le head
      have r := RuntimeProgram.length_le tail
      simpa only [LeanExe.Wasm.Binary.CoreWasm.encodeInstrs, programBound, List.length_append]
        using Nat.add_le_add l r
  termination_by sizeOf a
end

theorem alloc_bound : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
    LeanExe.Wasm.Binary.CoreWasm.coreAllocInstrs).length + 4 < 2 ^ 32 := by
  have h := allocEncoding.property.length_le
  have small : programBound LeanExe.Wasm.Binary.CoreWasm.coreAllocInstrs + 4 < 2 ^ 32 := by decide
  omega

theorem reset_bound : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
    LeanExe.Wasm.Binary.CoreWasm.coreResetInstrs).length + 2 < 2 ^ 32 := by
  have h := resetEncoding.property.length_le
  have small : programBound LeanExe.Wasm.Binary.CoreWasm.coreResetInstrs + 2 < 2 ^ 32 := by decide
  omega

theorem retain_bound : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
    LeanExe.Wasm.Binary.CoreWasm.coreRetainInstrs).length + 4 < 2 ^ 32 := by
  have h := retainEncoding.property.length_le
  have small : programBound LeanExe.Wasm.Binary.CoreWasm.coreRetainInstrs + 4 < 2 ^ 32 := by decide
  omega

theorem release_bound : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
    (LeanExe.Wasm.Binary.CoreWasm.coreReleaseInstrs 4)).length + 4 < 2 ^ 32 := by
  have h := releaseEncoding.property.length_le
  have small : programBound (LeanExe.Wasm.Binary.CoreWasm.coreReleaseInstrs 4) + 4 < 2 ^ 32 := by decide
  omega

end Project.Compiler.RuntimeEncoding
