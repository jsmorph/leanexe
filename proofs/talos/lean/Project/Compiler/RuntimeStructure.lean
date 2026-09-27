import Project.Compiler.RuntimeAtoms

namespace Project.Compiler.RuntimeEncoding

open Project.Compiler.Parsing
open Project.Compiler.ArithmeticEncoding

inductive Control where
  | block | loop | ifNone

def Control.source (kind : Control) (body : List LeanExe.Wasm.Instr) : LeanExe.Wasm.Instr :=
  match kind with
  | .block => .block body
  | .loop => .loop body
  | .ifNone => .iff false body none

def Control.raw (kind : Control) (body : List Wasm.Binary.Instr) : Wasm.Binary.Instr :=
  match kind with
  | .block => .block .empty body
  | .loop => .loop .empty body
  | .ifNone => .iff .empty body none

def Control.tag : Control → UInt8
  | .block => 2
  | .loop => 3
  | .ifNone => 4

def Control.allowElse : Control → Bool
  | .ifNone => true
  | _ => false

mutual
  inductive RuntimeInstruction : LeanExe.Wasm.Instr → Wasm.Binary.Instr → Prop where
    | atom (h : RuntimeAtom a b) : RuntimeInstruction a b
    | control (kind : Control) (body : RuntimeProgram a b) :
        RuntimeInstruction (kind.source a) (kind.raw b)
    | ifElse (left : RuntimeProgram a ra) (right : RuntimeProgram b rb) :
        RuntimeInstruction (.iff false a (some b)) (.iff .empty ra (some rb))

  inductive RuntimeProgram : List LeanExe.Wasm.Instr → List Wasm.Binary.Instr → Prop where
    | nil : RuntimeProgram [] []
    | cons (head : RuntimeInstruction a ra) (tail : RuntimeProgram b rb) :
        RuntimeProgram (a :: b) (ra :: rb)
end

theorem control_bytes (kind : Control) (body : List LeanExe.Wasm.Instr) :
    LeanExe.Wasm.Binary.CoreWasm.encodeInstr (kind.source body) =
      [kind.tag, 64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs body ++ [11]) := by
  have empty : ByteArray.empty.toList = [] := by
    simp only [Project.Compiler.byteArray_toList, ByteArray.data_empty, Array.toList_empty]
  cases kind <;>
    simp [Control.source, Control.tag, LeanExe.Wasm.Binary.CoreWasm.encodeInstr,
      LeanExe.Wasm.Image.emitInstr, image_sequence, List.append_assoc, empty]

theorem if_else_bytes (left right : List LeanExe.Wasm.Instr) :
    LeanExe.Wasm.Binary.CoreWasm.encodeInstr (.iff false left (some right)) =
      [4, 64] ++ ((LeanExe.Wasm.Binary.CoreWasm.encodeInstrs left ++ [5]) ++
        (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs right ++ [11])) := by
  simp [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
    image_sequence, List.append_assoc]

theorem RuntimeInstruction.prefix {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : RuntimeInstruction a b) :
    ∃ opcode rest, LeanExe.Wasm.Binary.CoreWasm.encodeInstr a = opcode :: rest ∧
      opcode ≠ 11 ∧ opcode ≠ 5 := by
  cases h with
  | atom h => exact h.prefix
  | control kind body =>
    rw [control_bytes]
    refine ⟨kind.tag, _, rfl, ?_, ?_⟩ <;> cases kind <;> decide
  | ifElse left right =>
    rw [if_else_bytes]
    exact ⟨4, _, rfl, by decide, by decide⟩

theorem block_empty : Parses Wasm.Binary.blockType [64] .empty := by
  unfold Wasm.Binary.blockType
  exact bind_parses (read_byte 64) (pure_parses _)

end Project.Compiler.RuntimeEncoding
