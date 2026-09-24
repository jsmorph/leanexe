import Project.Correct.Scalar64.Module
import LeanExe.Wasm.Leb

/-! Untrusted byte encoding. Certification separately decodes these bytes and
checks the complete module against assemble; no encoder axiom is used. -/
namespace Project.Correct.Scalar64
open Wasm
open LeanExe.Wasm.Leb

private def bytes (values : List UInt8) : ByteArray := ByteArray.mk values.toArray
private def u32 (value : Nat) : ByteArray := u32lebU64 (UInt64.ofNat value)
private def vector (values : List ByteArray) : ByteArray := vecBytes values.toArray

def controlType (arity : Nat) (types : List ValueType) : Except String UInt8 :=
  match arity, types with
  | 0, [] => .ok 0x40
  | 1, [.i64] => .ok 0x7e
  | 1, [.i32] => .ok 0x7f
  | _, _ => .error "scalar64: inconsistent control result type"

mutual
def encodeInstruction : Instruction → Except String ByteArray
  | .const value =>
      if value = 0 || value = 1 then pure (bytes [0x41, value.toUInt8])
      else .error "scalar64: only Boolean i32 constants are admitted"
  | .constI64 value => pure (bytes [0x42] ++ s64lebU64 value)
  | .localGet index => pure (bytes [0x20] ++ u32 index)
  | .localSet index => pure (bytes [0x21] ++ u32 index)
  | .call index => pure (bytes [0x10] ++ u32 index)
  | .br index => pure (bytes [0x0c] ++ u32 index)
  | .br_if index => pure (bytes [0x0d] ++ u32 index)
  | .block 0 arity body [] types => do
      let type ← controlType arity types
      pure (bytes [0x02, type] ++ (← encodeInstructions body) ++ bytes [0x0b])
  | .loop 0 arity body [] types => do
      let type ← controlType arity types
      pure (bytes [0x03, type] ++ (← encodeInstructions body) ++ bytes [0x0b])
  | .iff 0 arity yes no [] types => do
      let type ← controlType arity types
      pure (bytes [0x04, type] ++ (← encodeInstructions yes) ++ bytes [0x05] ++
        (← encodeInstructions no) ++ bytes [0x0b])
  | .addI64 => pure (bytes [0x7c])
  | .subI64 => pure (bytes [0x7d])
  | .mulI64 => pure (bytes [0x7e])
  | .divUI64 => pure (bytes [0x80])
  | .remUI64 => pure (bytes [0x82])
  | .andI64 => pure (bytes [0x83])
  | .orI64 => pure (bytes [0x84])
  | .xorI64 => pure (bytes [0x85])
  | .shlI64 => pure (bytes [0x86])
  | .shrUI64 => pure (bytes [0x88])
  | .eqI64 => pure (bytes [0x51])
  | .neI64 => pure (bytes [0x52])
  | .ltUI64 => pure (bytes [0x54])
  | .leUI64 => pure (bytes [0x58])
  | .eqz => pure (bytes [0x45])
  | _ => .error "scalar64: instruction outside the certified profile"

def encodeInstructions : List Instruction → Except String ByteArray
  | [] => pure ByteArray.empty
  | instruction :: rest => do
      pure ((← encodeInstruction instruction) ++ (← encodeInstructions rest))
end

private def encodeType (function : Function) : ByteArray :=
  bytes [0x60] ++ u32 function.arity ++ bytes (List.replicate function.arity 0x7e) ++ bytes [1, 0x7e]

private def encodeFunction (index : Nat) (function : Function) : Except String ByteArray := do
  let declarations := if function.localCount = 0 then bytes [0]
    else bytes [1] ++ u32 function.localCount ++ bytes [0x7e]
  let body := declarations ++ (← encodeInstructions (function.lower index).body) ++ bytes [0x0b]
  pure (byteVecBytes body)

def encode (functions : List Function) (exportName : String) (entry : Nat) : Except String ByteArray := do
  unless checkModule functions entry do
    throw "scalar64: invalid locals, scratch capacity, entry, signature, or cyclic/forward call"
  let code ← (functions.zipIdx).mapM fun (function, index) => encodeFunction index function
  pure (bytes [0, 97, 115, 109, 1, 0, 0, 0] ++
    sectionBytes 1 (vector (functions.map encodeType)) ++
    sectionBytes 3 (vector ((List.range functions.length).map u32)) ++
    sectionBytes 7 (vector [byteVecBytes exportName.toUTF8 ++ bytes [0] ++ u32 entry]) ++
    sectionBytes 10 (vector code))

end Project.Correct.Scalar64
