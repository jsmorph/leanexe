import Init.Data.String.Basic
import Project.Artifact.Binary.Leb

namespace Wasm.Binary

open Parser

namespace Internal

def vectorLoop (parser : Parser α) : Nat → Parser (List α)
  | 0 => pure []
  | count + 1 => do
      let value ← parser
      let rest ← vectorLoop parser count
      pure (value :: rest)

end Internal

def vector (parser : Parser α) : Parser (List α) := do
  let length ← Leb.u32
  let remaining ← fun cursor => .ok (cursor.remaining, cursor)
  if length.toNat ≤ remaining then
    Internal.vectorLoop parser length.toNat
  else
    fail (.vectorLengthExceedsInput length.toNat remaining)

def byteVector : Parser (List UInt8) := do
  let length ← Leb.u32
  readBytes length.toNat

def name : Parser Name := do
  let bytes ← byteVector
  match String.fromUTF8? bytes.toByteArray with
  | some text => pure { bytes, text }
  | none => fail .invalidUtf8

def sized (parser : Parser α) : Parser α := do
  let size ← Leb.u32
  bounded size.toNat parser

end Wasm.Binary
