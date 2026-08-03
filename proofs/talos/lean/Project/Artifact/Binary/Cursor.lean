import Project.Artifact.Binary.Syntax

namespace Wasm.Binary

inductive ErrorKind where
  | unexpectedEnd
  | trailingBytes
  | expectedByte (expected found : UInt8)
  | integerTooLong (width : Nat)
  | integerOverflow (width : Nat)
  | invalidUtf8
  | vectorLengthExceedsInput (length remaining : Nat)
  | unsupportedSection (id : UInt8)
  | duplicateSection (id : SectionId)
  | sectionOutOfOrder (id : SectionId)
  | unsupportedType (code : UInt8)
  | unsupportedOpcode (opcode : UInt8)
  | malformed (description : String)
  deriving Repr, Inhabited, DecidableEq

structure Error where
  offset : Nat
  kind : ErrorKind
  deriving Repr, Inhabited, DecidableEq

structure Cursor where
  bytes : ByteArray
  pos : Nat
  limit : Nat

namespace Cursor

def start (bytes : ByteArray) : Cursor :=
  { bytes, pos := 0, limit := bytes.size }

def remaining (cursor : Cursor) : Nat :=
  cursor.limit - cursor.pos

end Cursor

def Parser (α : Type) : Type :=
  Cursor → Except Error (α × Cursor)

namespace Parser

instance : Monad Parser where
  pure value := fun cursor => .ok (value, cursor)
  bind parser next := fun cursor => do
    let (value, cursor') ← parser cursor
    next value cursor'

def fail (kind : ErrorKind) : Parser α :=
  fun cursor => .error { offset := cursor.pos, kind }

def position : Parser Nat :=
  fun cursor => .ok (cursor.pos, cursor)

def readByte : Parser UInt8 :=
  fun cursor =>
    if cursor.pos < cursor.limit then
      match cursor.bytes.data[cursor.pos]? with
      | some value => .ok (value, { cursor with pos := cursor.pos + 1 })
      | none => .error { offset := cursor.pos, kind := .unexpectedEnd }
    else
      .error { offset := cursor.pos, kind := .unexpectedEnd }

def peekByte : Parser UInt8 :=
  fun cursor =>
    if cursor.pos < cursor.limit then
      match cursor.bytes.data[cursor.pos]? with
      | some value => .ok (value, cursor)
      | none => .error { offset := cursor.pos, kind := .unexpectedEnd }
    else
      .error { offset := cursor.pos, kind := .unexpectedEnd }

def readBytes (count : Nat) : Parser (List UInt8) :=
  fun cursor =>
    if count ≤ cursor.remaining && cursor.pos + count ≤ cursor.bytes.size then
      let stop := cursor.pos + count
      let values := (cursor.bytes.extract cursor.pos stop).data.toList
      .ok (values, { cursor with pos := stop })
    else
      .error { offset := cursor.pos, kind := .unexpectedEnd }

def expectByte (expected : UInt8) : Parser Unit := do
  let offset ← position
  let found ← readByte
  if found = expected then
    pure ()
  else
    fun _ => .error { offset, kind := .expectedByte expected found }

def expectBytes : List UInt8 → Parser Unit
  | [] => pure ()
  | byte :: rest => do
      expectByte byte
      expectBytes rest

def bounded (size : Nat) (parser : Parser α) : Parser α :=
  fun cursor =>
    if size ≤ cursor.remaining && cursor.pos + size ≤ cursor.bytes.size then
      let stop := cursor.pos + size
      let inner := { cursor with limit := stop }
      let outer := { cursor with pos := stop }
      match parser inner with
      | .error error => .error error
      | .ok (value, inner') =>
          if inner'.pos = stop then
            .ok (value, outer)
          else
            .error { offset := inner'.pos, kind := .trailingBytes }
    else
      .error { offset := cursor.pos, kind := .unexpectedEnd }

def run (parser : Parser α) (bytes : ByteArray) : Except Error (α × Cursor) :=
  parser (Cursor.start bytes)

def runAll (parser : Parser α) (bytes : ByteArray) : Except Error α := do
  let (value, cursor) ← run parser bytes
  if cursor.pos = cursor.limit then
    pure value
  else
    .error { offset := cursor.pos, kind := .trailingBytes }

end Parser

end Wasm.Binary
