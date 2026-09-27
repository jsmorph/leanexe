import LeanExe.Ascii.Json.Value

namespace LeanExe
namespace Ascii
namespace Json

def decodeError : ByteArray :=
  errorJson

def failDecode {α : Type} : Except ByteArray α :=
  Except.error decodeError

def requireUInt64 (value : Value) : Except ByteArray UInt64 :=
  match asUInt64? value with
  | some n => Except.ok n
  | none => failDecode

def requireBool (value : Value) : Except ByteArray Bool :=
  match asBool? value with
  | some value => Except.ok value
  | none => failDecode

def requireString (value : Value) : Except ByteArray AsciiString :=
  match asString? value with
  | some text => Except.ok text
  | none => failDecode

def requireArray (value : Value) : Except ByteArray (Array Value) :=
  match asArray? value with
  | some items => Except.ok items
  | none => failDecode

def requireObject (value : Value) : Except ByteArray (Array Field) :=
  match asObject? value with
  | some fields => Except.ok fields
  | none => failDecode

def requireUniqueField (fields : Array Field) (name : AsciiString) :
    Except ByteArray Value :=
  match getUniqueField? fields name with
  | some value => Except.ok value
  | none => failDecode

def requireField (value : Value) (name : AsciiString) : Except ByteArray Value := do
  let fields <- requireObject value
  requireUniqueField fields name

def decodeRequiredField {α : Type} (fields : Array Field) (name : AsciiString)
    (decode : Value -> Except ByteArray α) : Except ByteArray α := do
  let raw <- requireUniqueField fields name
  decode raw

def requireUInt64Field (value : Value) (name : AsciiString) :
    Except ByteArray UInt64 := do
  let raw <- requireField value name
  requireUInt64 raw

def requireBoolField (value : Value) (name : AsciiString) :
    Except ByteArray Bool := do
  let raw <- requireField value name
  requireBool raw

def requireStringField (value : Value) (name : AsciiString) :
    Except ByteArray AsciiString := do
  let raw <- requireField value name
  requireString raw

def requireArrayField (value : Value) (name : AsciiString) :
    Except ByteArray (Array Value) := do
  let raw <- requireField value name
  requireArray raw

def requireObjectField (value : Value) (name : AsciiString) :
    Except ByteArray (Array Field) := do
  let raw <- requireField value name
  requireObject raw

def requireOnlyFields (fields : Array Field) (names : Array AsciiString) :
    Except ByteArray Unit :=
  if allFieldNamesIn fields names then
    Except.ok ()
  else
    failDecode

def decodeUInt64Array (value : Value) : Except ByteArray (Array UInt64) := do
  let items <- requireArray value
  items.foldl
    (fun state item =>
      match state with
      | Except.error err => Except.error err
      | Except.ok values =>
          match requireUInt64 item with
          | Except.error err => Except.error err
          | Except.ok n => Except.ok (values.push n))
    (Except.ok #[])

def decodeArray {α : Type} (decode : Value -> Except ByteArray α) (value : Value) :
    Except ByteArray (Array α) := do
  let items <- requireArray value
  items.foldl
    (fun state item =>
      match state with
      | Except.error err => Except.error err
      | Except.ok values =>
          match decode item with
          | Except.error err => Except.error err
          | Except.ok decoded => Except.ok (values.push decoded))
    (Except.ok #[])

def parseBytesExcept (bytes : ByteArray) : Except ByteArray Value :=
  match parseBytes bytes with
  | some value => Except.ok value
  | none => failDecode

def renderExcept (value : Value) : Except ByteArray ByteArray :=
  match render? value with
  | some bytes => Except.ok bytes
  | none => failDecode

end Json
end Ascii
end LeanExe
