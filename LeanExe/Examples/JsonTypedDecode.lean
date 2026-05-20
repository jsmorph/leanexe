import LeanExe.Ascii.Json.Decode

namespace LeanExe
namespace Examples.JsonTypedDecode

open Ascii.Json

structure Request where
  values : Array UInt64
  multiplier : UInt64
  includeCount : Bool

def valuesFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "values".toUTF8

def multiplierFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "multiplier".toUTF8

def includeCountFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "includeCount".toUTF8

def sumFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "sum".toUTF8

def scaledFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "scaled".toUTF8

def countFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "count".toUTF8

def includedFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "included".toUTF8

def requestFieldNames : Array AsciiString :=
  #[valuesFieldName, multiplierFieldName, includeCountFieldName]

def checkedAdd (left right : UInt64) : Except ByteArray UInt64 :=
  let sum := left + right
  if sum < left then
    Except.error decodeError
  else
    Except.ok sum

def checkedMul (left right : UInt64) : Except ByteArray UInt64 :=
  let product := left * right
  if right == (0 : UInt64) then
    Except.ok product
  else if product / right == left then
    Except.ok product
  else
    Except.error decodeError

def sumValues (values : Array UInt64) : Except ByteArray UInt64 :=
  values.foldl
    (fun state value =>
      match state with
      | Except.error err => Except.error err
      | Except.ok sum => checkedAdd sum value)
    (Except.ok 0)

def decodeRequest (value : Value) : Except ByteArray Request := do
  let fields <- requireObject value
  let _ <- requireOnlyFields fields requestFieldNames
  let rawValues <- requireUniqueField fields valuesFieldName
  let values <- decodeUInt64Array rawValues
  let multiplier <- requireUInt64Field value multiplierFieldName
  let includeCount <- requireBoolField value includeCountFieldName
  pure { values := values, multiplier := multiplier, includeCount := includeCount }

def resultValue (sum scaled : UInt64) (count : Nat) (included : Bool) : Value :=
  Value.obj #[
    Field.mk sumFieldName (Value.num sum),
    Field.mk scaledFieldName (Value.num scaled),
    Field.mk countFieldName (Value.num (if included then UInt64.ofNat count else 0)),
    Field.mk includedFieldName (Value.bool included)
  ]

def runRequest (request : Request) : Except ByteArray ByteArray := do
  let sum <- sumValues request.values
  let scaled <- checkedMul sum request.multiplier
  renderExcept (resultValue sum scaled request.values.size request.includeCount)

def transform (input : ByteArray) : Except ByteArray ByteArray := do
  let value <- parseBytesExcept input
  let request <- decodeRequest value
  runRequest request

end Examples.JsonTypedDecode
end LeanExe
