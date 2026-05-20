import LeanExe.Ascii.Json.Decode

namespace LeanExe
namespace Examples.JsonObjectArrayDecode

open Ascii.Json

structure Item where
  id : UInt64
  weight : UInt64

structure Request where
  items : Array Item
  scale : UInt64

def itemsFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "items".toUTF8

def idFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "id".toUTF8

def weightFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "weight".toUTF8

def scaleFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "scale".toUTF8

def weightedFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "weighted".toUTF8

def countFieldName : AsciiString :=
  AsciiString.ofTrustedByteArray "count".toUTF8

def itemFieldNames : Array AsciiString :=
  #[idFieldName, weightFieldName]

def requestFieldNames : Array AsciiString :=
  #[itemsFieldName, scaleFieldName]

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

def decodeItem (value : Value) : Except ByteArray Item := do
  let fields <- requireObject value
  let _ <- requireOnlyFields fields itemFieldNames
  let rawId <- requireUniqueField fields idFieldName
  let id <- requireUInt64 rawId
  let rawWeight <- requireUniqueField fields weightFieldName
  let weight <- requireUInt64 rawWeight
  pure { id := id, weight := weight }

def decodeRequest (value : Value) : Except ByteArray Request := do
  let fields <- requireObject value
  let _ <- requireOnlyFields fields requestFieldNames
  let rawItems <- requireUniqueField fields itemsFieldName
  let items <- decodeArray (fun item => decodeItem item) rawItems
  let rawScale <- requireUniqueField fields scaleFieldName
  let scale <- requireUInt64 rawScale
  pure { items := items, scale := scale }

def itemContribution (item : Item) : Except ByteArray UInt64 := do
  checkedMul item.id item.weight

def weightedSum (items : Array Item) : Except ByteArray UInt64 :=
  items.foldl
    (fun state item =>
      match state with
      | Except.error err => Except.error err
      | Except.ok sum =>
          match itemContribution item with
          | Except.error err => Except.error err
          | Except.ok contribution => checkedAdd sum contribution)
    (Except.ok 0)

def resultValue (weighted : UInt64) (count : Nat) : Value :=
  Value.obj #[
    Field.mk weightedFieldName (Value.num weighted),
    Field.mk countFieldName (Value.num (UInt64.ofNat count))
  ]

def runRequest (request : Request) : Except ByteArray ByteArray := do
  let base <- weightedSum request.items
  let scaled <- checkedMul base request.scale
  renderExcept (resultValue scaled request.items.size)

def transform (input : ByteArray) : Except ByteArray ByteArray := do
  let value <- parseBytesExcept input
  let request <- decodeRequest value
  runRequest request

end Examples.JsonObjectArrayDecode
end LeanExe
