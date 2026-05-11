import LeanExe.Ascii.Json
import LeanExe.Examples.Collatz

namespace LeanExe
namespace Examples.JsonCollatzLength

def fieldName : ByteArray :=
  let b0 := ByteArray.empty.push (99 : UInt8)
  let b1 := b0.push (111 : UInt8)
  let b2 := b1.push (108 : UInt8)
  let b3 := b2.push (108 : UInt8)
  let b4 := b3.push (97 : UInt8)
  let b5 := b4.push (116 : UInt8)
  let b6 := b5.push (122 : UInt8)
  let b7 := b6.push (76 : UInt8)
  let b8 := b7.push (101 : UInt8)
  let b9 := b8.push (110 : UInt8)
  let b10 := b9.push (103 : UInt8)
  let b11 := b10.push (116 : UInt8)
  let b12 := b11.push (104 : UInt8)
  let b13 := b12.push (70 : UInt8)
  let b14 := b13.push (111 : UInt8)
  b14.push (114 : UInt8)

def parseObject (text : AsciiString) : Option UInt64 :=
  match Ascii.expectWsByte text 0 Ascii.byteLBrace with
  | none => none
  | some pos1 =>
      match Ascii.Json.expectFieldName text pos1 fieldName with
      | none => none
      | some valuePos =>
          match Ascii.parseUInt64 text (Ascii.skipWs text valuePos) with
          | none => none
          | some parsed =>
              match Ascii.expectWsByte text parsed.pos Ascii.byteRBrace with
              | none => none
              | some endPos =>
                  if Ascii.skipWs text endPos == text.size then
                    some parsed.value
                  else
                    none

def lengthPrefix : ByteArray :=
  (((((((((ByteArray.empty.push Ascii.byteLBrace).push Ascii.byteQuote).push (108 : UInt8)).push
    (101 : UInt8)).push (110 : UInt8)).push (103 : UInt8)).push (116 : UInt8)).push
    (104 : UInt8)).push Ascii.byteQuote).push Ascii.byteColon

def resultJson (n : UInt64) : ByteArray :=
  (Ascii.appendUInt64Decimal lengthPrefix n).push Ascii.byteRBrace

def transformAscii (text : AsciiString) : ByteArray :=
  match parseObject text with
  | some n =>
      match Collatz.length? n with
      | some len => resultJson len
      | none => Ascii.Json.errorJson
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonCollatzLength
end LeanExe
