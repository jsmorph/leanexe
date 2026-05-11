import LeanExe.Ascii.Json

namespace LeanExe
namespace Examples.JsonAdd

def parseObject (text : AsciiString) : Option UInt64 :=
  match Ascii.expectWsByte text 0 Ascii.byteLBrace with
  | none => none
  | some pos1 =>
      match Ascii.Json.expectFieldName1 text pos1 Ascii.byteA with
      | none => none
      | some aValuePos =>
          match Ascii.parseUInt64 text (Ascii.skipWs text aValuePos) with
          | none => none
          | some parsedA =>
              match Ascii.expectWsByte text parsedA.pos Ascii.byteComma with
              | none => none
              | some pos2 =>
                  match Ascii.Json.expectFieldName1 text pos2 Ascii.byteB with
                  | none => none
                  | some bValuePos =>
                      match Ascii.parseUInt64 text (Ascii.skipWs text bValuePos) with
                      | none => none
                      | some parsedB =>
                          match Ascii.expectWsByte text parsedB.pos Ascii.byteRBrace with
                          | none => none
                          | some endPos =>
                              if Ascii.skipWs text endPos == text.size then
                                let sum := parsedA.value + parsedB.value
                                if sum < parsedA.value then
                                  none
                                else
                                  some sum
                              else
                                none

def sumPrefix : ByteArray :=
  "{\"sum\":".toUTF8

def resultJson (n : UInt64) : ByteArray :=
  (Ascii.appendUInt64Decimal sumPrefix n).push Ascii.byteRBrace

def transformAscii (text : AsciiString) : ByteArray :=
  match parseObject text with
  | some sum => resultJson sum
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonAdd
end LeanExe
