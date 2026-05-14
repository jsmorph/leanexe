import LeanExe.Ascii.Json

namespace LeanExe
namespace Examples.JsonDouble

def inputFieldName : ByteArray :=
  "n".toUTF8

def resultFieldName : ByteArray :=
  "result".toUTF8

def parseInput (text : AsciiString) : Option UInt64 :=
  Ascii.Json.getUInt64Field text inputFieldName

def resultJson (n : UInt64) : ByteArray :=
  Ascii.Json.object1UInt64 resultFieldName n

def doubleFits (n : UInt64) : Bool :=
  !(n > (9223372036854775807 : UInt64))

def transformAscii (text : AsciiString) : ByteArray :=
  match parseInput text with
  | some n =>
      if doubleFits n then
        resultJson (n * 2)
      else
        Ascii.Json.errorJson
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonDouble
end LeanExe
