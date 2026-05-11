import LeanExe.Ascii.Json
import LeanExe.Examples.Collatz

namespace LeanExe
namespace Examples.JsonCollatzLength

def fieldName : ByteArray :=
  "collatzLengthFor".toUTF8

def parseObject (text : AsciiString) : Option UInt64 :=
  Ascii.Json.getUInt64Field text fieldName

def resultJson (n : UInt64) : ByteArray :=
  Ascii.Json.object1UInt64 "length".toUTF8 n

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
