import LeanExe.Ascii.Json
import LeanExe.Examples.Collatz

namespace LeanExe
namespace Examples.JsonCollatzLength

def fieldName : ByteArray :=
  "collatzLengthFor".toUTF8

def parseInput (text : AsciiString) : Option UInt64 :=
  Ascii.Json.getUInt64Field text fieldName

def lengthInput? (text : AsciiString) : Option UInt64 :=
  do
    let n <- parseInput text
    Collatz.length? n

def resultJson (n : UInt64) : ByteArray :=
  Ascii.Json.object1UInt64 "length".toUTF8 n

def transformAscii (text : AsciiString) : ByteArray :=
  match lengthInput? text with
  | some len => resultJson len
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonCollatzLength
end LeanExe
