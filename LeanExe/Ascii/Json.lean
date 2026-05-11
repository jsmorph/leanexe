import LeanExe.Ascii.Decimal

namespace LeanExe
namespace Ascii
namespace Json

def expectFieldName1 (text : AsciiString) (pos : Nat) (name : UInt8) : Option Nat :=
  match expectWsByte text pos byteQuote with
  | none => none
  | some pos1 =>
      match expectByte text pos1 name with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteQuote with
          | none => none
          | some pos3 => expectWsByte text pos3 byteColon

def errorJson : ByteArray :=
  ((((((((((ByteArray.empty.push byteLBrace).push byteQuote).push (101 : UInt8)).push
    (114 : UInt8)).push (114 : UInt8)).push (111 : UInt8)).push (114 : UInt8)).push
    byteQuote).push byteColon).push (49 : UInt8)).push byteRBrace

end Json
end Ascii
end LeanExe
