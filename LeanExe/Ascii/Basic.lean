import LeanExe.AsciiString

namespace LeanExe
namespace Ascii

def byteLBrace : UInt8 := 123
def byteRBrace : UInt8 := 125
def byteLBracket : UInt8 := 91
def byteRBracket : UInt8 := 93
def byteQuote : UInt8 := 34
def byteBackslash : UInt8 := 92
def byteColon : UInt8 := 58
def byteComma : UInt8 := 44
def byteDigitZero : UInt8 := 48
def byteA : UInt8 := 97
def byteB : UInt8 := 98
def byteF : UInt8 := 102
def byteN : UInt8 := 110
def byteT : UInt8 := 116

def isWs (byte : UInt8) : Bool :=
  byte == (32 : UInt8) ||
    byte == (9 : UInt8) ||
    byte == (10 : UInt8) ||
    byte == (13 : UInt8)

def skipWsFuel : Nat -> AsciiString -> Nat -> Nat
  | 0, _text, pos => pos
  | fuel + 1, text, pos =>
      if isWs (text.getD pos 0) then
        skipWsFuel fuel text (pos + 1)
      else
        pos

def skipWs (text : AsciiString) (pos : Nat) : Nat :=
  skipWsFuel (text.size + 1) text pos

def expectByte (text : AsciiString) (pos : Nat) (byte : UInt8) : Option Nat :=
  if pos < text.size && text.get! pos == byte then
    some (pos + 1)
  else
    none

def expectWsByte (text : AsciiString) (pos : Nat) (byte : UInt8) : Option Nat :=
  expectByte text (skipWs text pos) byte

end Ascii
end LeanExe
