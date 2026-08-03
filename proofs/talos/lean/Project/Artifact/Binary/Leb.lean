import Project.Artifact.Binary.Cursor

namespace Wasm.Binary.Leb

open Parser

namespace Internal

def unsignedLoop (width shift fuel value : Nat) : Parser Nat := do
  match fuel with
  | 0 => fail (.integerTooLong width)
  | fuel' + 1 =>
      let byte ← readByte
      let payload := byte.toNat % 128
      let value' := value + payload * 2 ^ shift
      if fuel' = 0 && ¬payload < 2 ^ (width - shift) then
        fail (.integerOverflow width)
      else if byte.toNat < 128 then
        pure value'
      else if fuel' = 0 then
        fail (.integerTooLong width)
      else
        unsignedLoop width (shift + 7) fuel' value'

def signedTerminalFits (width shift payload : Nat) : Bool :=
  if shift + 7 ≤ width then
    true
  else
    let used := width - shift
    payload < 2 ^ (used - 1) || 128 - 2 ^ (used - 1) ≤ payload

def signedValue (shift payload value : Nat) : Int :=
  let value' := value + payload * 2 ^ shift
  if payload < 64 then
    Int.ofNat value'
  else
    Int.ofNat value' - Int.ofNat (2 ^ (shift + 7))

def signedLoop (width shift fuel value : Nat) : Parser Int := do
  match fuel with
  | 0 => fail (.integerTooLong width)
  | fuel' + 1 =>
      let byte ← readByte
      let payload := byte.toNat % 128
      if fuel' = 0 && ¬signedTerminalFits width shift payload then
        fail (.integerOverflow width)
      else if byte.toNat < 128 then
        pure (signedValue shift payload value)
      else if fuel' = 0 then
        fail (.integerTooLong width)
      else
        signedLoop width (shift + 7) fuel'
          (value + payload * 2 ^ shift)

end Internal

def u32 : Parser UInt32 := do
  pure (UInt32.ofNat (← Internal.unsignedLoop 32 0 5 0))

def u64 : Parser UInt64 := do
  pure (UInt64.ofNat (← Internal.unsignedLoop 64 0 10 0))

def s32 : Parser Int :=
  Internal.signedLoop 32 0 5 0

def s64 : Parser Int :=
  Internal.signedLoop 64 0 10 0

end Wasm.Binary.Leb
