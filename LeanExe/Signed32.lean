namespace LeanExe.Signed32

def extend8Bits (value : UInt32) : UInt32 :=
  let byte := value &&& 0xFF
  if byte < 0x80 then byte else byte ||| 0xFFFFFF00

def decode (value : UInt32) : Int :=
  if value.toNat < 2 ^ 31 then value.toNat else (value.toNat : Int) - 2 ^ 32

end LeanExe.Signed32
