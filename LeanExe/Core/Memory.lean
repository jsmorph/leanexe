import Init.Control.State
import Init.Data.ByteArray.Lemmas
import LeanExe.Core.Program

namespace LeanExe.Core.Memory

def zeroBytes (count : Nat) : ByteArray := ⟨Array.replicate count 0⟩

def extend (bytes : ByteArray) (count : Nat) : ByteArray := bytes ++ zeroBytes count

/-- The page delta has UInt32 semantics. Growth appends zero bytes; failure
returns 4294967295 and leaves the array unchanged. -/
def nativeGrow (bytes : ByteArray) (delta : UInt64) (cap : Nat) : UInt64 × ByteArray :=
  let pages := bytes.size / 65536
  if pages + delta.toUInt32.toNat ≤ cap then
    (UInt64.ofNat pages, extend bytes (delta.toUInt32.toNat * 65536))
  else (4294967295, bytes)

def read (address : UInt64) : StateM ByteArray UInt64 := fun bytes =>
  (if address.toNat < bytes.size then bytes[address.toNat]!.toUInt64 else 0, bytes)

def write (address value : UInt64) : StateM ByteArray UInt64 := fun bytes =>
  (0, if address.toNat < bytes.size then bytes.set! address.toNat value.toUInt8 else bytes)

def size : StateM ByteArray UInt64 := fun bytes => (UInt64.ofNat bytes.size, bytes)

/-- Grow by a UInt32 number of 64 KiB pages, up to the 4 GiB memory limit. -/
def grow (delta : UInt64) : StateM ByteArray UInt64 := fun bytes => nativeGrow bytes delta 65536

/-- Effects are equalities to the ordinary native state computations. -/
inductive effects : Nat → List UInt64 → ByteArray → UInt64 → ByteArray → Prop where
  | read {address initial value final}
      (computed : Memory.read address initial = (value, final)) :
      effects 0 [address] initial value final
  | write {address byte initial value final}
      (computed : Memory.write address byte initial = (value, final)) :
      effects 1 [address, byte] initial value final
  | size {initial value final}
      (computed : Memory.size initial = (value, final)) :
      effects 2 [] initial value final
  | grow {delta initial value final}
      (computed : Memory.grow delta initial = (value, final)) :
      effects 3 [delta] initial value final

def effectArity : Nat → Option Nat
  | 0 => some 1
  | 1 => some 2
  | 2 => some 0
  | 3 => some 1
  | _ => none

end LeanExe.Core.Memory
