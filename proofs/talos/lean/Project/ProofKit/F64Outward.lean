import Project.ProofKit.F64Adjacent

namespace Project.ProofKit.F64Outward
open Project.ProofKit.F64Order
open Project.ProofKit.F64Adjacent

structure Checked where
  status : UInt64
  value : UInt64
  deriving DecidableEq, Inhabited, Repr

def rejected : Checked := ⟨1, 0⟩

def neighbor (up : Bool) (bits : UInt64) : UInt64 :=
  if up then nextUp bits else nextDown bits

def endpoint (up : Bool) (rounded : UInt64) : Checked :=
  if finiteBits rounded then
    let bits := neighbor up rounded
    if finiteBits bits then ⟨0, bits⟩ else rejected
  else rejected

def add (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.add a b)
  else rejected

def sub (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.sub a b)
  else rejected

def mul (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.mul a b)
  else rejected

def div (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b && decide (0 < absBits b) then
    endpoint up (Wasm.IEEE64.div a b)
  else rejected

def sqrt (up : Bool) (a : UInt64) : Checked :=
  if finiteBits a && decide (a ≤ 0x8000000000000000) then
    endpoint up (Wasm.IEEE64.sqrt a)
  else rejected

end Project.ProofKit.F64Outward
