import LeanExe.Float32
import Project.ProofKit.F32RangeCheck

namespace Project.ProofKit.F32DotRangeCertificate

def checkedPrefix (x w : Nat → UInt32) (mulBound addBound : Nat) : Nat → UInt32 × Bool
  | 0 => (0, true)
  | count + 1 =>
    let previous := checkedPrefix x w mulBound addBound count
    let product := LeanExe.Float32.mulBits (x count) (w count)
    (LeanExe.Float32.addBits previous.1 product, previous.2 &&
      F32RangeCertificate.multiplication (x count) (w count) mulBound &&
      F32RangeCertificate.addition previous.1 product addBound)

structure Profile where
  value : UInt32
  multiplication : Nat
  addition : Nat

def profile (x w : Nat → UInt32) (count : Nat) : Profile := Id.run do
  let mut total : UInt32 := 0
  let mut mulBound := 173
  let mut addBound := 1
  for i in [:count] do
    let product := LeanExe.Float32.mulBits (x i) (w i)
    mulBound := max mulBound ((Wasm.IEEE32.scaledMagnitude (x i) * Wasm.IEEE32.scaledMagnitude (w i)).log2 + 1)
    addBound := max addBound ((Wasm.IEEE32.scaledValue total + Wasm.IEEE32.scaledValue product).natAbs.log2 + 1)
    total := LeanExe.Float32.addBits total product
  return ⟨total, mulBound, addBound⟩

end Project.ProofKit.F32DotRangeCertificate
