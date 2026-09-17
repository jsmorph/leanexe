import Project.ExpNeg.Model
import Project.Gelu.Model

namespace Project.GeluWide
open Project.ProofKit.F64Order

def evaluate (x : UInt64) : UInt64 :=
  let a := absBits x
  let z := negativeAbsBits (Gelu.argumentMagnitude a)
  let e := ExpNeg.evaluate z
  let d := Wasm.IEEE64.add 0x3FF0000000000000 e
  if x < 0x8000000000000000 then Wasm.IEEE64.div a d
  else Wasm.IEEE64.div (Wasm.IEEE64.mul (negativeAbsBits a) e) d

def inCore (x : UInt64) : Bool := decide (absBits x ≤ 0x4020000000000000)

def evaluateAll (x : UInt64) : UInt64 :=
  if inCore x then evaluate x
  else if x < 0x8000000000000000 then x else 0

def geluWide (x : UInt64) : ExpSmall.Result :=
  if finiteBits x then ⟨0, evaluateAll x⟩ else ⟨1, 0⟩

end Project.GeluWide
