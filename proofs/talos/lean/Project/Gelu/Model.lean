import Project.ExpWide.Model
import Project.ProofKit.F64Absolute

namespace Project.Gelu
open Project.ProofKit.F64Order

def argumentMagnitude (a : UInt64) : UInt64 :=
  let square := Wasm.IEEE64.mul a a
  let cubicFactor := Wasm.IEEE64.add
    (Wasm.IEEE64.mul square 0x3FA6E4E26D4801F7) 0x3FF0000000000000
  Wasm.IEEE64.mul (Wasm.IEEE64.mul cubicFactor a) 0x3FF9884533D43651

def positivePart (a : UInt64) : UInt64 :=
  let z := negativeAbsBits (argumentMagnitude a)
  let e := ExpWide.evaluate z
  Wasm.IEEE64.div a (Wasm.IEEE64.add 0x3FF0000000000000 e)

def evaluate (x : UInt64) : UInt64 :=
  let a := absBits x
  let p := positivePart a
  if x < 0x8000000000000000 then p else Wasm.IEEE64.sub p a

def inDomain (x : UInt64) : Bool := decide (absBits x ≤ 0x4008000000000000)

def evaluateAll (x : UInt64) : UInt64 :=
  if inDomain x then evaluate x
  else if x < 0x8000000000000000 then x else 0

def gelu (x : UInt64) : ExpSmall.Result :=
  if inDomain x then ⟨0, evaluate x⟩ else ⟨1, 0⟩

end Project.Gelu
