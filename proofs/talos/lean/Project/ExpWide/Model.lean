import Project.ExpSmall.Model

namespace Project.ExpWide

def evaluate (x : UInt64) : UInt64 :=
  let y := Wasm.IEEE64.div x 0x4020000000000000
  let a := ExpSmall.polynomial y
  let b := Wasm.IEEE64.mul a a
  let c := Wasm.IEEE64.mul b b
  Wasm.IEEE64.mul c c

def inDomain (x : UInt64) : Bool :=
  x == 0 || (decide (0x8000000000000000 ≤ x) && decide (x ≤ 0xC020000000000000))

def expWide (x : UInt64) : ExpSmall.Result :=
  if inDomain x then ⟨0, evaluate x⟩ else ⟨1, 0⟩

end Project.ExpWide
