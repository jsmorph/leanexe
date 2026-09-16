import Interpreter.Wasm.IEEE64

namespace Project.ExpSmall

def polynomial (x : UInt64) : UInt64 :=
  let a := Wasm.IEEE64.add (Wasm.IEEE64.mul 0x3F56C16C16C16C17 x) 0x3F81111111111111
  let b := Wasm.IEEE64.add (Wasm.IEEE64.mul a x) 0x3FA5555555555555
  let c := Wasm.IEEE64.add (Wasm.IEEE64.mul b x) 0x3FC5555555555555
  let d := Wasm.IEEE64.add (Wasm.IEEE64.mul c x) 0x3FE0000000000000
  let e := Wasm.IEEE64.add (Wasm.IEEE64.mul d x) 0x3FF0000000000000
  Wasm.IEEE64.add (Wasm.IEEE64.mul e x) 0x3FF0000000000000

def inDomain (x : UInt64) : Bool :=
  x == 0 || (decide (0x8000000000000000 ≤ x) && decide (x ≤ 0xBFF0000000000000))

structure Result where
  status : UInt64
  bits : UInt64
  deriving DecidableEq, Inhabited

def expSmall (x : UInt64) : Result :=
  if inDomain x then ⟨0, polynomial x⟩ else ⟨1, 0⟩

end Project.ExpSmall
