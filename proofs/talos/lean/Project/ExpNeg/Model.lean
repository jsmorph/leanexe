import Project.ExpSmall.Model

namespace Project.ExpNeg

def polynomial (x : UInt64) : UInt64 :=
  let p17 := Wasm.IEEE64.add (Wasm.IEEE64.mul 0x3CA6827863B97D97 x) 0x3CE952C77030AD4A
  let p16 := Wasm.IEEE64.add (Wasm.IEEE64.mul p17 x) 0x3D2AE7F3E733B81F
  let p15 := Wasm.IEEE64.add (Wasm.IEEE64.mul p16 x) 0x3D6AE7F3E733B81F
  let p14 := Wasm.IEEE64.add (Wasm.IEEE64.mul p15 x) 0x3DA93974A8C07C9D
  let p13 := Wasm.IEEE64.add (Wasm.IEEE64.mul p14 x) 0x3DE6124613A86D09
  let p12 := Wasm.IEEE64.add (Wasm.IEEE64.mul p13 x) 0x3E21EED8EFF8D898
  let p11 := Wasm.IEEE64.add (Wasm.IEEE64.mul p12 x) 0x3E5AE64567F544E4
  let p10 := Wasm.IEEE64.add (Wasm.IEEE64.mul p11 x) 0x3E927E4FB7789F5C
  let p9 := Wasm.IEEE64.add (Wasm.IEEE64.mul p10 x) 0x3EC71DE3A556C734
  let p8 := Wasm.IEEE64.add (Wasm.IEEE64.mul p9 x) 0x3EFA01A01A01A01A
  let p7 := Wasm.IEEE64.add (Wasm.IEEE64.mul p8 x) 0x3F2A01A01A01A01A
  let p6 := Wasm.IEEE64.add (Wasm.IEEE64.mul p7 x) 0x3F56C16C16C16C17
  let p5 := Wasm.IEEE64.add (Wasm.IEEE64.mul p6 x) 0x3F81111111111111
  let p4 := Wasm.IEEE64.add (Wasm.IEEE64.mul p5 x) 0x3FA5555555555555
  let p3 := Wasm.IEEE64.add (Wasm.IEEE64.mul p4 x) 0x3FC5555555555555
  let p2 := Wasm.IEEE64.add (Wasm.IEEE64.mul p3 x) 0x3FE0000000000000
  let p1 := Wasm.IEEE64.add (Wasm.IEEE64.mul p2 x) 0x3FF0000000000000
  Wasm.IEEE64.add (Wasm.IEEE64.mul p1 x) 0x3FF0000000000000

structure Reduction where
  word : UInt64
  squares : Nat
  deriving DecidableEq, Inhabited

def reduce : Nat → UInt64 → Nat → Reduction
  | 0, x, squares => ⟨x, squares⟩
  | steps+1, x, squares =>
    if x ≤ 0xBFF0000000000000 then ⟨x, squares⟩
    else
      let y := Wasm.IEEE64.mul x 0x3FE0000000000000
      reduce steps y (squares+1)

def square : Nat → UInt64 → UInt64
  | 0, x => x
  | steps+1, x => square steps (Wasm.IEEE64.mul x x)

def evaluate (x : UInt64) : UInt64 :=
  if 0xC050000000000000 < x then 0
  else
    let r := reduce 6 x 0
    square r.squares (polynomial r.word)

def inDomain (x : UInt64) : Bool :=
  x == 0 || (decide (0x8000000000000000 ≤ x) && decide (x < 0xFFF0000000000000))

def expNeg (x : UInt64) : ExpSmall.Result :=
  if inDomain x then ⟨0, evaluate x⟩ else ⟨1, 0⟩

end Project.ExpNeg
