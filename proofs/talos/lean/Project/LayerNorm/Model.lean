import Interpreter.Wasm.IEEE64

namespace Project.LayerNorm

def bounded (x : UInt64) : Bool :=
  decide (x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x4010000000000000)

def rowBounded (a b c d : UInt64) : Bool := bounded a && bounded b && bounded c && bounded d

def average (a b c d : UInt64) : UInt64 :=
  Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.add a b) (Wasm.IEEE64.add c d))
    0x4010000000000000

def denominator (a b c d : UInt64) : UInt64 :=
  let variance := average (Wasm.IEEE64.mul a a) (Wasm.IEEE64.mul b b)
    (Wasm.IEEE64.mul c c) (Wasm.IEEE64.mul d d)
  Wasm.IEEE64.sqrt (Wasm.IEEE64.add variance 0x3EE4F8B588E368F1)

def affine (x denominator gamma beta : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.div x denominator) gamma) beta

structure Result where
  status : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64
  deriving DecidableEq, Inhabited

def compute (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) : Result :=
  let m := average x0 x1 x2 x3
  let c0 := Wasm.IEEE64.sub x0 m
  let c1 := Wasm.IEEE64.sub x1 m
  let c2 := Wasm.IEEE64.sub x2 m
  let c3 := Wasm.IEEE64.sub x3 m
  let d := denominator c0 c1 c2 c3
  ⟨0, affine c0 d g0 b0, affine c1 d g1 b1, affine c2 d g2 b2, affine c3 d g3 b3⟩

def layerNorm (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) : Result :=
  if rowBounded x0 x1 x2 x3 && rowBounded g0 g1 g2 g3 && rowBounded b0 b1 b2 b3 then
    compute x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3
  else ⟨1, 0, 0, 0, 0⟩

end Project.LayerNorm
