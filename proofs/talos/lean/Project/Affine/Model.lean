import Interpreter.Wasm.IEEE64

namespace Project.Affine

def dot2 (x0 x1 w0 w1 : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul x0 w0) (Wasm.IEEE64.mul x1 w1)

def dot4 (x0 x1 x2 x3 w0 w1 w2 w3 : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dot2 x0 x1 w0 w1) (dot2 x2 x3 w2 w3)

def dot8 (x0 x1 x2 x3 x4 x5 x6 x7 w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dot4 x0 x1 x2 x3 w0 w1 w2 w3) (dot4 x4 x5 x6 x7 w4 w5 w6 w7)

def affine4 (x0 x1 x2 x3 w0 w1 w2 w3 bias : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dot4 x0 x1 x2 x3 w0 w1 w2 w3) bias

def affine8 (x0 x1 x2 x3 x4 x5 x6 x7 w0 w1 w2 w3 w4 w5 w6 w7 bias : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dot8 x0 x1 x2 x3 x4 x5 x6 x7 w0 w1 w2 w3 w4 w5 w6 w7) bias

end Project.Affine
