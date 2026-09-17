import Project.Softmax.Model
import Project.ExpNeg.Model

namespace Project.SoftmaxWide
open Project.Softmax

def weight (n i x m : UInt64) : UInt64 :=
  if i < n then ExpNeg.evaluate (Wasm.IEEE64.sub x m) else 0

def compute (n a b c d : UInt64) : Result :=
  let m := rowMaximum n a b c d
  let w0 := weight n 0 a m
  let w1 := weight n 1 b m
  let w2 := weight n 2 c m
  let w3 := weight n 3 d m
  let s := total w0 w1 w2 w3
  ⟨0, probability n 0 w0 s, probability n 1 w1 s,
    probability n 2 w2 s, probability n 3 w3 s⟩

end Project.SoftmaxWide
