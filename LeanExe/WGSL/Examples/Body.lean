import LeanExe.WGSL.Compile

namespace LeanExe.WGSL.Examples.Body
open Source

@[wgsl] def add : Kernel := fun arithmetic a b row col =>
  arithmetic.add (a (row * 3 + col)) (b (row * 3 + col))

@[wgsl] def multiply : Kernel := fun arithmetic a b row col =>
  arithmetic.mul (a (row * 3 + col)) (b (row * 3 + col))

@[wgsl] def matmul : Kernel := fun arithmetic a b row col =>
  Source.fold 4 0 fun k acc =>
    let product := arithmetic.mul (a (row * 4 + k)) (b (k * 3 + col))
    arithmetic.add acc product

@[wgsl] def sumProducts : Kernel := fun arithmetic a b row col =>
  Source.fold 4 0 fun k acc =>
    let product := arithmetic.add (a (row * 4 + k)) (b (k * 3 + col))
    arithmetic.add acc product

end LeanExe.WGSL.Examples.Body
