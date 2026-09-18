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

private def linear (row col : Nat) := row * 3 + col
private def twice (arithmetic : ScalarArithmetic) (word : UInt32) :=
  arithmetic.mul word 0x40000000

@[wgsl] def helper : Kernel := fun arithmetic a b row col =>
  let i := linear row col
  let doubled := twice arithmetic (a i)
  arithmetic.add doubled (b i)

@[wgsl] def transpose : Kernel := fun arithmetic a b row col =>
  arithmetic.add (a (col * 2 + row)) (b (row * 3 + col))

@[wgsl] def nested : Kernel := fun arithmetic a b row col =>
  Source.fold 2 0x3f800000 fun k acc =>
    let inner := Source.fold 3 0 fun j subtotal =>
      arithmetic.add subtotal (arithmetic.mul (a (row * 6 + k * 3 + j)) (b (j * 3 + col)))
    arithmetic.add acc inner

@[wgsl] def zeroFold : Kernel := fun arithmetic a b _ _ =>
  Source.fold 0 0x3f000000 fun _ acc => arithmetic.add acc (arithmetic.mul (a 0) (b 0))

@[wgsl] def matmul768 : Kernel := fun arithmetic a b row col =>
  Source.fold 768 0 fun k acc =>
    arithmetic.add acc (arithmetic.mul (a (row * 768 + k)) (b (k * 3 + col)))

/-- Exercise unused input bindings and the largest finite binary32 literal. -/
@[wgsl] def constant : Kernel := fun _ _ _ _ _ => 0x7f7fffff

@[wgsl] def onlyA : Kernel := fun _ a _ row col => a (row * 3 + col)

/-- Executable corpus membership shared by the compiler and IEEE32 runner. -/
def cases : List (String × Kernel × Shape) := [
  ("add", add, ⟨2, 3, 6, 6⟩),
  ("multiply", multiply, ⟨2, 3, 6, 6⟩),
  ("matmul", matmul, ⟨2, 3, 8, 12⟩),
  ("sumProducts", sumProducts, ⟨2, 3, 8, 12⟩),
  ("helper", helper, ⟨2, 3, 6, 6⟩),
  ("transpose", transpose, ⟨2, 3, 6, 6⟩),
  ("nested", nested, ⟨2, 3, 12, 9⟩),
  ("zeroFold", zeroFold, ⟨2, 3, 1, 1⟩),
  ("matmul768", matmul768, ⟨1, 3, 768, 2304⟩),
  ("constant", constant, ⟨2, 3, 1, 1⟩),
  ("onlyA", onlyA, ⟨2, 3, 6, 1⟩)]

end LeanExe.WGSL.Examples.Body
