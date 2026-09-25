import Lean
open Lean

namespace ArithmeticMilestone

def constant : UInt64 := 18446744073709551615
def wrapping (x y : UInt64) : UInt64 := (x + 17) * (y - 3)
def quotient (x y : UInt64) : UInt64 := x / y
def remainder (x y : UInt64) : UInt64 := x % y
def shifts (x y : UInt64) : UInt64 := (x <<< y) ^^^ (x >>> y)
def nested (x y : UInt64) : UInt64 :=
  (((x + 7) * (y - 3)) / (x % (y + 1))) +
    (((x &&& y) ||| (x ^^^ y)) <<< ((x >>> y) + 64))
def order (x y : UInt64) : UInt64 := x - y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

def cases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [("wrapping", wrapping), ("quotient", quotient), ("remainder", remainder),
   ("shifts", shifts), ("nested", nested), ("order", order)]

end ArithmeticMilestone

def main : IO Unit := do
  IO.println (Json.compress (Json.mkObj [
    ("name", toJson "constant"), ("args", Json.arr #[]),
    ("expected", toJson (toString ArithmeticMilestone.constant))]))
  for (name, source) in ArithmeticMilestone.cases do
    for (x, y) in ArithmeticMilestone.inputs do
      IO.println (Json.compress (Json.mkObj [
        ("name", toJson name), ("args", toJson [toString x, toString y]),
        ("expected", toJson (toString (source x y)))]))
