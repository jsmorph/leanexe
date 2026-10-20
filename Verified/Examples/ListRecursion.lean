import Verified.Reflect.Command

namespace Verified.Examples.ListRecursion

def sum : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sum xs

def increment : List UInt64 → List UInt64
  | [] => []
  | x :: xs => (x + 1) :: increment xs

verified_compile compiled := [sum, increment]

example : compiled.sum.func.modes = [.borrowed] := rfl
example : compiled.increment.func.modes = [.owned] := rfl

#print axioms compiled.sum.implements
#print axioms compiled.sum.trapFree
#print axioms compiled.increment.implements
#print axioms compiled.increment.trapFree

end Verified.Examples.ListRecursion
