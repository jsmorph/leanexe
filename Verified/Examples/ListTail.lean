import Verified.Reflect.Command

namespace Verified.Examples.ListTail

def sum (xs : List UInt64) (acc : UInt64) : UInt64 :=
  match xs with
  | [] => acc
  | x :: tail => sum tail (acc + x)

def reverse (xs acc : List UInt64) : List UInt64 :=
  match xs with
  | [] => acc
  | x :: tail => reverse tail (x :: acc)

verified_compile compiled := [sum, reverse]

example : compiled.sum.func.modes = [.borrowed, .borrowed] := rfl
example : compiled.reverse.func.modes = [.owned, .owned] := rfl

#print axioms compiled.sum.implements
#print axioms compiled.sum.trapFree
#print axioms compiled.reverse.implements
#print axioms compiled.reverse.trapFree

end Verified.Examples.ListTail
