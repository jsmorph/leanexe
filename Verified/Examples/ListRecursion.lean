import Library.Lists.Word.Program
import Verified.Reflect.Command

namespace Verified.Examples.ListRecursion

export Library.Lists.Word (increment)

def sum : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sum xs

verified_compile compiled := [sum, Library.Lists.Word.increment]

example : compiled.sum.func.modes = [.borrowed] := rfl
example : compiled.increment.func.modes = [.owned] := rfl

#print axioms compiled.sum.implements
#print axioms compiled.sum.trapFree
#print axioms compiled.increment.implements
#print axioms compiled.increment.trapFree

end Verified.Examples.ListRecursion
