import Verified.Reflect.Command

namespace Verified.Examples.ListLoops

def range (n : UInt64) : List UInt64 :=
  LeanExe.loop n [] fun i xs => (n - 1 - i) :: xs

def extend (n : UInt64) (xs : List UInt64) : List UInt64 :=
  LeanExe.loop n xs fun i ys => i :: ys

verified_compile compiled := [range, extend]

example : compiled.extend.func.modes = [.borrowed, .owned] := rfl

#print axioms compiled.range.implements
#print axioms compiled.range.trapFree
#print axioms compiled.extend.implements
#print axioms compiled.extend.trapFree

end Verified.Examples.ListLoops
