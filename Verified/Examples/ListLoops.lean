import Library.Lists.Word.Program
import Verified.Reflect.Command

namespace Verified.Examples.ListLoops

export Library.Lists.Word (range)

def extend (n : UInt64) (xs : List UInt64) : List UInt64 :=
  LeanExe.loop n xs fun i ys => i :: ys

verified_compile compiled := [Library.Lists.Word.range, extend]

example : compiled.extend.func.modes = [.borrowed, .owned] := rfl

#print axioms compiled.range.implements
#print axioms compiled.range.trapFree
#print axioms compiled.extend.implements
#print axioms compiled.extend.trapFree

end Verified.Examples.ListLoops
