import Library.Lists.Word.Program
import Verified.Reflect.Command

namespace Verified.Examples.ListTail

export Library.Lists.Word (sum reverse)

verified_compile compiled := [Library.Lists.Word.sum, Library.Lists.Word.reverse]

example : compiled.sum.func.modes = [.borrowed, .borrowed] := rfl
example : compiled.reverse.func.modes = [.owned, .owned] := rfl

#print axioms compiled.sum.implements
#print axioms compiled.sum.trapFree
#print axioms compiled.reverse.implements
#print axioms compiled.reverse.trapFree

end Verified.Examples.ListTail
