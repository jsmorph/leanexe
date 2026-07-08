/-
  Pins every generated module's runtime functions to the shared definitions
  in `Defs.lean`.  A compiler change that diverges the runtime suite in any
  module breaks the corresponding `rfl` here.
-/

import Project.Runtime.Defs
import Project.AppendBang.Program
import Project.AssocList.Program
import Project.BoxFree.Program
import Project.Gcd.Program
import Project.OrderBook.Program
import Project.PairFree.Program
import Project.PushSize.Program
import Project.PushTwice.Program
import Project.SharedPair.Program
import Project.Validate.Program

namespace Project.Runtime

example : Project.AppendBang.func1Def = allocFuncDef := rfl
example : Project.AppendBang.func2Def = resetFuncDef := rfl
example : Project.AppendBang.func3Def = retainFuncDef := rfl
example : Project.AppendBang.func4Def = releaseFuncDef 4 := rfl

example : Project.AssocList.func4Def = allocFuncDef := rfl
example : Project.AssocList.func5Def = resetFuncDef := rfl
example : Project.AssocList.func6Def = retainFuncDef := rfl
example : Project.AssocList.func7Def = releaseFuncDef 7 := rfl

example : Project.BoxFree.func3Def = allocFuncDef := rfl
example : Project.BoxFree.func4Def = resetFuncDef := rfl
example : Project.BoxFree.func5Def = retainFuncDef := rfl
example : Project.BoxFree.func6Def = releaseFuncDef 6 := rfl

example : Project.Gcd.func1Def = allocFuncDef := rfl
example : Project.Gcd.func2Def = resetFuncDef := rfl
example : Project.Gcd.func3Def = retainFuncDef := rfl
example : Project.Gcd.func4Def = releaseFuncDef 4 := rfl

example : Project.OrderBook.func2Def = allocFuncDef := rfl
example : Project.OrderBook.func3Def = resetFuncDef := rfl
example : Project.OrderBook.func4Def = retainFuncDef := rfl
example : Project.OrderBook.func5Def = releaseFuncDef 5 := rfl

example : Project.PairFree.func4Def = allocFuncDef := rfl
example : Project.PairFree.func5Def = resetFuncDef := rfl
example : Project.PairFree.func6Def = retainFuncDef := rfl
example : Project.PairFree.func7Def = releaseFuncDef 7 := rfl

example : Project.PushSize.func1Def = allocFuncDef := rfl
example : Project.PushSize.func2Def = resetFuncDef := rfl
example : Project.PushSize.func3Def = retainFuncDef := rfl
example : Project.PushSize.func4Def = releaseFuncDef 4 := rfl

example : Project.PushTwice.func2Def = allocFuncDef := rfl
example : Project.PushTwice.func3Def = resetFuncDef := rfl
example : Project.PushTwice.func4Def = retainFuncDef := rfl
example : Project.PushTwice.func5Def = releaseFuncDef 5 := rfl

example : Project.SharedPair.func1Def = allocFuncDef := rfl
example : Project.SharedPair.func2Def = resetFuncDef := rfl
example : Project.SharedPair.func3Def = retainFuncDef := rfl
example : Project.SharedPair.func4Def = releaseFuncDef 4 := rfl

example : Project.Validate.func4Def = allocFuncDef := rfl
example : Project.Validate.func5Def = resetFuncDef := rfl
example : Project.Validate.func6Def = retainFuncDef := rfl
example : Project.Validate.func7Def = releaseFuncDef 7 := rfl

end Project.Runtime
