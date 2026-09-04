/-
  Pins every generated module's runtime functions to the shared definitions
  in `Defs.lean`.  Nominal type indices are local to each generated module, so
  the comparisons erase only that field.  A compiler change that diverges any
  parameter, local, instruction, or result breaks the corresponding `rfl`.
-/

import Project.Runtime.Defs
import Project.AppendBang.Program
import Project.AssocList.Program
import Project.BoxFree.Program
import Project.ClobCancel.Program
import Project.ClobDepth.Program
import Project.ClobFindBest.Program
import Project.ClobLimit.Program
import Project.ClobMarket.Program
import Project.ClobMatchFuel.Program
import Project.ClobPostOnly.Program
import Project.ClobQuote.Program
import Project.EulerRusanov.Program
import Project.FoldSum.Program
import Project.F64Dot2CheckedBits.Program
import Project.F64DotCheckedBits.Program
import Project.F64Horner2CheckedBits.Program
import Project.F64MulBits.Program
import Project.Gcd.Program
import Project.LebU32.Program
import Project.OrderBook.Program
import Project.PairFree.Program
import Project.PushSize.Program
import Project.PushTwice.Program
import Project.SharedPair.Program
import Project.Validate.Program

namespace Project.Runtime

example : eraseTypeIdx Project.AppendBang.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.AssocList.func4Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func5Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func6Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func7Def = eraseTypeIdx (releaseFuncDef 7) := rfl

example : eraseTypeIdx Project.BoxFree.func3Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.BoxFree.func4Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.BoxFree.func5Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.BoxFree.func6Def = eraseTypeIdx (releaseFuncDef 6) := rfl

example : eraseTypeIdx Project.FoldSum.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.FoldSum.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.FoldSum.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.FoldSum.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64MulBits.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64MulBits.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64MulBits.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64MulBits.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64Dot2CheckedBits.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.F64Horner2CheckedBits.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.EulerRusanov.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64DotCheckedBits.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64DotCheckedBits.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64DotCheckedBits.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64DotCheckedBits.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.Gcd.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gcd.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gcd.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gcd.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.LebU32.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.LebU32.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.LebU32.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.LebU32.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.OrderBook.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.OrderBook.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.OrderBook.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.OrderBook.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.PairFree.func4Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.PairFree.func5Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.PairFree.func6Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.PairFree.func7Def = eraseTypeIdx (releaseFuncDef 7) := rfl

example : eraseTypeIdx Project.PushSize.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.PushSize.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.PushSize.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.PushSize.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.PushTwice.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.PushTwice.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.PushTwice.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.PushTwice.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.SharedPair.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.SharedPair.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.SharedPair.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.SharedPair.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.Validate.func4Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Validate.func5Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Validate.func6Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Validate.func7Def = eraseTypeIdx (releaseFuncDef 7) := rfl

example : eraseTypeIdx Project.ClobCancel.func4Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobCancel.func5Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobCancel.func6Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobCancel.func7Def = eraseTypeIdx (releaseFuncDef 7) := rfl

example : eraseTypeIdx Project.ClobDepth.func8Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobDepth.func9Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobDepth.func10Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobDepth.func11Def = eraseTypeIdx (releaseFuncDef 11) := rfl

example : eraseTypeIdx Project.ClobQuote.func11Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobQuote.func12Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobQuote.func13Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobQuote.func14Def = eraseTypeIdx (releaseFuncDef 14) := rfl

example : eraseTypeIdx Project.ClobFindBest.func9Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobFindBest.func10Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobFindBest.func11Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobFindBest.func12Def = eraseTypeIdx (releaseFuncDef 12) := rfl

example : eraseTypeIdx Project.ClobLimit.func22Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobLimit.func23Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobLimit.func24Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobLimit.func25Def = eraseTypeIdx (releaseFuncDef 25) := rfl

example : eraseTypeIdx Project.ClobMarket.func22Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobMarket.func23Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobMarket.func24Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobMarket.func25Def = eraseTypeIdx (releaseFuncDef 25) := rfl

example : eraseTypeIdx Project.ClobMatchFuel.func15Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobMatchFuel.func16Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobMatchFuel.func17Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobMatchFuel.func18Def = eraseTypeIdx (releaseFuncDef 18) := rfl

example : eraseTypeIdx Project.ClobPostOnly.func18Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ClobPostOnly.func19Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ClobPostOnly.func20Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ClobPostOnly.func21Def = eraseTypeIdx (releaseFuncDef 21) := rfl

end Project.Runtime
