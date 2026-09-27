/-
  Pins every generated module's runtime functions to the shared definitions
  in `Defs.lean`.  Nominal type indices are local to each generated module, so
  the comparisons erase only that field.  A compiler change that diverges any
  parameter, local, instruction, or result breaks the corresponding `rfl`.
-/

import Project.Runtime.Defs
import Project.Gpt2RowMean.Program
import Project.Gpt2RowInvStd.Program
import Project.Gpt2AttentionScore.Program
import Project.Gpt2LinearRows.Program
import Project.Gpt2QuantizedLinearRows.Program
import Project.Gpt2QuantizedGroupedRows.Program
import Project.Gpt2QuantizedCached.Program
import Project.Gpt2CachedStep.Program
import Project.PackedRead.Program
import Project.PackedGenerate.Program
import Project.SequenceSoftmax.Program
import Project.TinyGpt2Seq.Program
import Project.TinyGpt2Checked.Program
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
import Project.EulerConservative.Program
import Project.Euler2DConservative.Program
import Project.Euler2DDynamicFlux.Program
import Project.Euler2DCellStep.Program
import Project.EulerDynamicFlux.Program
import Project.EulerCellStep.Program
import Project.EulerGridScan.Program
import Project.EulerGridStep.Program
import Project.EulerRusanov.Program
import Project.EulerRusanovStep.Program
import Project.EulerRiemann.Program
import Project.EulerOutwardSpeed.Program
import Project.EulerReconstruction.Program
import Project.EulerOutwardMaximum.Program
import Project.EulerOutwardCfl.Program
import Project.EulerOutwardGrid.Program
import Project.EulerOutwardFlux.Program
import Project.EulerOutwardFaceStep.Program
import Project.EulerReconstructed.Program
import Project.EulerCertificateFlux.Program
import Project.EulerCertificate.Program
import Project.ExpSmall.Program
import Project.ExpWide.Program
import Project.ExpNeg.Program
import Project.Softmax.Program
import Project.SoftmaxWide.Program
import Project.LayerNorm.Program
import Project.Gelu.Program
import Project.GeluWide.Program
import Project.TinyGpt2Hidden.Program
import Project.TinyGpt2Infer.Program
import Project.FoldSum.Program
import Project.F64Dot2CheckedBits.Program
import Project.F64Clip.Program
import Project.F64DotCheckedBits.Program
import Project.F64Horner2CheckedBits.Program
import Project.F64MulBits.Program
import Project.F64SubBits.Program
import Project.F64DivBits.Program
import Project.F64SqrtBits.Program
import Project.Gcd.Program
import Project.LebU32.Program
import Project.OrderBook.Program
import Project.PairFree.Program
import Project.PushSize.Program
import Project.PushTwice.Program
import Project.SharedPair.Program
import Project.Validate.Program

namespace Project.Runtime

example : eraseTypeIdx Project.Gpt2RowMean.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowMean.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowMean.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowMean.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.Gpt2RowInvStd.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowInvStd.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowInvStd.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2RowInvStd.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.Gpt2AttentionScore.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2AttentionScore.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2AttentionScore.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2AttentionScore.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.Gpt2LinearRows.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2LinearRows.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2LinearRows.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2LinearRows.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.Gpt2CachedStep.func39Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2CachedStep.func40Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2CachedStep.func41Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2CachedStep.func42Def = eraseTypeIdx (releaseFuncDef 42) := rfl

example : eraseTypeIdx Project.AppendBang.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.AppendBang.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.AssocList.func3Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func4Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func5Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.AssocList.func6Def = eraseTypeIdx (releaseFuncDef 6) := rfl

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

example : eraseTypeIdx Project.F64SubBits.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64SubBits.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64SubBits.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64SubBits.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64DivBits.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64DivBits.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64DivBits.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64DivBits.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64SqrtBits.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64SqrtBits.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64SqrtBits.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64SqrtBits.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.F64Dot2CheckedBits.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64Dot2CheckedBits.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.F64Clip.func7Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64Clip.func8Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64Clip.func9Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64Clip.func10Def = eraseTypeIdx (releaseFuncDef 10) := rfl

example : eraseTypeIdx Project.F64Horner2CheckedBits.func2Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func3Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func4Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.F64Horner2CheckedBits.func5Def = eraseTypeIdx (releaseFuncDef 5) := rfl

example : eraseTypeIdx Project.EulerRusanov.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanov.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.EulerRusanovStep.func7Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanovStep.func8Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanovStep.func9Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerRusanovStep.func10Def = eraseTypeIdx (releaseFuncDef 10) := rfl

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

example : eraseTypeIdx Project.EulerConservative.func6Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerConservative.func7Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerConservative.func8Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerConservative.func9Def = eraseTypeIdx (releaseFuncDef 9) := rfl

example : eraseTypeIdx Project.EulerDynamicFlux.func17Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerDynamicFlux.func18Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerDynamicFlux.func19Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerDynamicFlux.func20Def = eraseTypeIdx (releaseFuncDef 20) := rfl

example : eraseTypeIdx Project.EulerCellStep.func26Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerCellStep.func27Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerCellStep.func28Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerCellStep.func29Def = eraseTypeIdx (releaseFuncDef 29) := rfl

example : eraseTypeIdx Project.EulerGridScan.func12Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerGridScan.func13Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerGridScan.func14Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerGridScan.func15Def = eraseTypeIdx (releaseFuncDef 15) := rfl

example : eraseTypeIdx Project.EulerGridStep.func37Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerGridStep.func38Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerGridStep.func39Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerGridStep.func40Def = eraseTypeIdx (releaseFuncDef 40) := rfl


example : eraseTypeIdx Project.Euler2DConservative.func14Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Euler2DConservative.func15Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Euler2DConservative.func16Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Euler2DConservative.func17Def = eraseTypeIdx (releaseFuncDef 17) := rfl

example : eraseTypeIdx Project.Euler2DDynamicFlux.func26Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Euler2DDynamicFlux.func27Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Euler2DDynamicFlux.func28Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Euler2DDynamicFlux.func29Def = eraseTypeIdx (releaseFuncDef 29) := rfl

example : eraseTypeIdx Project.Euler2DCellStep.func36Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Euler2DCellStep.func37Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Euler2DCellStep.func38Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Euler2DCellStep.func39Def = eraseTypeIdx (releaseFuncDef 39) := rfl

example : eraseTypeIdx Project.EulerRiemann.func104Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerRiemann.func105Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerRiemann.func106Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerRiemann.func107Def = eraseTypeIdx (releaseFuncDef 107) := rfl

example : eraseTypeIdx Project.EulerOutwardSpeed.func37Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardSpeed.func38Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardSpeed.func39Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardSpeed.func40Def = eraseTypeIdx (releaseFuncDef 40) := rfl

example : eraseTypeIdx Project.EulerReconstruction.func41Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstruction.func42Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstruction.func43Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstruction.func44Def = eraseTypeIdx (releaseFuncDef 44) := rfl

example : eraseTypeIdx Project.EulerOutwardMaximum.func43Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardMaximum.func44Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardMaximum.func45Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardMaximum.func46Def = eraseTypeIdx (releaseFuncDef 46) := rfl

example : eraseTypeIdx Project.EulerOutwardCfl.func16Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardCfl.func17Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardCfl.func18Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardCfl.func19Def = eraseTypeIdx (releaseFuncDef 19) := rfl

example : eraseTypeIdx Project.EulerOutwardGrid.func46Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardGrid.func47Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardGrid.func48Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardGrid.func49Def = eraseTypeIdx (releaseFuncDef 49) := rfl

example : eraseTypeIdx Project.EulerOutwardFlux.func55Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFlux.func56Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFlux.func57Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFlux.func58Def = eraseTypeIdx (releaseFuncDef 58) := rfl

example : eraseTypeIdx Project.EulerOutwardFaceStep.func71Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFaceStep.func72Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFaceStep.func73Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerOutwardFaceStep.func74Def = eraseTypeIdx (releaseFuncDef 74) := rfl

example : eraseTypeIdx Project.EulerReconstructed.func149Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstructed.func150Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstructed.func151Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerReconstructed.func152Def = eraseTypeIdx (releaseFuncDef 152) := rfl

example : eraseTypeIdx Project.EulerCertificateFlux.func36Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificateFlux.func37Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificateFlux.func38Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificateFlux.func39Def = eraseTypeIdx (releaseFuncDef 39) := rfl

example : eraseTypeIdx Project.EulerCertificate.func191Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificate.func192Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificate.func193Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.EulerCertificate.func194Def = eraseTypeIdx (releaseFuncDef 194) := rfl

example : eraseTypeIdx Project.ExpSmall.func3Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ExpSmall.func4Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ExpSmall.func5Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ExpSmall.func6Def = eraseTypeIdx (releaseFuncDef 6) := rfl

example : eraseTypeIdx Project.ExpWide.func4Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ExpWide.func5Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ExpWide.func6Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ExpWide.func7Def = eraseTypeIdx (releaseFuncDef 7) := rfl

example : eraseTypeIdx Project.ExpNeg.func8Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.ExpNeg.func9Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.ExpNeg.func10Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.ExpNeg.func11Def = eraseTypeIdx (releaseFuncDef 11) := rfl

example : eraseTypeIdx Project.Softmax.func12Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Softmax.func13Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Softmax.func14Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Softmax.func15Def = eraseTypeIdx (releaseFuncDef 15) := rfl

example : eraseTypeIdx Project.SoftmaxWide.func13Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.SoftmaxWide.func14Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.SoftmaxWide.func15Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.SoftmaxWide.func16Def = eraseTypeIdx (releaseFuncDef 16) := rfl

example : eraseTypeIdx Project.LayerNorm.func7Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.LayerNorm.func8Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.LayerNorm.func9Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.LayerNorm.func10Def = eraseTypeIdx (releaseFuncDef 10) := rfl

example : eraseTypeIdx Project.Gelu.func9Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gelu.func10Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gelu.func11Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gelu.func12Def = eraseTypeIdx (releaseFuncDef 12) := rfl

example : eraseTypeIdx Project.GeluWide.func14Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.GeluWide.func15Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.GeluWide.func16Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.GeluWide.func17Def = eraseTypeIdx (releaseFuncDef 17) := rfl

example : eraseTypeIdx Project.TinyGpt2Hidden.func75Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Hidden.func76Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Hidden.func77Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Hidden.func78Def = eraseTypeIdx (releaseFuncDef 78) := rfl

example : eraseTypeIdx Project.TinyGpt2Infer.func79Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Infer.func80Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Infer.func81Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Infer.func82Def = eraseTypeIdx (releaseFuncDef 82) := rfl

example : eraseTypeIdx Project.TinyGpt2Checked.func86Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Checked.func87Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Checked.func88Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Checked.func89Def = eraseTypeIdx (releaseFuncDef 89) := rfl

example : eraseTypeIdx Project.SequenceSoftmax.func12Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.SequenceSoftmax.func13Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.SequenceSoftmax.func14Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.SequenceSoftmax.func15Def = eraseTypeIdx (releaseFuncDef 15) := rfl

example : eraseTypeIdx Project.TinyGpt2Seq.func79Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Seq.func80Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Seq.func81Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.TinyGpt2Seq.func82Def = eraseTypeIdx (releaseFuncDef 82) := rfl

example : eraseTypeIdx Project.PackedRead.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.PackedRead.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.PackedRead.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.PackedRead.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.PackedGenerate.func1Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.PackedGenerate.func2Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.PackedGenerate.func3Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.PackedGenerate.func4Def = eraseTypeIdx (releaseFuncDef 4) := rfl

example : eraseTypeIdx Project.Gpt2QuantizedLinearRows.func9Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedLinearRows.func10Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedLinearRows.func11Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedLinearRows.func12Def = eraseTypeIdx (releaseFuncDef 12) := rfl

example : eraseTypeIdx Project.Gpt2QuantizedGroupedRows.func9Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedGroupedRows.func10Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedGroupedRows.func11Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedGroupedRows.func12Def = eraseTypeIdx (releaseFuncDef 12) := rfl

example : eraseTypeIdx Project.Gpt2QuantizedCached.func62Def = eraseTypeIdx allocFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedCached.func63Def = eraseTypeIdx resetFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedCached.func64Def = eraseTypeIdx retainFuncDef := rfl
example : eraseTypeIdx Project.Gpt2QuantizedCached.func65Def = eraseTypeIdx (releaseFuncDef 65) := rfl

end Project.Runtime
